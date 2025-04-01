package buckler

import (
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

// Prove proves the relation.
func Prove(params celpc.Parameters, ck celpc.AjtaiCommitKey, c Circuit[ProverWitness]) Proof {
	pf := Proof{
		Witness:           make(map[string]celpc.Commitment, 0),
		DecomposedWitness: make(map[uint64][]celpc.Commitment, 0),
		Evaluations:       make(map[uint64]celpc.EvaluationProof, 0),
	}

	ctx := newProverContext(params)
	c.Define(ctx)

	maxDegree := 2 * params.Degree()
	for i := 0; i < len(ctx.aritmeticCircuits); i++ {
		circuit := ctx.aritmeticCircuits[i].(*arithmeticCircuitProve)
		for j := 0; j < len(circuit.monomials); j++ {
			degree := 0
			if circuit.coeffPublicWitness[j] != nil {
				degree += params.Degree() - 1
			}
			degree += len(circuit.monomials[j])*(2*params.Degree()-1) + 1

			if degree > maxDegree {
				maxDegree = degree
			}
		}
	}

	logEmbedDegree := int(math.Ceil(math.Log2(float64(maxDegree))))
	embedDegree := 1 << logEmbedDegree

	ecd := NewEncoder(params, embedDegree)
	prover := celpc.NewProver(params, ck)
	ringQ := bigring.NewBigRing(embedDegree, params.Modulus())
	oracle := celpc.NewRandomOracle(params)
	hash := celpc.NewRandomOracle(params)

	encodes := make(map[**big.Int]bigring.BigNTTPoly, 0)
	commitments := make([]celpc.Commitment, 0)
	openings := make([]celpc.Opening, 0)

	for i := 0; i < reflect.TypeOf(c).Elem().NumField(); i++ {
		witnessName := reflect.TypeOf(c).Elem().Field(i).Name
		witnessValue := reflect.ValueOf(c).Elem().Field(i).Interface()
		switch witness := witnessValue.(type) {
		case PublicWitness:
			wEcd := ecd.Encode(witness)
			wEcdNTT := ringQ.ToNTTPoly(wEcd)
			encodes[&witness[:1][0]] = wEcdNTT
		case []*big.Int:
			wEcd := ecd.RandomEncode(witness)
			wEcdNTT := ringQ.ToNTTPoly(wEcd)
			encodes[&witness[:1][0]] = wEcdNTT

			wCommit, wOpen := prover.Commit(bigring.BigPoly{Coeffs: wEcd.Coeffs[:2*params.Degree()]})
			commitments = append(commitments, wCommit)
			openings = append(openings, wOpen)

			pf.Witness[witnessName] = wCommit

			if wDcmp, ok := ctx.decomposedWitness[&witness[:1][0]]; ok {
				wHash := hashCommitment(wCommit, hash)
				for j := range wDcmp {
					wDcmpEcd := ecd.RandomEncode(wDcmp[j])
					wDcmpEcdNTT := ringQ.ToNTTPoly(wDcmpEcd)
					encodes[&wDcmp[j][:1][0]] = wDcmpEcdNTT

					dcmpCommit, dcmpOpen := prover.Commit(bigring.BigPoly{Coeffs: wDcmpEcd.Coeffs[:2*params.Degree()]})
					commitments = append(commitments, dcmpCommit)
					openings = append(openings, dcmpOpen)

					pf.DecomposedWitness[wHash] = append(pf.DecomposedWitness[wHash], dcmpCommit)
				}
			}
		}
	}
	pf.OpeningProof = prover.ProveOpening(commitments, openings)

	for i := 0; i < len(commitments); i++ {
		oracle.WriteCommitment(commitments[i])
	}
	oracle.WriteOpeningProof(pf.OpeningProof)
	oracle.Finalize()

	batchConsts := make([]*big.Int, len(ctx.aritmeticCircuits))
	for i := 0; i < len(ctx.aritmeticCircuits); i++ {
		batchConsts[i] = big.NewInt(0)
		oracle.SampleModAssign(batchConsts[i])
	}

	batchedNTT := ringQ.NewNTTPoly()
	for t, circuit := range ctx.aritmeticCircuits {
		circuit := circuit.(*arithmeticCircuitProve)

		for i := 0; i < len(circuit.monomials); i++ {
			var term bigring.BigNTTPoly
			if circuit.coeffPublicWitness[i] == nil {
				term = ringQ.NewNTTPoly()
				for j := 0; j < ringQ.N(); j++ {
					term.Coeffs[j].SetInt64(circuit.coeffInt64[i])
					term.Coeffs[j].Mul(term.Coeffs[j], circuit.coeffBigInt[i])
					term.Coeffs[j].Mod(term.Coeffs[j], params.Modulus())
				}
			} else {
				term = encodes[&circuit.coeffPublicWitness[i][:1][0]]
				ringQ.ScalarMulNTTAssign(term, big.NewInt(0).SetInt64(circuit.coeffInt64[i]), term)
				ringQ.ScalarMulNTTAssign(term, circuit.coeffBigInt[i], term)
			}

			for j := 0; j < len(circuit.monomials[i]); j++ {
				monomial := encodes[&circuit.monomials[i][j][:1][0]]
				ringQ.MulNTTAssign(term, monomial, term)
			}
			ringQ.ScalarMulAddNTTAssign(term, batchConsts[t], batchedNTT)
		}
	}
	batched := ringQ.ToPoly(batchedNTT)

	rowCheckQuo, _ := ringQ.QuoRemByVanishing(batched, params.Degree())
	rowCheckQuoDeg := maxDegree - params.Degree()

	rowCheckQuoCommitDeg := int(math.Ceil(float64(rowCheckQuoDeg)/float64(params.BigIntCommitSize()))) * params.BigIntCommitSize()
	rowCheckQuoShift := ringQ.NewPoly()
	for i, ii := 0, rowCheckQuoCommitDeg-rowCheckQuoDeg; i < rowCheckQuoCommitDeg; i, ii = i+1, ii+1 {
		rowCheckQuoShift.Coeffs[ii].Set(rowCheckQuo.Coeffs[i])
	}

	var rowCheckQuoOpening, rowCheckQuoShiftOpening celpc.Opening
	pf.RowCheckCommit.QuoCommitment, rowCheckQuoOpening = prover.Commit(bigring.BigPoly{Coeffs: rowCheckQuo.Coeffs[:rowCheckQuoCommitDeg]})
	pf.RowCheckCommit.QuoShiftCommitment, rowCheckQuoShiftOpening = prover.Commit(bigring.BigPoly{Coeffs: rowCheckQuoShift.Coeffs[:rowCheckQuoCommitDeg]})
	pf.RowCheckCommit.OpeningProof = prover.ProveOpening(
		[]celpc.Commitment{pf.RowCheckCommit.QuoCommitment, pf.RowCheckCommit.QuoShiftCommitment},
		[]celpc.Opening{rowCheckQuoOpening, rowCheckQuoShiftOpening},
	)

	oracle.WriteCommitment(pf.RowCheckCommit.QuoCommitment)
	oracle.WriteCommitment(pf.RowCheckCommit.QuoShiftCommitment)
	oracle.WriteOpeningProof(pf.RowCheckCommit.OpeningProof)
	oracle.Finalize()

	evaluatePoint := big.NewInt(0)
	oracle.SampleModAssign(evaluatePoint)

	for i := 0; i < len(commitments); i++ {
		commitmentHash := hashCommitment(commitments[i], hash)
		pf.Evaluations[commitmentHash] = prover.Evaluate(evaluatePoint, openings[i])
	}
	pf.RowCheckEval.QuoEval = prover.Evaluate(evaluatePoint, rowCheckQuoOpening)
	pf.RowCheckEval.QuoShiftEval = prover.Evaluate(evaluatePoint, rowCheckQuoShiftOpening)

	return pf
}
