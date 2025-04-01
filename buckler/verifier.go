package buckler

import (
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

// Verify verifies the proof of the relation.
func Verify(params celpc.Parameters, ck celpc.AjtaiCommitKey, c Circuit[VerifierWitness], pf Proof) bool {
	ctx := newVerifierContext(params, pf)
	c.Define(ctx)

	maxDegree := 2 * params.Degree()
	for i := 0; i < len(ctx.aritmeticCircuits); i++ {
		circuit := ctx.aritmeticCircuits[i].(*arithmeticCircuitVerify)
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
	verifier := celpc.NewVerifier(params, ck)
	ringQ := bigring.NewBigRing(embedDegree, params.Modulus())
	oracle := celpc.NewRandomOracle(params)
	hash := celpc.NewRandomOracle(params)

	encodes := make(map[**big.Int]bigring.BigPoly, 0)
	commitments := make([]celpc.Commitment, 0)

	for i := 0; i < reflect.TypeOf(c).Elem().NumField(); i++ {
		witnessValue := reflect.ValueOf(c).Elem().Field(i).Interface()
		switch witnessValue := witnessValue.(type) {
		case PublicWitness:
			wEcd := ecd.Encode(witnessValue)
			encodes[&witnessValue[:1][0]] = wEcd
		case celpc.Commitment:
			commitments = append(commitments, witnessValue)

			wHash := hashCommitment(witnessValue, hash)
			if wDcmp, ok := pf.DecomposedWitness[wHash]; ok {
				commitments = append(commitments, wDcmp...)
			}
		}
	}

	if !verifier.VerifyOpeningProof(commitments, pf.OpeningProof) {
		return false
	}
	if !verifier.VerifyOpeningProof([]celpc.Commitment{pf.RowCheckCommit.QuoCommitment, pf.RowCheckCommit.QuoShiftCommitment}, pf.RowCheckCommit.OpeningProof) {
		return false
	}

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

	oracle.WriteCommitment(pf.RowCheckCommit.QuoCommitment)
	oracle.WriteCommitment(pf.RowCheckCommit.QuoShiftCommitment)
	oracle.WriteOpeningProof(pf.RowCheckCommit.OpeningProof)
	oracle.Finalize()

	evaluatePoint := big.NewInt(0)
	oracle.SampleModAssign(evaluatePoint)

	vanishPoint := big.NewInt(0).Exp(evaluatePoint, big.NewInt(int64(params.Degree())), params.Modulus())
	vanishPoint.Sub(vanishPoint, big.NewInt(1))

	for i := 0; i < len(commitments); i++ {
		commitmentHash := hashCommitment(commitments[i], hash)
		if !verifier.VerifyEvaluation(evaluatePoint, commitments[i], pf.Evaluations[commitmentHash]) {
			return false
		}
	}
	if !verifier.VerifyEvaluation(evaluatePoint, pf.RowCheckCommit.QuoCommitment, pf.RowCheckEval.QuoEval) {
		return false
	}
	if !verifier.VerifyEvaluation(evaluatePoint, pf.RowCheckCommit.QuoShiftCommitment, pf.RowCheckEval.QuoShiftEval) {
		return false
	}
	rowCheckQuoDeg := maxDegree - params.Degree()
	rowCheckQuoCommitDeg := int(math.Ceil(float64(rowCheckQuoDeg)/float64(params.BigIntCommitSize()))) * params.BigIntCommitSize()
	rowCheckShiftEval := big.NewInt(0).Exp(evaluatePoint, big.NewInt(int64(rowCheckQuoCommitDeg-rowCheckQuoDeg)), params.Modulus())
	rowCheckShiftEval.Mul(rowCheckShiftEval, pf.RowCheckEval.QuoEval.Value)
	rowCheckShiftEval.Mod(rowCheckShiftEval, params.Modulus())

	if rowCheckShiftEval.Cmp(pf.RowCheckEval.QuoShiftEval.Value) != 0 {
		return false
	}

	batchedEval := big.NewInt(0)
	for t, circuit := range ctx.aritmeticCircuits {
		circuit := circuit.(*arithmeticCircuitVerify)

		for i := 0; i < len(circuit.monomials); i++ {
			var term *big.Int
			if circuit.coeffPublicWitness[i] == nil {
				term = big.NewInt(0).SetInt64(circuit.coeffInt64[i])
				term.Mul(term, circuit.coeffBigInt[i])
				term.Mod(term, params.Modulus())
			} else {
				term = ringQ.Evaluate(encodes[&circuit.coeffPublicWitness[i][:1][0]], evaluatePoint)
				term.Mul(term, big.NewInt(0).SetInt64(circuit.coeffInt64[i]))
				term.Mul(term, circuit.coeffBigInt[i])
				term.Mod(term, params.Modulus())
			}

			for j := 0; j < len(circuit.monomials[i]); j++ {
				monomialHash := hashCommitment(circuit.monomials[i][j], hash)
				monomialEval := pf.Evaluations[monomialHash].Value
				term.Mul(term, monomialEval)
				term.Mod(term, params.Modulus())
			}
			term.Mul(term, batchConsts[t])
			batchedEval.Add(batchedEval, term)
			batchedEval.Mod(batchedEval, params.Modulus())
		}
	}

	rowCheckEval := big.NewInt(0).Set(pf.RowCheckEval.QuoEval.Value)
	rowCheckEval.Mul(rowCheckEval, vanishPoint)
	rowCheckEval.Mod(rowCheckEval, params.Modulus())

	if rowCheckEval.Cmp(batchedEval) != 0 {
		return false
	}

	return true
}
