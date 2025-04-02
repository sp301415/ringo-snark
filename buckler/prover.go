package buckler

import (
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

func (w *walker) walkForProve(prover *Prover, v reflect.Value, pw []PublicWitness, sw []Witness) {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness{}):
		pw[w.publicWitnessCount] = v.Interface().(PublicWitness)
		w.publicWitnessCount++
	case reflect.TypeOf(Witness{}):
		sw[w.witnessCount] = v.Interface().(Witness)
		w.witnessCount++
	}

	switch v.Kind() {
	case reflect.Ptr, reflect.Interface:
		w.walkForProve(prover, v.Elem(), pw, sw)
	case reflect.Invalid:
		panic("invalid type")
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			w.walkForProve(prover, v.Field(i), pw, sw)
		}
	case reflect.Slice, reflect.Array:
		for i := 0; i < v.Len(); i++ {
			w.walkForProve(prover, v.Index(i), pw, sw)
		}
	}
}

// Prover proves the given circuit.
type Prover struct {
	Parameters celpc.Parameters

	ringQ *bigring.BigRing

	encoder    *Encoder
	polyProver *celpc.Prover

	oracle *celpc.RandomOracle

	ctx *Context
}

type proverBuffer struct {
	publicWitnesses []PublicWitness
	witnesses       []Witness

	publicWitnessEncodings []bigring.BigNTTPoly
	witnessEncodings       []bigring.BigNTTPoly

	commitments []celpc.Commitment
	openings    []celpc.Opening
}

func newProver(params celpc.Parameters, ctx *Context) *Prover {
	logEmbedDegree := int(math.Ceil(math.Log2(float64(ctx.maxDegree))))
	embedDegree := 1 << logEmbedDegree

	return &Prover{
		Parameters: params,

		ringQ: bigring.NewBigRing(embedDegree, params.Modulus()),

		encoder:    NewEncoder(params, embedDegree),
		polyProver: celpc.NewProver(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,
	}
}

func (p *Prover) newBuffer() proverBuffer {
	return proverBuffer{
		publicWitnesses:        make([]PublicWitness, p.ctx.publicWitnessCount),
		witnesses:              make([]Witness, p.ctx.witnessCount),
		publicWitnessEncodings: make([]bigring.BigNTTPoly, p.ctx.publicWitnessCount),
		witnessEncodings:       make([]bigring.BigNTTPoly, p.ctx.witnessCount),
		commitments:            make([]celpc.Commitment, p.ctx.witnessCount),
		openings:               make([]celpc.Opening, p.ctx.witnessCount),
	}
}

// Prove proves the circuit in given assignment.
func (p *Prover) Prove(ck celpc.AjtaiCommitKey, c Circuit) Proof {
	p.oracle.Reset()
	p.polyProver.Commiter = celpc.NewAjtaiCommiter(p.Parameters, ck)
	buf := p.newBuffer()

	walker := &walker{}
	walker.walkForProve(p, reflect.ValueOf(c), buf.publicWitnesses, buf.witnesses)

	for i := 0; i < len(buf.publicWitnesses); i++ {
		pwEcd := p.encoder.Encode(buf.publicWitnesses[i])
		buf.publicWitnessEncodings[i] = p.ringQ.ToNTTPoly(pwEcd)
	}

	for wID, wDcmpIDs := range p.ctx.decomposedWitness {
		w := buf.witnesses[wID]
		logBound := len(wDcmpIDs) - 1

		wDcmp := make([]Witness, logBound+1)
		for i := 0; i < logBound+1; i++ {
			wDcmp[i] = make(Witness, p.Parameters.Degree())
		}

		for i := 0; i < p.Parameters.Degree(); i++ {
			coeffDcmp := bigSignedDecompose(w[i], p.Parameters.Modulus(), logBound)
			for j := 0; j < logBound+1; j++ {
				wDcmp[j][i] = coeffDcmp[j]
			}
		}

		for i, wDcmpID := range wDcmpIDs {
			buf.witnesses[wDcmpID[0].Int64()] = wDcmp[i]
		}
	}

	for i := 0; i < len(buf.witnesses); i++ {
		wEcd := p.encoder.RandomEncode(buf.witnesses[i])
		wEcdNTT := p.ringQ.ToNTTPoly(wEcd)
		buf.witnessEncodings[i] = wEcdNTT

		wCommit := bigring.BigPoly{Coeffs: wEcd.Coeffs[:2*p.Parameters.Degree()]}
		buf.commitments[i], buf.openings[i] = p.polyProver.Commit(wCommit)
	}
	openingProof := p.polyProver.ProveOpening(buf.commitments, buf.openings)

	for i := 0; i < len(buf.commitments); i++ {
		p.oracle.WriteCommitment(buf.commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)
	p.oracle.Finalize()

	batchArithConsts := make(map[int]*big.Int)
	for _, constraint := range p.ctx.constraints {
		if _, ok := batchArithConsts[constraint.degree]; !ok {
			batchArithConsts[constraint.degree] = big.NewInt(0)
			p.oracle.SampleModAssign(batchArithConsts[constraint.degree])
		}
	}

	rowCheckCommit, rowCheckOpenings := p.rowCheckFirstMove(batchArithConsts, buf)

	p.oracle.WriteCommitment(rowCheckCommit.QuoCommitment)
	p.oracle.WriteCommitment(rowCheckCommit.QuoShiftCommitment)
	p.oracle.WriteOpeningProof(rowCheckCommit.OpeningProof)
	p.oracle.Finalize()

	evaluatePoint := big.NewInt(0)
	p.oracle.SampleModAssign(evaluatePoint)

	evalProofs := make([]celpc.EvaluationProof, len(buf.commitments))
	for i := 0; i < len(buf.commitments); i++ {
		evalProofs[i] = p.polyProver.Evaluate(evaluatePoint, buf.openings[i])
	}
	rowCheckEvalProof := RowCheckEvalProof{
		QuoEvalProof:      p.polyProver.Evaluate(evaluatePoint, rowCheckOpenings.QuoOpening),
		QuoShiftEvalProof: p.polyProver.Evaluate(evaluatePoint, rowCheckOpenings.QuoShiftOpening),
	}

	return Proof{
		PublicWitness: buf.publicWitnesses,
		Witness:       buf.commitments,
		OpeningProof:  openingProof,

		RowCheckCommit: rowCheckCommit,

		EvalProofs:        evalProofs,
		RowCheckEvalProof: rowCheckEvalProof,
	}
}

func (p *Prover) rowCheckFirstMove(batchConsts map[int]*big.Int, buf proverBuffer) (RowCheckCommit, rowCheckOpening) {
	batchConstsPow := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPow[k] = big.NewInt(0).Set(v)
	}

	batchedNTT := p.ringQ.NewNTTPoly()
	for _, constraint := range p.ctx.constraints {
		constraintEvalNTT := p.ringQ.NewNTTPoly()
		termNTT := p.ringQ.NewNTTPoly()
		for i := 0; i < len(constraint.witness); i++ {
			for j := 0; j < p.ringQ.N(); j++ {
				termNTT.Coeffs[j].SetInt64(constraint.coeffsInt64[i])
			}

			if constraint.coeffsBig[i] != nil {
				for j := 0; j < p.ringQ.N(); j++ {
					termNTT.Coeffs[j].Mul(termNTT.Coeffs[j], constraint.coeffsBig[i])
					termNTT.Coeffs[j].Mod(termNTT.Coeffs[j], p.Parameters.Modulus())
				}
			}

			if constraint.coeffsPublicWitness[i] != -1 {
				pwEcdNTT := buf.publicWitnessEncodings[constraint.coeffsPublicWitness[i]]
				p.ringQ.MulNTTAssign(termNTT, pwEcdNTT, termNTT)
			}

			for j := 0; j < len(constraint.witness[i]); j++ {
				witnessEcdNTT := buf.witnessEncodings[constraint.witness[i][j]]
				p.ringQ.MulNTTAssign(termNTT, witnessEcdNTT, termNTT)
			}
			p.ringQ.AddNTTAssign(constraintEvalNTT, termNTT, constraintEvalNTT)
		}
		p.ringQ.ScalarMulAddNTTAssign(constraintEvalNTT, batchConstsPow[constraint.degree], batchedNTT)

		batchConstsPow[constraint.degree].Mul(batchConstsPow[constraint.degree], batchConsts[constraint.degree])
		batchConstsPow[constraint.degree].Mod(batchConstsPow[constraint.degree], p.Parameters.Modulus())
	}
	batched := p.ringQ.ToPoly(batchedNTT)

	quo, _ := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()

	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
	quoShift := p.ringQ.NewPoly()
	for i, ii := 0, quoCommitDeg-quoDeg; i < quoCommitDeg; i, ii = i+1, ii+1 {
		quoShift.Coeffs[ii].Set(quo.Coeffs[i])
	}

	var com RowCheckCommit
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.QuoShiftCommitment, open.QuoShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quoShift.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.QuoShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.QuoShiftOpening},
	)

	return com, open
}
