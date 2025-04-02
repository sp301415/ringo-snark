package buckler

import (
	"math"
	"math/big"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

// Verifier verifies the given circuit.
type Verifier struct {
	Parameters celpc.Parameters

	ringQ *bigring.BigRing

	encoder      *Encoder
	polyVerifier *celpc.Verifier

	oracle *celpc.RandomOracle

	ctx *Context
}

type verifierBuffer struct {
	evaluationPoint    *big.Int
	vanishPoint        *big.Int
	publicWitnessEvals []*big.Int
}

func newVerifier(params celpc.Parameters, ctx *Context) *Verifier {
	logEmbedDegree := int(math.Ceil(math.Log2(float64(ctx.maxDegree))))
	embedDegree := 1 << logEmbedDegree

	return &Verifier{
		Parameters: params,

		ringQ: bigring.NewBigRing(embedDegree, params.Modulus()),

		encoder:      NewEncoder(params, embedDegree),
		polyVerifier: celpc.NewVerifier(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,
	}
}

func (v *Verifier) newBuffer() verifierBuffer {
	return verifierBuffer{
		evaluationPoint:    big.NewInt(0),
		vanishPoint:        big.NewInt(0),
		publicWitnessEvals: make([]*big.Int, v.ctx.publicWitnessCount),
	}
}

// Verify verifies the circuit with the given proof.
func (v *Verifier) Verify(ck celpc.AjtaiCommitKey, pf Proof) bool {
	v.oracle.Reset()
	v.polyVerifier.Commiter = celpc.NewAjtaiCommiter(v.Parameters, ck)
	buf := v.newBuffer()

	for i := 0; i < len(pf.Witness); i++ {
		v.oracle.WriteCommitment(pf.Witness[i])
	}
	v.oracle.WriteOpeningProof(pf.OpeningProof)
	v.oracle.Finalize()

	batchArithConsts := make(map[int]*big.Int, len(v.ctx.constraints))
	for _, constraint := range v.ctx.constraints {
		if _, ok := batchArithConsts[constraint.degree]; !ok {
			batchArithConsts[constraint.degree] = big.NewInt(0)
			v.oracle.SampleModAssign(batchArithConsts[constraint.degree])
		}
	}

	v.oracle.WriteCommitment(pf.RowCheckCommit.QuoCommitment)
	v.oracle.WriteCommitment(pf.RowCheckCommit.QuoShiftCommitment)
	v.oracle.WriteOpeningProof(pf.RowCheckCommit.OpeningProof)
	v.oracle.Finalize()

	v.oracle.SampleModAssign(buf.evaluationPoint)
	buf.vanishPoint.Exp(buf.evaluationPoint, big.NewInt(int64(v.Parameters.Degree())), v.Parameters.Modulus())
	buf.vanishPoint.Sub(buf.vanishPoint, big.NewInt(1))

	for i := 0; i < len(pf.PublicWitness); i++ {
		pwEcd := v.encoder.Encode(pf.PublicWitness[i])
		buf.publicWitnessEvals[i] = v.ringQ.Evaluate(pwEcd, buf.evaluationPoint)
	}

	if !v.polyVerifier.VerifyOpeningProof(pf.Witness, pf.OpeningProof) {
		return false
	}
	for i := 0; i < len(pf.EvalProofs); i++ {
		if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, pf.Witness[i], pf.EvalProofs[i]) {
			return false
		}
	}

	if !v.rowCheck(batchArithConsts, buf, pf) {
		return false
	}

	return true
}

func (v *Verifier) rowCheck(batchConsts map[int]*big.Int, buf verifierBuffer, pf Proof) bool {
	batchConstsPow := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPow[k] = big.NewInt(0).Set(v)
	}

	commits := []celpc.Commitment{pf.RowCheckCommit.QuoCommitment, pf.RowCheckCommit.QuoShiftCommitment}
	evalPfs := []celpc.EvaluationProof{pf.RowCheckEvalProof.QuoEvalProof, pf.RowCheckEvalProof.QuoShiftEvalProof}
	if !v.polyVerifier.VerifyOpeningProof(commits, pf.RowCheckCommit.OpeningProof) {
		return false
	}
	for i := range evalPfs {
		if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, commits[i], evalPfs[i]) {
			return false
		}
	}

	quoDeg := v.ctx.maxDegree - v.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(v.Parameters.BigIntCommitSize()))) * v.Parameters.BigIntCommitSize()

	quoShiftEval := big.NewInt(0).Exp(buf.evaluationPoint, big.NewInt(int64(quoCommitDeg-quoDeg)), v.Parameters.Modulus())
	quoShiftEval.Mul(quoShiftEval, pf.QuoEvalProof.Value)
	quoShiftEval.Mod(quoShiftEval, v.Parameters.Modulus())
	if quoShiftEval.Cmp(pf.QuoShiftEvalProof.Value) != 0 {
		return false
	}

	batchedEval := big.NewInt(0)
	for _, constraint := range v.ctx.constraints {
		constraintEval := big.NewInt(0)
		termEval := big.NewInt(0)
		for i := 0; i < len(constraint.witness); i++ {
			termEval.SetInt64(constraint.coeffsInt64[i])

			if constraint.coeffsBig[i] != nil {
				termEval.Mul(termEval, constraint.coeffsBig[i])
				termEval.Mod(termEval, v.Parameters.Modulus())
			}

			if constraint.coeffsPublicWitness[i] != -1 {
				termEval.Mul(termEval, buf.publicWitnessEvals[constraint.coeffsPublicWitness[i]])
				termEval.Mod(termEval, v.Parameters.Modulus())
			}

			for j := 0; j < len(constraint.witness[i]); j++ {
				termEval.Mul(termEval, pf.EvalProofs[constraint.witness[i][j]].Value)
				termEval.Mod(termEval, v.Parameters.Modulus())
			}
			constraintEval.Add(constraintEval, termEval)
			constraintEval.Mod(constraintEval, v.Parameters.Modulus())
		}
		constraintEval.Mul(constraintEval, batchConstsPow[constraint.degree])
		batchedEval.Add(batchedEval, constraintEval)
		batchedEval.Mod(batchedEval, v.Parameters.Modulus())

		batchConstsPow[constraint.degree].Mul(batchConstsPow[constraint.degree], batchConsts[constraint.degree])
		batchConstsPow[constraint.degree].Mod(batchConstsPow[constraint.degree], v.Parameters.Modulus())
	}

	checkEval := big.NewInt(0).Mul(pf.RowCheckEvalProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}
