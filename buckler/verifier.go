package buckler

import (
	"math"
	"math/big"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
	"github.com/sp301415/rlwe-piop/num"
)

// Verifier verifies the given circuit.
type Verifier struct {
	Parameters celpc.Parameters

	ringQ     *bigring.BigRing
	baseRingQ *bigring.BigRing

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

		ringQ:     bigring.NewBigRing(embedDegree, params.Modulus()),
		baseRingQ: bigring.NewBigRing(params.Degree(), params.Modulus()),

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

	if v.ctx.HasLinearCheck() {
		v.oracle.WriteCommitment(pf.LinCheckMaskCommitment.MaskCommitment)
		v.oracle.WriteOpeningProof(pf.LinCheckMaskCommitment.OpeningProof)
		v.oracle.WriteBigInt(pf.LinCheckMaskCommitment.MaskSum)
	}

	v.oracle.Finalize()

	batchArithConsts := make(map[int]*big.Int, len(v.ctx.arithConstraints))
	if v.ctx.HasRowCheck() {
		for _, constraint := range v.ctx.arithConstraints {
			if _, ok := batchArithConsts[constraint.degree]; !ok {
				batchArithConsts[constraint.degree] = v.oracle.SampleMod()
			}
		}
	}

	batchLinConst := big.NewInt(0)
	batchLinVec := make([]*big.Int, v.Parameters.Degree())
	if v.ctx.HasLinearCheck() {
		v.oracle.SampleModAssign(batchLinConst)

		batchLinVec[0] = v.oracle.SampleMod()
		for i := 1; i < v.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], v.Parameters.Modulus())
		}
	}

	if v.ctx.HasRowCheck() {
		v.oracle.WriteCommitment(pf.RowCheckCommitment.QuoCommitment)
		v.oracle.WriteOpeningProof(pf.RowCheckCommitment.OpeningProof)
	}

	if v.ctx.HasLinearCheck() {
		v.oracle.WriteCommitment(pf.LinCheckCommitment.QuoCommitment)
		v.oracle.WriteCommitment(pf.LinCheckCommitment.RemCommitment)
		v.oracle.WriteCommitment(pf.LinCheckCommitment.RemShiftCommitment)
		v.oracle.WriteOpeningProof(pf.LinCheckCommitment.OpeningProof)
	}

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

	if v.ctx.HasRowCheck() {
		if !v.rowCheck(batchArithConsts, buf, pf) {
			return false
		}
	}

	if v.ctx.HasLinearCheck() {
		if !v.linCheck(batchLinConst, batchLinVec, buf, pf) {
			return false
		}
	}

	return true
}

func (v *Verifier) rowCheck(batchConsts map[int]*big.Int, buf verifierBuffer, pf Proof) bool {
	batchConstsPow := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPow[k] = big.NewInt(0).Set(v)
	}

	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.RowCheckCommitment.QuoCommitment}, pf.RowCheckCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, pf.RowCheckCommitment.QuoCommitment, pf.RowCheckEvaluationProof.QuoEvalProof) {
		return false
	}

	batchedEval := big.NewInt(0)
	for _, constraint := range v.ctx.arithConstraints {
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

	checkEval := big.NewInt(0).Mul(pf.RowCheckEvaluationProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}

func (v *Verifier) linCheck(batchConst *big.Int, linCheckVec []*big.Int, buf verifierBuffer, pf Proof) bool {
	batchConstPow := big.NewInt(0).Set(batchConst)

	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.LinCheckMaskCommitment.MaskCommitment}, pf.LinCheckMaskCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, pf.LinCheckMaskCommitment.MaskCommitment, pf.LinCheckEvaluationProof.MaskEvalProof) {
		return false
	}

	commits := []celpc.Commitment{
		pf.LinCheckCommitment.QuoCommitment,
		pf.LinCheckCommitment.RemCommitment,
		pf.LinCheckCommitment.RemShiftCommitment,
	}
	evalPfs := []celpc.EvaluationProof{
		pf.LinCheckEvaluationProof.QuoEvalProof,
		pf.LinCheckEvaluationProof.RemEvalProof,
		pf.LinCheckEvaluationProof.RemShiftEvalProof,
	}

	if !v.polyVerifier.VerifyOpeningProof(commits, pf.LinCheckCommitment.OpeningProof) {
		return false
	}
	for i := range evalPfs {
		if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, commits[i], evalPfs[i]) {
			return false
		}
	}

	remShiftCheckEval := big.NewInt(0).Mul(pf.RemEvalProof.Value, buf.evaluationPoint)
	remShiftCheckEval.Mod(remShiftCheckEval, v.Parameters.Modulus())
	if remShiftCheckEval.Cmp(pf.RemShiftEvalProof.Value) != 0 {
		return false
	}

	linCheckVecEcd := v.encoder.Encode(linCheckVec)
	linCheckVecEcdEval := v.ringQ.Evaluate(linCheckVecEcd, buf.evaluationPoint)

	batchedEval := big.NewInt(0)

	linCheckVecNTTTrans := make([]*big.Int, v.Parameters.Degree())
	for i := 0; i < v.Parameters.Degree(); i++ {
		linCheckVecNTTTrans[i] = big.NewInt(0).Set(linCheckVec[v.Parameters.Degree()-i-1])
	}
	v.baseRingQ.InvNTTInPlace(linCheckVecNTTTrans)
	linCheckVecNTTTransEcd := v.encoder.Encode(linCheckVecNTTTrans)
	linCheckVecNTTTransEcdEval := v.ringQ.Evaluate(linCheckVecNTTTransEcd, buf.evaluationPoint)

	for _, nttConstraint := range v.ctx.nttConstraints {
		wEcdInEval := pf.EvalProofs[nttConstraint[0]].Value
		wEcdOutEval := pf.EvalProofs[nttConstraint[1]].Value

		nttConstraintEval0 := big.NewInt(0).Mul(wEcdInEval, linCheckVecNTTTransEcdEval)
		nttConstraintEval1 := big.NewInt(0).Mul(wEcdOutEval, linCheckVecEcdEval)
		nttConstraintEval0.Sub(nttConstraintEval0, nttConstraintEval1)
		nttConstraintEval0.Mod(nttConstraintEval0, v.Parameters.Modulus())

		nttConstraintEval0.Mul(nttConstraintEval0, batchConstPow)
		batchedEval.Add(batchedEval, nttConstraintEval0)
		batchedEval.Mod(batchedEval, v.Parameters.Modulus())

		batchConstPow.Mul(batchConstPow, batchConst)
		batchConstPow.Mod(batchConstPow, v.Parameters.Modulus())
	}

	for i := range v.ctx.autConstraints {
		autIdx := v.ctx.autConstraintsIdx[i]
		autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*v.Parameters.Degree())))
		linCheckVecAutTrans := v.baseRingQ.AutomorphismNTT(bigring.BigNTTPoly{Coeffs: linCheckVec}, autIdxInv).Coeffs
		linCheckVecAutTransEcd := v.encoder.Encode(linCheckVecAutTrans)
		linCheckVecAutTransEval := v.ringQ.Evaluate(linCheckVecAutTransEcd, buf.evaluationPoint)

		for _, autConstraint := range v.ctx.autConstraints[i] {
			wEcdInEval := pf.EvalProofs[autConstraint[0]].Value
			wEcdOutEval := pf.EvalProofs[autConstraint[1]].Value

			autConstraintEval0 := big.NewInt(0).Mul(wEcdInEval, linCheckVecAutTransEval)
			autConstraintEval1 := big.NewInt(0).Mul(wEcdOutEval, linCheckVecEcdEval)
			autConstraintEval0.Sub(autConstraintEval0, autConstraintEval1)
			autConstraintEval0.Mod(autConstraintEval0, v.Parameters.Modulus())

			autConstraintEval0.Mul(autConstraintEval0, batchConstPow)
			batchedEval.Add(batchedEval, autConstraintEval0)
			batchedEval.Mod(batchedEval, v.Parameters.Modulus())

			batchConstPow.Mul(batchConstPow, batchConst)
			batchConstPow.Mod(batchConstPow, v.Parameters.Modulus())
		}
	}

	batchedEval.Add(batchedEval, pf.LinCheckEvaluationProof.MaskEvalProof.Value)
	batchedEval.Mod(batchedEval, v.Parameters.Modulus())

	checkEval := big.NewInt(0).Mul(pf.LinCheckEvaluationProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Add(checkEval, pf.RemShiftEvalProof.Value)
	checkEval.Add(checkEval, pf.LinCheckMaskCommitment.MaskSum)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}
