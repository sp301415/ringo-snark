package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
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

	if int(v.ctx.witnessCount) != len(pf.Witness) || int(v.ctx.publicWitnessCount) != len(pf.PublicWitness) {
		return false
	}

	for i := 0; i < len(pf.Witness); i++ {
		v.oracle.WriteCommitment(pf.Witness[i])
	}
	v.oracle.WriteOpeningProof(pf.OpeningProof)

	if v.ctx.HasLinCheck() {
		v.oracle.WriteCommitment(pf.LinCheckMaskCommitment.MaskCommitment)
		v.oracle.WriteOpeningProof(pf.LinCheckMaskCommitment.OpeningProof)
		v.oracle.WriteBigInt(pf.LinCheckMaskCommitment.MaskSum)
	}

	if v.ctx.HasSumCheck() {
		v.oracle.WriteCommitment(pf.SumCheckMaskCommitment.MaskCommitment)
		v.oracle.WriteOpeningProof(pf.SumCheckMaskCommitment.OpeningProof)
		v.oracle.WriteBigInt(pf.SumCheckMaskCommitment.MaskSum)
	}

	v.oracle.Finalize()

	var batchRowCheckConst *big.Int
	if v.ctx.HasRowCheck() {
		batchRowCheckConst = v.oracle.SampleMod()
	}

	batchLinCheckConst := big.NewInt(0)
	batchLinVec := make([]*big.Int, v.Parameters.Degree())
	if v.ctx.HasLinCheck() {
		v.oracle.SampleModAssign(batchLinCheckConst)

		batchLinVec[0] = v.oracle.SampleMod()
		for i := 1; i < v.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], v.Parameters.Modulus())
		}
	}

	var batchSumCheckConst *big.Int
	if v.ctx.HasSumCheck() {
		batchSumCheckConst = v.oracle.SampleMod()
	}

	if v.ctx.HasRowCheck() {
		v.oracle.WriteCommitment(pf.RowCheckCommitment.QuoCommitment)
		v.oracle.WriteOpeningProof(pf.RowCheckCommitment.OpeningProof)
	}

	if v.ctx.HasLinCheck() {
		v.oracle.WriteCommitment(pf.LinCheckCommitment.QuoCommitment)
		v.oracle.WriteCommitment(pf.LinCheckCommitment.RemCommitment)
		v.oracle.WriteCommitment(pf.LinCheckCommitment.RemShiftCommitment)
		v.oracle.WriteOpeningProof(pf.LinCheckCommitment.OpeningProof)
	}

	if v.ctx.HasSumCheck() {
		v.oracle.WriteCommitment(pf.SumCheckCommitment.QuoCommitment)
		v.oracle.WriteCommitment(pf.SumCheckCommitment.RemCommitment)
		v.oracle.WriteCommitment(pf.SumCheckCommitment.RemShiftCommitment)
		v.oracle.WriteOpeningProof(pf.SumCheckCommitment.OpeningProof)
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
		if !v.rowCheck(batchRowCheckConst, buf, pf) {
			return false
		}
	}

	if v.ctx.HasLinCheck() {
		if !v.linCheck(batchLinCheckConst, batchLinVec, buf, pf) {
			return false
		}
	}

	if v.ctx.HasSumCheck() {
		if !v.sumCheck(batchSumCheckConst, buf, pf) {
			return false
		}
	}

	return true
}

func (v *Verifier) evaluateCircuit(batchConst *big.Int, buf verifierBuffer, constraints []ArithmeticConstraint, pf Proof) *big.Int {
	batchConstPow := big.NewInt(0).Set(batchConst)

	batchedEval := big.NewInt(0)
	for _, constraint := range constraints {
		termEval := big.NewInt(0)
		constraintEval := big.NewInt(0)
		for i := 0; i < len(constraint.witness); i++ {
			termEval.Set(constraint.coeffsBig[i])

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
		constraintEval.Mul(constraintEval, batchConstPow)
		batchedEval.Add(batchedEval, constraintEval)
		batchedEval.Mod(batchedEval, v.Parameters.Modulus())

		batchConstPow.Mul(batchConstPow, batchConst)
		batchConstPow.Mod(batchConstPow, v.Parameters.Modulus())
	}

	return batchedEval
}

func (v *Verifier) rowCheck(batchConst *big.Int, buf verifierBuffer, pf Proof) bool {
	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.RowCheckCommitment.QuoCommitment}, pf.RowCheckCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, pf.RowCheckCommitment.QuoCommitment, pf.RowCheckEvaluationProof.QuoEvalProof) {
		return false
	}

	batchedEval := v.evaluateCircuit(batchConst, buf, v.ctx.arithConstraints, pf)
	checkEval := big.NewInt(0).Mul(pf.RowCheckEvaluationProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}

func (v *Verifier) linCheck(batchConst *big.Int, linCheckVec []*big.Int, buf verifierBuffer, pf Proof) bool {
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

	remShiftCheckEval := big.NewInt(0).Mul(pf.LinCheckEvaluationProof.RemEvalProof.Value, buf.evaluationPoint)
	remShiftCheckEval.Mod(remShiftCheckEval, v.Parameters.Modulus())
	if remShiftCheckEval.Cmp(pf.LinCheckEvaluationProof.RemShiftEvalProof.Value) != 0 {
		return false
	}

	batchConstPow := big.NewInt(0).Set(batchConst)

	linCheckVecEcd := v.encoder.Encode(linCheckVec)
	linCheckVecEcdEval := v.ringQ.Evaluate(linCheckVecEcd, buf.evaluationPoint)

	batchedEval := big.NewInt(0)
	constraintEval0, constraintEval1 := big.NewInt(0), big.NewInt(0)
	linCheckVecTransformed := make([]*big.Int, v.Parameters.Degree())
	for i := 0; i < v.Parameters.Degree(); i++ {
		linCheckVecTransformed[i] = big.NewInt(0)
	}
	for _, transformer := range v.ctx.linTransformers {
		transformer.TransformAssign(linCheckVec, linCheckVecTransformed)
		linCheckVecTransformedEcd := v.encoder.Encode(linCheckVecTransformed)
		linCheckVecTransformedEcdEval := v.ringQ.Evaluate(linCheckVecTransformedEcd, buf.evaluationPoint)
		for i := range v.ctx.linCheckConstraints[transformer] {
			wEcdInEval := pf.EvalProofs[v.ctx.linCheckConstraints[transformer][i][0]].Value
			wEcdOutEval := pf.EvalProofs[v.ctx.linCheckConstraints[transformer][i][1]].Value

			constraintEval0.Mul(wEcdInEval, linCheckVecTransformedEcdEval)
			constraintEval1.Mul(wEcdOutEval, linCheckVecEcdEval)
			constraintEval0.Sub(constraintEval0, constraintEval1)
			constraintEval0.Mod(constraintEval0, v.Parameters.Modulus())

			constraintEval0.Mul(constraintEval0, batchConstPow)
			batchedEval.Add(batchedEval, constraintEval0)
			batchedEval.Mod(batchedEval, v.Parameters.Modulus())

			batchConstPow.Mul(batchConstPow, batchConst)
			batchConstPow.Mod(batchConstPow, v.Parameters.Modulus())
		}
	}

	batchedEval.Add(batchedEval, pf.LinCheckEvaluationProof.MaskEvalProof.Value)
	batchedEval.Mod(batchedEval, v.Parameters.Modulus())

	checkEval := big.NewInt(0).Mul(pf.LinCheckEvaluationProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Add(checkEval, pf.LinCheckEvaluationProof.RemShiftEvalProof.Value)
	checkEval.Add(checkEval, pf.LinCheckMaskCommitment.MaskSum)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}

func (v *Verifier) sumCheck(batchConst *big.Int, buf verifierBuffer, pf Proof) bool {
	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.SumCheckMaskCommitment.MaskCommitment}, pf.SumCheckMaskCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, pf.SumCheckMaskCommitment.MaskCommitment, pf.SumCheckEvaluationProof.MaskEvalProof) {
		return false
	}

	commits := []celpc.Commitment{
		pf.SumCheckCommitment.QuoCommitment,
		pf.SumCheckCommitment.RemCommitment,
		pf.SumCheckCommitment.RemShiftCommitment,
	}
	evalPfs := []celpc.EvaluationProof{
		pf.SumCheckEvaluationProof.QuoEvalProof,
		pf.SumCheckEvaluationProof.RemEvalProof,
		pf.SumCheckEvaluationProof.RemShiftEvalProof,
	}

	if !v.polyVerifier.VerifyOpeningProof(commits, pf.SumCheckCommitment.OpeningProof) {
		return false
	}
	for i := range evalPfs {
		if !v.polyVerifier.VerifyEvaluation(buf.evaluationPoint, commits[i], evalPfs[i]) {
			return false
		}
	}

	remShiftCheckEval := big.NewInt(0).Mul(pf.SumCheckEvaluationProof.RemEvalProof.Value, buf.evaluationPoint)
	remShiftCheckEval.Mod(remShiftCheckEval, v.Parameters.Modulus())
	if remShiftCheckEval.Cmp(pf.SumCheckEvaluationProof.RemShiftEvalProof.Value) != 0 {
		return false
	}

	batchConstPow := big.NewInt(0).Set(batchConst)
	batchedSum, constraintEval := big.NewInt(0), big.NewInt(0)
	for _, sumCheckSum := range v.ctx.sumCheckSums {
		constraintEval.Mul(batchConstPow, sumCheckSum)
		batchedSum.Add(batchedSum, constraintEval)
		batchedSum.Mod(batchedSum, v.Parameters.Modulus())

		batchConstPow.Mul(batchConstPow, batchConst)
		batchConstPow.Mod(batchConstPow, v.Parameters.Modulus())
	}
	batchedSum.Mul(batchedSum, v.encoder.degreeInv)

	batchedEval := v.evaluateCircuit(batchConst, buf, v.ctx.sumCheckConstraints, pf)
	batchedEval.Add(batchedEval, pf.SumCheckEvaluationProof.MaskEvalProof.Value)
	batchedEval.Sub(batchedEval, batchedSum)
	batchedEval.Mod(batchedEval, v.Parameters.Modulus())

	checkEval := big.NewInt(0).Mul(pf.SumCheckEvaluationProof.QuoEvalProof.Value, buf.vanishPoint)
	checkEval.Add(checkEval, pf.SumCheckEvaluationProof.RemShiftEvalProof.Value)
	checkEval.Add(checkEval, pf.SumCheckMaskCommitment.MaskSum)
	checkEval.Mod(checkEval, v.Parameters.Modulus())

	return batchedEval.Cmp(checkEval) == 0
}
