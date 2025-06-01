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

	buffer verifierBuffer
}

type verifierBuffer struct {
	evalPoint   *big.Int
	vanishPoint *big.Int

	pEcd    bigring.BigPoly
	pEcdNTT bigring.BigNTTPoly

	batched *big.Int
	eval    *big.Int
	term    *big.Int
	check   *big.Int

	batchConstRowCheckPow []*big.Int
	batchConstLinCheckPow []*big.Int
	batchConstSumCheckPow []*big.Int

	linCheckVec          []*big.Int
	linCheckVecTrans     []*big.Int
	linCheckVecEval      *big.Int
	linCheckVecTransEval *big.Int

	batchedSum *big.Int
}

// newVerifierBuffer initializes a new verifier buffer.
func newVerifierBuffer(params celpc.Parameters, ringQ *bigring.BigRing, ctx *Context) verifierBuffer {
	batchConstRowCheckPow := make([]*big.Int, len(ctx.arithConstraints))
	for i := range batchConstRowCheckPow {
		batchConstRowCheckPow[i] = big.NewInt(0).Set(params.Modulus())
	}

	batchConstLinCheckPow := make([]*big.Int, 0)
	for _, transformer := range ctx.linCheck {
		for range ctx.linCheckConstraints[transformer] {
			batchConstLinCheckPow = append(batchConstLinCheckPow, big.NewInt(0).Set(params.Modulus()))
		}
	}

	batchConstSumCheckPow := make([]*big.Int, len(ctx.sumCheckConstraints))
	for i := range batchConstSumCheckPow {
		batchConstSumCheckPow[i] = big.NewInt(0).Set(params.Modulus())
	}

	linCheckVec := make([]*big.Int, params.Degree())
	linCheckVecTrans := make([]*big.Int, params.Degree())
	for i := 0; i < params.Degree(); i++ {
		linCheckVec[i] = big.NewInt(0).Set(params.Modulus())
		linCheckVecTrans[i] = big.NewInt(0).Set(params.Modulus())
	}

	return verifierBuffer{
		evalPoint:   big.NewInt(0).Set(params.Modulus()),
		vanishPoint: big.NewInt(0).Set(params.Modulus()),

		pEcd:    ringQ.NewPoly(),
		pEcdNTT: ringQ.NewNTTPoly(),

		batched: big.NewInt(0).Set(params.Modulus()),
		eval:    big.NewInt(0).Set(params.Modulus()),
		term:    big.NewInt(0).Set(params.Modulus()),
		check:   big.NewInt(0).Set(params.Modulus()),

		batchConstRowCheckPow: batchConstRowCheckPow,
		batchConstLinCheckPow: batchConstLinCheckPow,
		batchConstSumCheckPow: batchConstSumCheckPow,

		linCheckVec:          linCheckVec,
		linCheckVecTrans:     linCheckVecTrans,
		linCheckVecEval:      big.NewInt(0).Set(params.Modulus()),
		linCheckVecTransEval: big.NewInt(0).Set(params.Modulus()),

		batchedSum: big.NewInt(0).Set(params.Modulus()),
	}
}

// Verify verifies the circuit with the given proof.
func (v *Verifier) Verify(ck celpc.AjtaiCommitKey, pf Proof) bool {
	v.oracle.Reset()
	v.polyVerifier.Commiter = celpc.NewAjtaiCommiter(v.Parameters, ck)

	if int(v.ctx.witnessCount) != len(pf.Witness) || int(v.ctx.publicWitnessCount) != len(pf.PublicWitness) {
		return false
	}

	for i := range pf.Witness {
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

	if v.ctx.HasRowCheck() {
		v.oracle.SampleModAssign(v.buffer.batchConstRowCheckPow[0])
		for i := 1; i < len(v.buffer.batchConstRowCheckPow); i++ {
			v.buffer.batchConstRowCheckPow[i].Mul(v.buffer.batchConstRowCheckPow[i-1], v.buffer.batchConstRowCheckPow[0])
			v.buffer.batchConstRowCheckPow[i].Mod(v.buffer.batchConstRowCheckPow[i], v.Parameters.Modulus())
		}
	}

	if v.ctx.HasLinCheck() {
		v.oracle.SampleModAssign(v.buffer.batchConstLinCheckPow[0])
		for i := 1; i < len(v.buffer.batchConstLinCheckPow); i++ {
			v.buffer.batchConstLinCheckPow[i].Mul(v.buffer.batchConstLinCheckPow[i-1], v.buffer.batchConstLinCheckPow[0])
			v.buffer.batchConstLinCheckPow[i].Mod(v.buffer.batchConstLinCheckPow[i], v.Parameters.Modulus())
		}

		v.oracle.SampleModAssign(v.buffer.linCheckVec[0])
		for i := 1; i < v.Parameters.Degree(); i++ {
			v.buffer.linCheckVec[i].Mul(v.buffer.linCheckVec[i-1], v.buffer.linCheckVec[0])
			v.buffer.linCheckVec[i].Mod(v.buffer.linCheckVec[i], v.Parameters.Modulus())
		}
	}

	if v.ctx.HasSumCheck() {
		v.oracle.SampleModAssign(v.buffer.batchConstSumCheckPow[0])
		for i := 1; i < len(v.buffer.batchConstSumCheckPow); i++ {
			v.buffer.batchConstSumCheckPow[i].Mul(v.buffer.batchConstSumCheckPow[i-1], v.buffer.batchConstSumCheckPow[0])
			v.buffer.batchConstSumCheckPow[i].Mod(v.buffer.batchConstSumCheckPow[i], v.Parameters.Modulus())
		}
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

	v.oracle.SampleModAssign(v.buffer.evalPoint)
	v.buffer.vanishPoint.Exp(v.buffer.evalPoint, big.NewInt(int64(v.Parameters.Degree())), v.Parameters.Modulus())
	v.buffer.vanishPoint.Sub(v.buffer.vanishPoint, big.NewInt(1))

	publicWitnessEvals := make([]*big.Int, len(pf.PublicWitness))
	for i := range pf.PublicWitness {
		v.encoder.EncodeAssign(pf.PublicWitness[i], v.buffer.pEcd)
		publicWitnessEvals[i] = big.NewInt(0)
		v.ringQ.EvaluateAssign(v.buffer.pEcd, v.buffer.evalPoint, publicWitnessEvals[i])
	}

	if !v.polyVerifier.VerifyOpeningProof(pf.Witness, pf.OpeningProof) {
		return false
	}
	for i := range pf.Witness {
		if !v.polyVerifier.VerifyEvaluation(v.buffer.evalPoint, pf.Witness[i], pf.EvalProofs[i]) {
			return false
		}
	}

	if v.ctx.HasRowCheck() {
		if !v.rowCheck(v.buffer.batchConstRowCheckPow, v.buffer.evalPoint, v.buffer.vanishPoint, publicWitnessEvals, pf) {
			return false
		}
	}

	if v.ctx.HasLinCheck() {
		if !v.linCheck(v.buffer.batchConstLinCheckPow, v.buffer.linCheckVec, v.buffer.evalPoint, v.buffer.vanishPoint, pf) {
			return false
		}
	}

	if v.ctx.HasSumCheck() {
		if !v.sumCheck(v.buffer.batchConstSumCheckPow, v.buffer.evalPoint, v.buffer.vanishPoint, publicWitnessEvals, pf) {
			return false
		}
	}

	return true
}

func (v *Verifier) evaluateCircuitAssign(batchConstPow []*big.Int, constraints []ArithmeticConstraint, pwEvals []*big.Int, pf Proof, batched *big.Int) {
	batched.SetUint64(0)

	for c, constraint := range constraints {
		v.buffer.eval.SetUint64(0)
		for i := range constraints[c].witness {
			v.buffer.term.Set(constraint.coeffsBig[i])

			if constraint.coeffsPublicWitness[i] != -1 {
				v.buffer.term.Mul(v.buffer.term, pwEvals[constraint.coeffsPublicWitness[i]])
				v.buffer.term.Mod(v.buffer.term, v.Parameters.Modulus())
			}

			for j := range constraint.witness[i] {
				v.buffer.term.Mul(v.buffer.term, pf.EvalProofs[constraint.witness[i][j]].Value)
				v.buffer.term.Mod(v.buffer.term, v.Parameters.Modulus())
			}
			v.buffer.eval.Add(v.buffer.eval, v.buffer.term)
			v.buffer.eval.Mod(v.buffer.eval, v.Parameters.Modulus())
		}
		v.buffer.eval.Mul(v.buffer.eval, batchConstPow[c])

		batched.Add(batched, v.buffer.eval)
		batched.Mod(batched, v.Parameters.Modulus())
	}
}

func (v *Verifier) rowCheck(batchConstPow []*big.Int, evalPoint, vanishPoint *big.Int, pwEvals []*big.Int, pf Proof) bool {
	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.RowCheckCommitment.QuoCommitment}, pf.RowCheckCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(evalPoint, pf.RowCheckCommitment.QuoCommitment, pf.RowCheckEvaluationProof.QuoEvalProof) {
		return false
	}

	v.evaluateCircuitAssign(batchConstPow, v.ctx.arithConstraints, pwEvals, pf, v.buffer.batched)

	v.buffer.check.Mul(pf.RowCheckEvaluationProof.QuoEvalProof.Value, vanishPoint)
	v.buffer.check.Mod(v.buffer.check, v.Parameters.Modulus())

	return v.buffer.batched.Cmp(v.buffer.check) == 0
}

func (v *Verifier) linCheck(batchConstPow []*big.Int, linCheckVec []*big.Int, evalPoint, vanishPoint *big.Int, pf Proof) bool {
	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.LinCheckMaskCommitment.MaskCommitment}, pf.LinCheckMaskCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(evalPoint, pf.LinCheckMaskCommitment.MaskCommitment, pf.LinCheckEvaluationProof.MaskEvalProof) {
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
		if !v.polyVerifier.VerifyEvaluation(evalPoint, commits[i], evalPfs[i]) {
			return false
		}
	}

	v.buffer.check.Mul(pf.LinCheckEvaluationProof.RemEvalProof.Value, evalPoint)
	v.buffer.check.Mod(v.buffer.check, v.Parameters.Modulus())
	if v.buffer.check.Cmp(pf.LinCheckEvaluationProof.RemShiftEvalProof.Value) != 0 {
		return false
	}

	v.encoder.EncodeAssign(linCheckVec, v.buffer.pEcd)
	v.ringQ.EvaluateAssign(v.buffer.pEcd, evalPoint, v.buffer.linCheckVecEval)

	v.buffer.batched.SetUint64(0)
	powIdx := 0
	for _, transformer := range v.ctx.linCheck {
		transformer.TransformAssign(linCheckVec, v.buffer.linCheckVecTrans)
		v.encoder.EncodeAssign(v.buffer.linCheckVecTrans, v.buffer.pEcd)
		v.ringQ.EvaluateAssign(v.buffer.pEcd, evalPoint, v.buffer.linCheckVecTransEval)
		for i := range v.ctx.linCheckConstraints[transformer] {
			wEcdInEval := pf.EvalProofs[v.ctx.linCheckConstraints[transformer][i][0]].Value
			wEcdOutEval := pf.EvalProofs[v.ctx.linCheckConstraints[transformer][i][1]].Value

			v.buffer.eval.Mul(wEcdInEval, v.buffer.linCheckVecTransEval)
			v.buffer.term.Mul(wEcdOutEval, v.buffer.linCheckVecEval)
			v.buffer.eval.Sub(v.buffer.eval, v.buffer.term)
			v.buffer.eval.Mod(v.buffer.eval, v.Parameters.Modulus())

			v.buffer.eval.Mul(v.buffer.eval, batchConstPow[powIdx])
			v.buffer.batched.Add(v.buffer.batched, v.buffer.eval)
			v.buffer.batched.Mod(v.buffer.batched, v.Parameters.Modulus())

			powIdx++
		}
	}

	v.buffer.batched.Add(v.buffer.batched, pf.LinCheckEvaluationProof.MaskEvalProof.Value)
	v.buffer.batched.Mod(v.buffer.batched, v.Parameters.Modulus())

	v.buffer.check.Mul(pf.LinCheckEvaluationProof.QuoEvalProof.Value, vanishPoint)
	v.buffer.check.Add(v.buffer.check, pf.LinCheckEvaluationProof.RemShiftEvalProof.Value)
	v.buffer.check.Add(v.buffer.check, pf.LinCheckMaskCommitment.MaskSum)
	v.buffer.check.Mod(v.buffer.check, v.Parameters.Modulus())

	return v.buffer.batched.Cmp(v.buffer.check) == 0
}

func (v *Verifier) sumCheck(batchConstPow []*big.Int, evalPoint, vanishPoint *big.Int, pwEvals []*big.Int, pf Proof) bool {
	if !v.polyVerifier.VerifyOpeningProof([]celpc.Commitment{pf.SumCheckMaskCommitment.MaskCommitment}, pf.SumCheckMaskCommitment.OpeningProof) {
		return false
	}
	if !v.polyVerifier.VerifyEvaluation(evalPoint, pf.SumCheckMaskCommitment.MaskCommitment, pf.SumCheckEvaluationProof.MaskEvalProof) {
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
		if !v.polyVerifier.VerifyEvaluation(evalPoint, commits[i], evalPfs[i]) {
			return false
		}
	}

	v.buffer.check.Mul(pf.LinCheckEvaluationProof.RemEvalProof.Value, evalPoint)
	v.buffer.check.Mod(v.buffer.check, v.Parameters.Modulus())
	if v.buffer.check.Cmp(pf.LinCheckEvaluationProof.RemShiftEvalProof.Value) != 0 {
		return false
	}

	v.buffer.batchedSum.SetUint64(0)
	for i, sumCheckSum := range v.ctx.sumCheckSums {
		v.buffer.eval.Mul(batchConstPow[i], sumCheckSum)
		v.buffer.batchedSum.Add(v.buffer.batchedSum, v.buffer.eval)
		v.buffer.batchedSum.Mod(v.buffer.batchedSum, v.Parameters.Modulus())
	}
	v.buffer.batchedSum.Mul(v.buffer.batchedSum, v.encoder.degreeInv)

	v.evaluateCircuitAssign(batchConstPow, v.ctx.sumCheckConstraints, pwEvals, pf, v.buffer.batched)
	v.buffer.batched.Add(v.buffer.batched, pf.SumCheckEvaluationProof.MaskEvalProof.Value)
	v.buffer.batched.Sub(v.buffer.batched, v.buffer.batchedSum)
	v.buffer.batched.Mod(v.buffer.batched, v.Parameters.Modulus())

	v.buffer.check.Mul(pf.SumCheckEvaluationProof.QuoEvalProof.Value, vanishPoint)
	v.buffer.check.Add(v.buffer.check, pf.SumCheckEvaluationProof.RemShiftEvalProof.Value)
	v.buffer.check.Add(v.buffer.check, pf.SumCheckMaskCommitment.MaskSum)
	v.buffer.check.Mod(v.buffer.check, v.Parameters.Modulus())

	return v.buffer.batched.Cmp(v.buffer.check) == 0
}
