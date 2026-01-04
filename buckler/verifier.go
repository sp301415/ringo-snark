package buckler

import (
	"bytes"
	"crypto/sha256"
	"reflect"

	fiatshamir "github.com/consensys/gnark-crypto/fiat-shamir"
	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/num"
)

// Verifier verifies the given circuit.
type Verifier[E num.Uint[E]] struct {
	JindoParams jindo.Parameters

	polyEval *bigpoly.CyclicEvaluator[E]

	ecd *Encoder[E]

	polyVerifier *jindo.Verifier[E]

	ctx *Context[E]
}

// Verify verifies the proof for the given public assignment.
func (v *Verifier[E]) Verify(c Circuit[E], pf *Proof[E]) bool {
	if v.ctx.circType != reflect.TypeOf(c).Elem() {
		return false
	}

	var z E

	pw := make([]PublicWitness[E], v.ctx.pwCnt)
	wk := &walker[E]{}
	if err := wk.vrfWalk(v, reflect.ValueOf(c), pw); err != nil {
		return false
	}

	for i := wk.pwCnt; i < v.ctx.pwCnt; i++ {
		pw[i] = make(PublicWitness[E], v.ctx.rank)
		for j := range v.ctx.rank {
			pw[i][j] = pw[i][j].New()
		}
	}

	for id, bound := range v.ctx.twoDcmpBound {
		base := decomposeBase(bound)

		pwBaseID := witnessToID(v.ctx.twoDcmpBase[id])
		pwMaskID := witnessToID(v.ctx.twoDcmpMask[id])
		for i := range base {
			pw[pwBaseID][i].SetBigInt(base[i])
			pw[pwMaskID][i].SetInt64(1)
		}
	}

	chalNames := []string{
		"arithBatchConst",
		"linCheckBatchConst",
		"linCheckConst",
		"sumCheckBatchConst",
		"evalPoint",
	}
	oracle := fiatshamir.NewTranscript(sha256.New(), chalNames...)
	var oracleBuf bytes.Buffer

	pwEcd := make([]*bigpoly.Poly[E], v.ctx.pwCnt)
	pwEcdNTT := make([]*bigpoly.Poly[E], v.ctx.pwCnt)
	for i := range pw {
		pwEcd[i] = v.ecd.Encode(pw[i])
		pwEcdNTT[i] = v.polyEval.NTT(pwEcd[i])
	}

	for i := range v.ctx.wCnt {
		pf.Witness[i].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracleBuf.Reset()
	}

	roundComIdx := v.ctx.wCnt

	var linCheckMaskEval E
	if v.ctx.HasLinearCheck() {
		linCheckMaskEval = pf.Evals[roundComIdx]
		pf.Witness[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracle.Bind("arithBatchConst", pf.LinCheckMaskSum.Marshal())
		oracleBuf.Reset()
		roundComIdx++
	}

	var sumCheckMaskEval E
	if v.ctx.HasSumCheck() {
		sumCheckMaskEval = pf.Evals[roundComIdx]
		pf.Witness[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracle.Bind("arithBatchConst", pf.SumCheckMaskSum.Marshal())
		oracleBuf.Reset()
		roundComIdx++
	}

	arithBatchConstBytes, err := oracle.ComputeChallenge("arithBatchConst")
	if err != nil {
		return false
	}

	linCheckBatchConstBytes, err := oracle.ComputeChallenge("linCheckBatchConst")
	if err != nil {
		return false
	}

	linCheckConstBytes, err := oracle.ComputeChallenge("linCheckConst")
	if err != nil {
		return false
	}

	sumCheckBatchConstBytes, err := oracle.ComputeChallenge("sumCheckBatchConst")
	if err != nil {
		return false
	}

	for i := int(roundComIdx); i < len(pf.Witness); i++ {
		pf.Witness[i].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()
	}

	evalPointBytes, err := oracle.ComputeChallenge("evalPoint")
	if err != nil {
		return false
	}
	evalPoint := z.New().SetBytes(evalPointBytes)

	if !v.polyVerifier.Verify(evalPoint, pf.Witness, pf.Evals, pf.EvalProof) {
		return false
	}

	vanishEval := num.ExpE(evalPoint, uint64(v.ctx.rank))
	vanishEval.Sub(vanishEval, z.New().SetUint64(1))

	pwEvals := make([]E, v.ctx.pwCnt)
	for i := range pwEvals {
		pwEvals[i] = pwEcd[i].Evaluate(evalPoint)
	}

	if v.ctx.HasArithmeticCheck() {
		batchConst := z.New().SetBytes(arithBatchConstBytes)

		if !v.arithCheck(batchConst, vanishEval, pf.Evals[roundComIdx], pf.Evals, pwEvals) {
			return false
		}
		roundComIdx++
	}

	if v.ctx.HasLinearCheck() {
		batchConst := z.New().SetBytes(linCheckBatchConstBytes)
		linCheckConst := z.New().SetBytes(linCheckConstBytes)

		quoEval, remLoEval, remHiEval := pf.Evals[roundComIdx], pf.Evals[roundComIdx+1], pf.Evals[roundComIdx+2]
		if !v.linCheck(batchConst, linCheckConst, linCheckMaskEval, evalPoint, vanishEval, pf.LinCheckMaskSum, quoEval, remLoEval, remHiEval, pf.Evals, pwEvals) {
			return false
		}
		roundComIdx += 3
	}

	if v.ctx.HasSumCheck() {
		batchConst := z.New().SetBytes(sumCheckBatchConstBytes)

		quoEval, remLoEval, remHiEval := pf.Evals[roundComIdx], pf.Evals[roundComIdx+1], pf.Evals[roundComIdx+2]
		if !v.sumCheck(batchConst, sumCheckMaskEval, evalPoint, vanishEval, pf.SumCheckMaskSum, quoEval, remLoEval, remHiEval, pf.Evals, pwEvals) {
			return false
		}
		roundComIdx += 3
	}

	return true
}

func (v *Verifier[E]) evalCircuit(batchConst E, constraints []ArithmeticConstraint[E], evals []E, pwEvals []E) E {
	var z E

	out, eval, term := z.New(), z.New(), z.New()
	for _, c := range constraints {
		eval.SetUint64(0)
		for i := range c.witness {
			term.Set(c.coeffs[i])
			if c.hasCoeffPublicWitness[i] {
				term.Mul(term, pwEvals[c.coeffsPublicWitness[i]])
			}
			for j := range c.witness[i] {
				term.Mul(term, evals[c.witness[i][j]])
			}
			eval.Add(eval, term)
		}
		eval.Mul(eval, batchConst)
		out.Add(out, eval)
	}

	return out
}

func (v *Verifier[E]) arithCheck(batchConst, vanishEval, quoEval E, evals []E, pwEvals []E) bool {
	var z E
	eval := v.evalCircuit(batchConst, v.ctx.arithConstraints, evals, pwEvals)
	test := z.New().Mul(quoEval, vanishEval)
	return eval.Cmp(test) == 0
}

func (v *Verifier[E]) linCheck(batchConst, linCheckConst, linCheckMaskEval, evalPoint, vanishEval, linCheckMaskSum, quoEval, remLoEval, remHiEval E, evals []E, pwEvals []E) bool {
	var z E

	remLoShiftEval := num.ExpE(evalPoint, uint64(v.JindoParams.Rank()-(v.ctx.rank-1)))
	remLoShiftEval.Mul(remLoShiftEval, remLoEval)
	if remHiEval.Cmp(remLoShiftEval) != 0 {
		return false
	}

	linCheckVec := make([]E, v.ctx.rank)
	linCheckVec[0] = z.New().SetUint64(1)
	for i := 1; i < v.ctx.rank; i++ {
		linCheckVec[i] = z.New().Mul(linCheckVec[i-1], linCheckConst)
	}
	linCheckEval := v.ecd.Encode(linCheckVec).Evaluate(evalPoint)

	linCheckVecTr := make([]E, v.ctx.rank)
	for i := range linCheckVec {
		linCheckVecTr[i] = z.New()
	}
	linCheckEcdTr := v.polyEval.NewPoly(false)

	eval, term, termMul := z.New(), z.New(), z.New()
	for _, tr := range v.ctx.linTransformers {
		tr.TransposeTo(linCheckVecTr, linCheckVec)
		v.ecd.EncodeTo(linCheckEcdTr, linCheckVecTr)
		linCheckTrEval := linCheckEcdTr.Evaluate(evalPoint)
		for _, wIDs := range v.ctx.linCheckConstraints[tr] {
			wOut, wIn := evals[wIDs[0]], evals[wIDs[1]]
			term.Mul(linCheckTrEval, wIn)
			termMul.Mul(linCheckEval, wOut)
			term.Sub(term, termMul)
			eval.Mul(eval, batchConst)
			eval.Add(eval, term)
		}
	}
	eval.Mul(eval, batchConst)
	eval.Add(eval, linCheckMaskEval)

	test := z.New().Mul(quoEval, vanishEval)
	rem := z.New().Mul(remLoEval, evalPoint)
	test.Add(test, rem)
	test.Add(test, linCheckMaskSum)

	return eval.Cmp(test) == 0
}

func (v *Verifier[E]) sumCheck(batchConst, sumCheckMaskEval, evalPoint, vanishEval, sumCheckMaskSum, quoEval, remLoEval, remHiEval E, evals []E, pwEvals []E) bool {
	var z E

	remLoShiftEval := num.ExpE(evalPoint, uint64(v.JindoParams.Rank()-(v.ctx.rank-1)))
	remLoShiftEval.Mul(remLoShiftEval, remLoEval)
	if remHiEval.Cmp(remLoShiftEval) != 0 {
		return false
	}

	eval := v.evalCircuit(batchConst, v.ctx.sumCheckConstraints, evals, pwEvals)
	eval.Mul(eval, batchConst)
	eval.Add(eval, sumCheckMaskEval)

	test := z.New().Mul(quoEval, vanishEval)
	rem := z.New().Mul(remLoEval, evalPoint)
	test.Add(test, rem)
	test.Add(test, sumCheckMaskSum)

	return eval.Cmp(test) == 0
}
