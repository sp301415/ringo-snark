package buckler

import (
	"bytes"
	"crypto/sha256"
	"fmt"
	"math/big"
	"reflect"

	fiatshamir "github.com/consensys/gnark-crypto/fiat-shamir"
	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
)

// Prover proves the given circuit.
type Prover[E bignum.Uint[E]] struct {
	JindoParams jindo.Parameters

	polyEval *bigpoly.CyclicEvaluator[E]

	ecd *Encoder[E]

	polyProver *jindo.Prover[E]

	ctx *Context[E]
}

// witnessData holds the data of the witnesses during proving.
type witnessData[E bignum.Uint[E]] struct {
	pw []PublicWitness[E]
	w  []Witness[E]

	pwEcd    []*bigpoly.Poly[E]
	pwEcdNTT []*bigpoly.Poly[E]
	wEcd     []*bigpoly.Poly[E]
	wEcdNTT  []*bigpoly.Poly[E]
}

// Prove generates a proof for the given circuit and witnesses.
func (p *Prover[E]) Prove(c Circuit[E]) (*Proof[E], error) {
	if p.ctx.circType != reflect.TypeOf(c).Elem() {
		return nil, fmt.Errorf("circuit type mismatch")
	}

	var z E

	wData := witnessData[E]{
		pw: make([]PublicWitness[E], p.ctx.pwCnt),
		w:  make([]Witness[E], p.ctx.wCnt),
	}

	wk := &walker[E]{}
	if err := wk.prvWalk(p, reflect.ValueOf(c), wData.pw, wData.w); err != nil {
		return nil, err
	}

	for i := wk.pwCnt; i < p.ctx.pwCnt; i++ {
		wData.pw[i] = make(PublicWitness[E], p.ctx.rank)
		for j := range p.ctx.rank {
			wData.pw[i][j] = wData.pw[i][j].New()
		}
	}
	for i := wk.wCnt; i < p.ctx.wCnt; i++ {
		wData.w[i] = make(Witness[E], p.ctx.rank)
		for j := range p.ctx.rank {
			wData.w[i][j] = wData.w[i][j].New()
		}
	}

	mod := z.New().SetInt64(-1).BigInt(new(big.Int))
	mod.Add(mod, big.NewInt(1))

	bigCoeff := new(big.Int)

	for id, wDcmps := range p.ctx.infDcmpWitness {
		base := decomposeBase(p.ctx.infDcmpBound[id])
		for i := range p.ctx.rank {
			wData.w[id][i].BigInt(bigCoeff)
			dcmp := decomposeBig(bigCoeff, base, mod)
			for j, wDcmp := range wDcmps {
				wData.w[witnessToID(wDcmp)][i].SetInt64(dcmp[j])
			}
		}
	}

	sqNm, mul := new(big.Int), new(big.Int)
	for id, bound := range p.ctx.twoDcmpBound {
		base := decomposeBase(bound)

		pwBaseID := witnessToID(p.ctx.twoDcmpBase[id])
		pwMaskID := witnessToID(p.ctx.twoDcmpMask[id])
		for i := range base {
			wData.pw[pwBaseID][i].SetBigInt(base[i])
			wData.pw[pwMaskID][i].SetInt64(1)
		}

		for i := range p.ctx.rank {
			wData.w[id][i].BigInt(bigCoeff)
			mul.Mul(bigCoeff, bigCoeff)
			sqNm.Add(sqNm, mul)
		}
		sqNm.Mod(sqNm, mod)

		dcmp := decomposeBig(sqNm, base, mod)
		for i := range dcmp {
			wData.w[witnessToID(p.ctx.twoDcmpWitness[id])][i].SetInt64(dcmp[i])
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

	wData.pwEcd = make([]*bigpoly.Poly[E], p.ctx.pwCnt)
	wData.pwEcdNTT = make([]*bigpoly.Poly[E], p.ctx.pwCnt)
	for i := range wData.pw {
		wData.pwEcd[i] = p.ecd.Encode(wData.pw[i])
		wData.pwEcdNTT[i] = p.polyEval.NTT(wData.pwEcd[i])
	}

	wData.wEcd = make([]*bigpoly.Poly[E], p.ctx.wCnt)
	wData.wEcdNTT = make([]*bigpoly.Poly[E], p.ctx.wCnt)
	coms := make([]*jindo.Commitment, p.ctx.batch())
	opens := make([]*jindo.Opening, p.ctx.batch())
	comPolys := make([][]E, p.ctx.batch())
	for i := range wData.w {
		wData.wEcd[i] = p.ecd.RandEncode(wData.w[i])
		wData.wEcdNTT[i] = p.polyEval.NTT(wData.wEcd[i])

		comPolys[i] = wData.wEcd[i].Coeffs[:p.ctx.rank+1]
		coms[i], opens[i] = p.polyProver.Commit(comPolys[i])

		coms[i].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracleBuf.Reset()
	}

	roundComIdx := p.ctx.wCnt

	var linCheckMask *bigpoly.Poly[E]
	var linCheckMaskSum E
	if p.ctx.HasLinearCheck() {
		linCheckMask, linCheckMaskSum = p.sumCheckMask(2 * p.ctx.rank)

		comPolys[roundComIdx] = linCheckMask.Coeffs[:2*p.ctx.rank]
		coms[roundComIdx], opens[roundComIdx] = p.polyProver.Commit(comPolys[roundComIdx])

		coms[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracle.Bind("arithBatchConst", linCheckMaskSum.Marshal())
		oracleBuf.Reset()

		roundComIdx++
	}

	var sumCheckMask *bigpoly.Poly[E]
	var sumCheckMaskSum E
	if p.ctx.HasSumCheck() {
		sumCheckMask, sumCheckMaskSum = p.sumCheckMask(p.ctx.sumCheckMaxRank)

		comPolys[roundComIdx] = sumCheckMask.Coeffs[:p.ctx.sumCheckMaxRank]
		coms[roundComIdx], opens[roundComIdx] = p.polyProver.Commit(comPolys[roundComIdx])

		coms[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("arithBatchConst", oracleBuf.Bytes())
		oracle.Bind("arithBatchConst", sumCheckMaskSum.Marshal())
		oracleBuf.Reset()

		roundComIdx++
	}

	arithBatchConstBytes, err := oracle.ComputeChallenge("arithBatchConst")
	if err != nil {
		return nil, err
	}

	if p.ctx.HasArithmeticCheck() {
		batchConst := z.New().SetBytes(arithBatchConstBytes)

		quo := p.arithCheck(batchConst, wData)

		comPolys[roundComIdx] = quo
		coms[roundComIdx], opens[roundComIdx] = p.polyProver.Commit(quo)

		coms[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		roundComIdx++
	}

	linCheckBatchConstBytes, err := oracle.ComputeChallenge("linCheckBatchConst")
	if err != nil {
		return nil, err
	}

	linCheckConstBytes, err := oracle.ComputeChallenge("linCheckConst")
	if err != nil {
		return nil, err
	}

	if p.ctx.HasLinearCheck() {
		batchConst := z.New().SetBytes(linCheckBatchConstBytes)
		linCheckConst := z.New().SetBytes(linCheckConstBytes)

		quo, remLo, remHi := p.linCheck(batchConst, linCheckConst, linCheckMask, wData)

		comPolys[roundComIdx] = quo
		coms[roundComIdx], opens[roundComIdx] = p.polyProver.Commit(quo)

		coms[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		comPolys[roundComIdx+1] = remLo
		coms[roundComIdx+1], opens[roundComIdx+1] = p.polyProver.Commit(remLo)

		coms[roundComIdx+1].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		comPolys[roundComIdx+2] = remHi
		coms[roundComIdx+2], opens[roundComIdx+2] = p.polyProver.Commit(remHi)

		coms[roundComIdx+2].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		roundComIdx += 3
	}

	sumCheckBatchConstBytes, err := oracle.ComputeChallenge("sumCheckBatchConst")
	if err != nil {
		return nil, err
	}

	if p.ctx.HasSumCheck() {
		batchConst := z.New().SetBytes(sumCheckBatchConstBytes)

		quo, remLo, remHi := p.sumCheck(batchConst, sumCheckMask, wData)

		comPolys[roundComIdx] = quo
		coms[roundComIdx], opens[roundComIdx] = p.polyProver.Commit(quo)

		coms[roundComIdx].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		comPolys[roundComIdx+1] = remLo
		coms[roundComIdx+1], opens[roundComIdx+1] = p.polyProver.Commit(remLo)

		coms[roundComIdx+1].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		comPolys[roundComIdx+2] = remHi
		coms[roundComIdx+2], opens[roundComIdx+2] = p.polyProver.Commit(remHi)

		coms[roundComIdx+2].WriteRawTo(&oracleBuf)
		oracle.Bind("evalPoint", oracleBuf.Bytes())
		oracleBuf.Reset()

		roundComIdx += 3
	}

	evalPointBytes, err := oracle.ComputeChallenge("evalPoint")
	if err != nil {
		return nil, err
	}
	evalPoint := z.New().SetBytes(evalPointBytes)

	evals, evalProof := p.polyProver.Evaluate(evalPoint, comPolys, coms, opens)

	return &Proof[E]{
		Witness: coms,

		LinCheckMaskSum: linCheckMaskSum,
		SumCheckMaskSum: sumCheckMaskSum,

		Evals:     evals,
		EvalProof: evalProof,
	}, nil
}

func (p *Prover[E]) evalCircuit(batchConst E, constraints []ArithmeticConstraint[E], wData witnessData[E]) *bigpoly.Poly[E] {
	pOut := p.polyEval.NewPoly(true)

	eval := p.polyEval.NewPoly(true)
	term := p.polyEval.NewPoly(true)
	for _, c := range constraints {
		eval.Clear()
		for i := range c.witness {
			for j := range p.polyEval.Rank() {
				term.Coeffs[j].Set(c.coeffs[i])
			}
			if c.hasCoeffPublicWitness[i] {
				p.polyEval.MulTo(term, term, wData.pwEcdNTT[c.coeffsPublicWitness[i]])
			}
			for j := range c.witness[i] {
				p.polyEval.MulTo(term, term, wData.wEcdNTT[c.witness[i][j]])
			}
			p.polyEval.AddTo(eval, eval, term)
		}
		p.polyEval.ScalarMulTo(eval, eval, batchConst)
		p.polyEval.AddTo(pOut, pOut, eval)
	}

	return pOut
}

func (p *Prover[E]) sumCheckMask(maskRank int) (*bigpoly.Poly[E], E) {
	var z E

	mask := p.polyEval.NewPoly(false)
	for i := range p.ctx.rank {
		mask.Coeffs[i].MustSetRandom()
	}

	maskSum := z.New().Set(mask.Coeffs[0])

	for i := p.ctx.rank; i < maskRank; i++ {
		mask.Coeffs[i].MustSetRandom()
		mask.Coeffs[i-p.ctx.rank].Sub(mask.Coeffs[i-p.ctx.rank], mask.Coeffs[i])
	}

	return mask, maskSum
}

func (p *Prover[E]) arithCheck(batchConst E, wData witnessData[E]) (quo []E) {
	eval := p.evalCircuit(batchConst, p.ctx.arithConstraints, wData)
	p.polyEval.InvNTTTo(eval, eval)
	quoPoly, _ := p.polyEval.QuoRemByVanishing(eval, p.ctx.rank)
	return quoPoly.Coeffs[:p.ctx.arithCheckMaxRank-p.ctx.rank]
}

func (p *Prover[E]) linCheck(batchConst, linCheckConst E, linCheckMask *bigpoly.Poly[E], wData witnessData[E]) (quo, remLo, remHi []E) {
	var z E

	linCheckVec := make([]E, p.ctx.rank)
	linCheckVec[0] = z.New().SetUint64(1)
	for i := 1; i < p.ctx.rank; i++ {
		linCheckVec[i] = z.New().Mul(linCheckVec[i-1], linCheckConst)
	}

	linCheckVecTr := make([]E, p.ctx.rank)
	for i := range linCheckVecTr {
		linCheckVecTr[i] = z.New()
	}

	linCheckEcd := p.ecd.Encode(linCheckVec)
	p.polyEval.NTTTo(linCheckEcd, linCheckEcd)

	linCheckEcdTr := p.polyEval.NewPoly(false)

	eval := p.polyEval.NewPoly(true)
	term := p.polyEval.NewPoly(true)
	for _, tr := range p.ctx.linTransformers {
		tr.TransposeTo(linCheckVecTr, linCheckVec)
		p.ecd.EncodeTo(linCheckEcdTr, linCheckVecTr)
		p.polyEval.NTTTo(linCheckEcdTr, linCheckEcdTr)
		for _, wIDs := range p.ctx.linCheckConstraints[tr] {
			wOut, wIn := wData.wEcdNTT[wIDs[0]], wData.wEcdNTT[wIDs[1]]
			p.polyEval.MulTo(term, linCheckEcdTr, wIn)
			p.polyEval.MulSubTo(term, linCheckEcd, wOut)
			p.polyEval.ScalarMulTo(eval, eval, batchConst)
			p.polyEval.AddTo(eval, eval, term)
		}
	}
	p.polyEval.ScalarMulTo(eval, eval, batchConst)
	p.polyEval.InvNTTTo(eval, eval)
	p.polyEval.AddTo(eval, eval, linCheckMask)

	quoPoly, remPoly := p.polyEval.QuoRemByVanishing(eval, p.ctx.rank)

	remLo = make([]E, p.ctx.rank-1)
	for i := 0; i < p.ctx.rank-1; i++ {
		remLo[i] = z.New().Set(remPoly.Coeffs[i+1])
	}

	remHi = make([]E, p.JindoParams.Rank())
	for i := 0; i < p.JindoParams.Rank()-(p.ctx.rank-1); i++ {
		remHi[i] = z.New()
	}
	for i, ii := 0, p.JindoParams.Rank()-(p.ctx.rank-1); i < p.ctx.rank-1; i, ii = i+1, ii+1 {
		remHi[ii] = z.New().Set(remLo[i])
	}

	return quoPoly.Coeffs[:p.ctx.rank], remLo, remHi
}

func (p *Prover[E]) sumCheck(batchConst E, sumCheckMask *bigpoly.Poly[E], wData witnessData[E]) (quo, remLo, remHi []E) {
	var z E

	eval := p.evalCircuit(batchConst, p.ctx.sumCheckConstraints, wData)
	p.polyEval.ScalarMulTo(eval, eval, batchConst)
	p.polyEval.InvNTTTo(eval, eval)
	p.polyEval.AddTo(eval, eval, sumCheckMask)

	quoPoly, remPoly := p.polyEval.QuoRemByVanishing(eval, p.ctx.rank)

	remLo = make([]E, p.ctx.rank-1)
	for i := 0; i < p.ctx.rank-1; i++ {
		remLo[i] = z.New().Set(remPoly.Coeffs[i+1])
	}

	remHi = make([]E, p.JindoParams.Rank())
	for i := 0; i < p.JindoParams.Rank()-(p.ctx.rank-1); i++ {
		remHi[i] = z.New()
	}
	for i, ii := 0, p.JindoParams.Rank()-(p.ctx.rank-1); i < p.ctx.rank-1; i, ii = i+1, ii+1 {
		remHi[ii] = z.New().Set(remLo[i])
	}

	return quoPoly.Coeffs[:p.ctx.sumCheckMaxRank-p.ctx.rank], remLo, remHi
}
