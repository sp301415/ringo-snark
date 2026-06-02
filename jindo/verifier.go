package jindo

import (
	"bytes"
	"math/big"
	"sync"

	"golang.org/x/crypto/sha3"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/vec"
)

// Verifier is a Jindo verifier.
type Verifier[E bignum.Uint[E]] struct {
	params     Parameters[E]
	ecd        *Encoder[E]
	rnsOut     *RNSReconstructor[E]
	embQOutToQ *crt.Embedder

	inCutOff  *crt.Element
	outCutOff *crt.Element

	ck *CommitKey

	pool      *sync.Pool
	poolS     *sync.Pool
	poolOut   *sync.Pool
	poolOutS  *sync.Pool
	pool64    *sync.Pool
	poolBigSq *sync.Pool
}

// NewVerifier creates a new [Verifier].
func NewVerifier[E bignum.Uint[E]](params Parameters[E], crs []byte) *Verifier[E] {
	inCutOffBig := big.NewInt(1)
	inCutOffBig.Lsh(inCutOffBig, uint(params.logInCutOff))
	inCutOff := crt.NewScalarFrom(inCutOffBig, params.op.Modulus())

	outCutOffBig := big.NewInt(1)
	outCutOffBig.Lsh(outCutOffBig, uint(params.logOutCutOff))
	outCutOff := crt.NewScalarFrom(outCutOffBig, params.opOut.Modulus())

	return &Verifier[E]{
		params:     params,
		ecd:        NewEncoder(params.op, params.ecd),
		rnsOut:     NewRNSReconstructor[E](params.opOut),
		embQOutToQ: crt.NewEmbedder(params.op.Rank(), params.op.Modulus(), params.opOut.Modulus()),

		inCutOff:  inCutOff,
		outCutOff: outCutOff,

		ck: NewCommitKey(params, crs),

		pool: &sync.Pool{
			New: func() any {
				return params.op.NewPoly()
			},
		},
		poolS: &sync.Pool{
			New: func() any {
				return (*crt.ShoupElement)(params.op.NewNTTPoly())
			},
		},
		poolOut: &sync.Pool{
			New: func() any {
				return params.opOut.NewPoly()
			},
		},
		poolOutS: &sync.Pool{
			New: func() any {
				return (*crt.ShoupElement)(params.opOut.NewNTTPoly())
			},
		},
		pool64: &sync.Pool{
			New: func() any {
				v := make([]uint64, params.op.Rank())
				return &v
			},
		},
		poolBigSq: &sync.Pool{
			New: func() any {
				b := make([]byte, (2*maxLogQ)/8)
				return new(big.Int).SetBytes(b)
			},
		},
	}
}

// Verify verifies the polynomial commitment.
func (v *Verifier[E]) Verify(x E, y []E, com []*Commitment, pf *Proof[E]) bool {
	if len(com) != v.params.batch {
		panic("len(v) != params.batch")
	}

	var z E

	oracle := sha3.NewShake128()
	oracleBuf := new(bytes.Buffer)

	bufE := make([]uint64, z.Limb())

	v.ck.WriteRawTo(oracleBuf)
	for i := range v.params.batch {
		com[i].WriteToBuf(oracleBuf)
	}
	writeE(oracleBuf, bufE, []E{x})
	writeE(oracleBuf, bufE, y)
	writeE(oracleBuf, bufE, pf.BlindEvals)

	oracle.Write(oracleBuf.Bytes())

	blindOracle := oracle.Clone()

	blindRandRawPtr := v.pool64.Get().(*[]uint64)
	blindRandRaw := *blindRandRawPtr
	defer v.pool64.Put(blindRandRawPtr)

	clear(blindRandRaw)
	for i := 0; i < v.params.ecd.exp; i++ {
		blindRandRaw[i*v.params.slots] = sampleN(blindOracle, v.params.ecd.base)
	}
	blindRandE := v.ecd.poolE.Get().(E)
	defer v.ecd.poolE.Put(blindRandE)

	v.ecd.DecodeConstRawTo(blindRandE, blindRandRaw)

	blindRand := v.pool.Get().(*crt.Element)
	defer v.pool.Put(blindRand)
	blindRandS := v.poolS.Get().(*crt.ShoupElement)
	defer v.poolS.Put(blindRandS)

	for l, ql := range v.params.op.Modulus() {
		vec.ReduceTo(blindRand.Coeffs[l], blindRandRaw, ql)
	}
	blindRand.IsNTT = false
	v.params.op.FwdNTTTo(blindRand, blindRand)
	v.params.op.SFormTo(blindRandS, blindRand)

	oracleBuf.Reset()

	writeE(oracleBuf, bufE, []E{blindRandE})
	for i := range v.params.batch {
		for j := range v.params.split {
			writeE(oracleBuf, bufE, pf.SplitEvals[i][j])
		}
	}
	for i := range pf.MaskCom {
		pf.MaskCom[i].WriteToBuf(oracleBuf)
	}
	writeE(oracleBuf, bufE, pf.MaskSplitEval)

	oracle.Write(oracleBuf.Bytes())

	alphaOracle := oracle.Clone()

	alphaRaw := make([]*[]uint64, v.params.split*v.params.batch)
	alpha := make([]*crt.Element, v.params.split*v.params.batch)
	alphaS := make([]*crt.ShoupElement, v.params.split*v.params.batch)
	alphaOut := make([]*crt.Element, v.params.split*v.params.batch)
	alphaOutS := make([]*crt.ShoupElement, v.params.split*v.params.batch)
	for i := range v.params.split * v.params.batch {
		alphaRaw[i] = v.pool64.Get().(*[]uint64)
		encodeChalRawTo(*alphaRaw[i], alphaOracle)

		alpha[i] = v.pool.Get().(*crt.Element)
		alphaS[i] = v.poolS.Get().(*crt.ShoupElement)
		for l, ql := range v.params.op.Modulus() {
			divHi, _ := ql.Div()
			vec.AddScalarTo(alpha[i].Coeffs[l], *alphaRaw[i], ql.Value(), nil)
			vec.SMulScalarTo(alpha[i].Coeffs[l], alpha[i].Coeffs[l], 1, divHi, ql)
		}
		alpha[i].IsNTT = false
		v.params.op.FwdNTTTo(alpha[i], alpha[i])
		v.params.op.SFormTo(alphaS[i], alpha[i])

		alphaOut[i] = v.poolOut.Get().(*crt.Element)
		alphaOutS[i] = v.poolOutS.Get().(*crt.ShoupElement)
		for l, ql := range v.params.opOut.Modulus() {
			divHi, _ := ql.Div()
			vec.AddScalarTo(alphaOut[i].Coeffs[l], *alphaRaw[i], ql.Value(), nil)
			vec.SMulScalarTo(alphaOut[i].Coeffs[l], alphaOut[i].Coeffs[l], 1, divHi, ql)
		}
		alphaOut[i].IsNTT = false
		v.params.opOut.FwdNTTTo(alphaOut[i], alphaOut[i])
		v.params.opOut.SFormTo(alphaOutS[i], alphaOut[i])
	}

	defer func() {
		for i := range alpha {
			v.pool64.Put(alphaRaw[i])
			v.pool.Put(alpha[i])
			v.poolS.Put(alphaS[i])
			v.poolOut.Put(alphaOut[i])
			v.poolOutS.Put(alphaOutS[i])
		}
	}()

	oracleBuf.Reset()

	for i := range alpha {
		write64(oracleBuf, *alphaRaw[i])
	}
	for i := range pf.Partial {
		pf.Partial[i].WriteToBuf(oracleBuf)
	}

	oracle.Write(oracleBuf.Bytes())

	chalOracle := oracle.Clone()

	chalRawPtr := v.pool64.Get().(*[]uint64)
	chalRaw := *chalRawPtr
	clear(chalRaw)

	chal := make([]*crt.Element, v.params.cols)
	chalS := make([]*crt.ShoupElement, v.params.cols)
	for i := 0; i < v.params.cols; i++ {
		encodeChalRawTo(chalRaw, chalOracle)

		chal[i] = v.pool.Get().(*crt.Element)
		for l, ql := range v.params.op.Modulus() {
			divHi, _ := ql.Div()
			vec.AddScalarTo(chal[i].Coeffs[l], chalRaw, ql.Value(), nil)
			vec.SMulScalarTo(chal[i].Coeffs[l], chal[i].Coeffs[l], 1, divHi, ql)
		}
		chal[i].IsNTT = false
		v.params.op.FwdNTTTo(chal[i], chal[i])

		chalS[i] = v.poolS.Get().(*crt.ShoupElement)
		v.params.op.SFormTo(chalS[i], chal[i])
	}

	defer v.pool64.Put(chalRawPtr)
	defer func() {
		for i := range chal {
			v.pool.Put(chal[i])
			v.poolS.Put(chalS[i])
		}
	}()

	pfInv := &Proof[E]{}

	pfInv.Partial = make([]*crt.Element, len(pf.Partial))
	for i := range pf.Partial {
		pfInv.Partial[i] = v.pool.Get().(*crt.Element)
		v.params.op.InvNTTTo(pfInv.Partial[i], pf.Partial[i])
	}

	pfInv.Encode = make([]*crt.Element, len(pf.Encode))
	for i := range pf.Encode {
		pfInv.Encode[i] = v.pool.Get().(*crt.Element)
		v.params.op.InvNTTTo(pfInv.Encode[i], pf.Encode[i])
	}

	pfInv.MLWE = make([]*crt.Element, len(pf.MLWE))
	for i := range pf.MLWE {
		pfInv.MLWE[i] = v.pool.Get().(*crt.Element)
		v.params.op.InvNTTTo(pfInv.MLWE[i], pf.MLWE[i])
	}

	pfInv.InCommit = make([]*crt.Element, len(pf.InCommit))
	for i := range pf.InCommit {
		pfInv.InCommit[i] = v.poolOut.Get().(*crt.Element)
		v.params.opOut.InvNTTTo(pfInv.InCommit[i], pf.InCommit[i])
	}

	defer func() {
		for i := range pfInv.Partial {
			v.pool.Put(pfInv.Partial[i])
		}

		for i := range pfInv.Encode {
			v.pool.Put(pfInv.Encode[i])
		}

		for i := range pfInv.MLWE {
			v.pool.Put(pfInv.MLWE[i])
		}

		for i := range pfInv.InCommit {
			v.poolOut.Put(pfInv.InCommit[i])
		}
	}()

	okOuter := v.verifyOuterCommitment(alphaOut, alphaOutS, com, pf, pfInv)
	okInner := v.verifyInnerCommitment(chal, chalS, pf, pfInv)
	okConsistency := v.verifyConsistency(x, chal, chalS, blindRand, blindRandS, pf)
	okEval := v.verifyEval(x, y, alpha, alphaS, blindRandE, pf, pfInv)

	return okOuter && okInner && okConsistency && okEval
}

// verifyOuterCommitment verfies the outer commitment.
func (v *Verifier[E]) verifyOuterCommitment(alpha []*crt.Element, alphaS []*crt.ShoupElement, com []*Commitment, pf, pfInv *Proof[E]) bool {
	inDcmpInv := append(pfInv.InCommit, make([]*crt.Element, v.params.outMSISRank)...)

	cutoff := inDcmpInv[v.params.cols*v.params.inMSISRank:]
	for i := range v.params.outMSISRank {
		cutoff[i] = v.poolOut.Get().(*crt.Element)
		cutoff[i].Clear()

		for j := range v.params.batch {
			for k := range v.params.split {
				v.params.opOut.SMulAddTo(cutoff[i], com[j].Value[k][i], alpha[j*v.params.split+k], alphaS[j*v.params.split+k])
			}
		}
		v.params.opOut.AddTo(cutoff[i], cutoff[i], pf.MaskCom[i])

		v.params.opOut.MulTo(cutoff[i], cutoff[i], v.outCutOff)

		for j := range v.params.cols * v.params.inMSISRank {
			v.params.opOut.SMulSubTo(cutoff[i], pf.InCommit[j], v.ck.Out[i][j], v.ck.OutS[i][j])
		}

		v.params.opOut.InvNTTTo(cutoff[i], cutoff[i])
	}

	defer func() {
		for i := range v.params.outMSISRank {
			v.poolOut.Put(cutoff[i])
		}
	}()

	return v.verifyNorm(v.rnsOut, inDcmpInv, v.params.outOpenTwoNm)
}

// verifyInnerCommitment verfies the inner commitment.
func (v *Verifier[E]) verifyInnerCommitment(chal []*crt.Element, chalS []*crt.ShoupElement, pf, pfInv *Proof[E]) bool {
	resInv := append(pfInv.Encode, pfInv.MLWE...)
	resInv = append(resInv, make([]*crt.Element, v.params.inMSISRank)...)

	inComQ := v.pool.Get().(*crt.Element)
	defer v.pool.Put(inComQ)
	cutoff := resInv[v.params.rows+1+v.params.mlweRank+v.params.inMSISRank:]
	for i := range v.params.inMSISRank {
		cutoff[i] = v.pool.Get().(*crt.Element)
		cutoff[i].Clear()

		for j := range v.params.cols {
			v.embQOutToQ.EmbedTo(inComQ, pfInv.InCommit[j*v.params.inMSISRank+i])
			v.params.op.FwdNTTTo(inComQ, inComQ)

			v.params.op.SMulAddTo(cutoff[i], inComQ, chal[j], chalS[j])
		}

		v.params.op.MulTo(cutoff[i], cutoff[i], v.inCutOff)

		for j := range v.params.rows + 1 {
			v.params.op.SMulSubTo(cutoff[i], pf.Encode[j], v.ck.In[i][j], v.ck.InS[i][j])
		}
		for j := range v.params.mlweRank {
			v.params.op.SMulSubTo(cutoff[i], pf.MLWE[j], v.ck.MLWE[i][j], v.ck.MLWES[i][j])
		}
		v.params.op.SubTo(cutoff[i], cutoff[i], pf.MLWE[v.params.mlweRank+i])

		v.params.op.InvNTTTo(cutoff[i], cutoff[i])
	}

	defer func() {
		for i := range v.params.inMSISRank {
			v.pool.Put(cutoff[i])
		}
	}()

	return v.verifyNorm(v.ecd.rns, resInv, v.params.resTwoNm)
}

// verifyConsistency verifies the consistency of the proof.
func (v *Verifier[E]) verifyConsistency(x E, chal []*crt.Element, chalS []*crt.ShoupElement, blindRand *crt.Element, blindRandS *crt.ShoupElement, pf *Proof[E]) bool {
	mulE := v.ecd.poolE.Get().(E)
	defer v.ecd.poolE.Put(mulE)

	left := v.pool.Get().(*crt.Element)
	defer v.pool.Put(left)
	leftS := v.poolS.Get().(*crt.ShoupElement)
	defer v.poolS.Put(leftS)

	test := v.pool.Get().(*crt.Element)
	test.Clear()
	defer v.pool.Put(test)

	mulE.SetUint64(1)
	leftSkip := bignum.Exp(x, uint64(v.params.slots*v.params.cols))
	for i := 0; i < v.params.rows; i++ {
		v.ecd.EncodeTo(left, []E{mulE})
		v.params.op.SFormTo(leftS, left)
		v.params.op.SMulAddTo(test, pf.Encode[i], left, leftS)
		mulE.Mul(mulE, leftSkip)
	}
	v.params.op.SMulAddTo(test, pf.Encode[v.params.rows], blindRand, blindRandS)

	for i := 0; i < v.params.cols; i++ {
		v.params.op.SMulSubTo(test, pf.Partial[i], chal[i], chalS[i])
	}

	for i := range test.Coeffs {
		for j := range test.Coeffs[i] {
			if test.Coeffs[i][j] != 0 {
				return false
			}
		}
	}

	return true
}

// verifyEval verifies the evaluation.
func (v *Verifier[E]) verifyEval(x E, y []E, alpha []*crt.Element, alphaS []*crt.ShoupElement, blindRandE E, pf, pfInv *Proof[E]) bool {
	right0Skip := bignum.Exp(x, uint64(v.params.rows*v.params.cols*v.params.slots))

	evalE := v.ecd.poolE.Get().(E)
	defer v.ecd.poolE.Put(evalE)
	mulE := v.ecd.poolE.Get().(E)
	defer v.ecd.poolE.Put(mulE)
	checkE := v.ecd.poolE.Get().(E)
	defer v.ecd.poolE.Put(checkE)

	for i := range v.params.batch {
		evalE.Set(y[i])
		mulE.Mul(blindRandE, pf.BlindEvals[i])
		evalE.Add(evalE, mulE)

		checkE.SetUint64(0)
		for j := v.params.split - 1; j >= 0; j-- {
			mulE.SetUint64(0)
			for k := v.params.slots - 1; k >= 0; k-- {
				mulE.Mul(mulE, x)
				mulE.Add(mulE, pf.SplitEvals[i][j][k])
			}
			checkE.Mul(checkE, right0Skip)
			checkE.Add(checkE, mulE)
		}

		if evalE.Cmp(checkE) != 0 {
			return false
		}
	}

	batchEvalE := make([]E, v.params.slots)
	batchCheckE := make([]E, v.params.slots)
	partialE := make([]E, v.params.slots)
	for i := range v.params.slots {
		batchEvalE[i] = v.ecd.poolE.Get().(E)
		batchCheckE[i] = v.ecd.poolE.Get().(E)
		partialE[i] = v.ecd.poolE.Get().(E)
	}

	defer func() {
		for i := range v.params.slots {
			v.ecd.poolE.Put(batchEvalE[i])
			v.ecd.poolE.Put(batchCheckE[i])
			v.ecd.poolE.Put(partialE[i])
		}
	}()

	splitEval := v.pool.Get().(*crt.Element)
	defer v.pool.Put(splitEval)
	batchEval := v.pool.Get().(*crt.Element)
	batchEval.Clear()
	defer v.pool.Put(batchEval)

	for i := range v.params.batch {
		for j := range v.params.split {
			v.ecd.EncodeTo(splitEval, pf.SplitEvals[i][j])
			v.params.op.SMulAddTo(batchEval, splitEval, alpha[i*v.params.split+j], alphaS[i*v.params.split+j])
		}
	}
	v.ecd.EncodeTo(splitEval, pf.MaskSplitEval)
	v.params.op.AddTo(batchEval, batchEval, splitEval)

	v.params.op.InvNTTTo(batchEval, batchEval)
	v.ecd.DecodeTo(batchEvalE, batchEval)

	for j := range v.params.slots {
		batchCheckE[j].SetUint64(0)
	}

	right1Pow := bignum.Exp(x, uint64(v.params.slots))
	for i := v.params.cols - 1; i >= 0; i-- {
		v.ecd.DecodeTo(partialE, pfInv.Partial[i])
		for j := range v.params.slots {
			batchCheckE[j].Mul(batchCheckE[j], right1Pow)
			batchCheckE[j].Add(batchCheckE[j], partialE[j])
		}
	}

	for i := range v.params.slots {
		if batchEvalE[i].Cmp(batchCheckE[i]) != 0 {
			return false
		}
	}

	return true
}

// verifyNorm checks the norm of the given polynomials.
func (v *Verifier[E]) verifyNorm(rns *RNSReconstructor[E], p []*crt.Element, nm float64) bool {
	nmSq := v.poolBigSq.Get().(*big.Int)
	nmSq.SetUint64(0)
	defer v.poolBigSq.Put(nmSq)

	sq := v.poolBigSq.Get().(*big.Int)
	defer v.poolBigSq.Put(sq)

	pBigPtr := v.ecd.poolBig.Get().(*[]*big.Int)
	pBig := *pBigPtr
	defer v.ecd.poolBig.Put(pBigPtr)

	for i := range p {
		rns.ReconstructTo(pBig, p[i])
		for j := 0; j < v.params.op.Rank(); j++ {
			sq.Mul(pBig[j], pBig[j])
			nmSq.Add(nmSq, sq)
		}
	}

	nmSq.Sqrt(nmSq)
	nmTest, _ := nmSq.Float64()

	return nmTest < nm
}
