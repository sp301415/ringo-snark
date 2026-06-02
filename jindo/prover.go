package jindo

import (
	"bytes"
	"math"
	"math/big"
	"sync"

	"golang.org/x/crypto/sha3"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

// Prover is a Jindo prover.
type Prover[E bignum.Uint[E]] struct {
	params Parameters[E]
	ecd    *Encoder[E]
	rnsOut *RNSReconstructor[E]

	inCut  *crt.Pow2Cutter
	outCut *crt.Pow2Cutter

	ecdAmb     *Encoder[E]
	embQToQAmb *crt.Embedder

	maskStdDevQuo *big.Float

	ck *CommitKey

	uniformSampler *csprng.UniformSampler
	roundedSampler *csprng.RoundedGaussianSampler

	pool     *sync.Pool
	poolS    *sync.Pool
	poolAmb  *sync.Pool
	poolAmbS *sync.Pool
	poolOut  *sync.Pool
	poolOutS *sync.Pool
	pool64   *sync.Pool
}

// NewProver creates a new [Prover].
func NewProver[E bignum.Uint[E]](params Parameters[E], crs []byte) *Prover[E] {
	stdDev := new(big.Float).SetFloat64(params.maskStdDev)
	stdDev.Mul(stdDev, stdDev)
	stdDev.Mul(stdDev, big.NewFloat(2))

	return &Prover[E]{
		params: params,
		ecd:    NewEncoder(params.op, params.ecd),
		rnsOut: NewRNSReconstructor[E](params.opOut),

		inCut:  crt.NewPow2Cutter(params.op.Rank(), params.opOut.Modulus(), params.op.Modulus(), int(params.logInCutOff)),
		outCut: crt.NewPow2Cutter(params.opOut.Rank(), params.opOut.Modulus(), params.opOut.Modulus(), int(params.logOutCutOff)),

		ecdAmb:     NewEncoder(params.opAmb, params.ecd),
		embQToQAmb: crt.NewEmbedder(params.op.Rank(), params.opAmb.Modulus(), params.op.Modulus()),

		maskStdDevQuo: stdDev,

		ck: NewCommitKey(params, crs),

		uniformSampler: csprng.NewUniformSampler(),
		roundedSampler: csprng.NewRoundedGaussianSampler(),

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
		poolAmb: &sync.Pool{
			New: func() any {
				return params.opAmb.NewPoly()
			},
		},
		poolAmbS: &sync.Pool{
			New: func() any {
				return (*crt.ShoupElement)(params.opAmb.NewNTTPoly())
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
	}
}

// Commit commits v.
// Panics if len(v) > params.rank.
// Otherwise, it pads zero.
func (p *Prover[E]) Commit(v []E) (*Commitment, *Opening[E]) {
	com := NewCommitment(p.params)
	open := NewOpening(p.params)

	p.CommitTo(com, open, v)

	return com, open
}

// CommitTo commits v to com and open.
// Panics if len(v) > params.rank.
// Otherwise, it pads zero.
func (p *Prover[E]) CommitTo(com *Commitment, open *Opening[E], v []E) {
	if len(v) > p.params.rank {
		panic("len(v) > params.rank")
	}

	pRawPtr := p.pool64.Get().(*[]uint64)
	pRaw := *pRawPtr
	defer p.pool64.Put(pRawPtr)

	for t := range p.params.split {
		for i := range p.params.cols {
			for j := range p.params.op.Rank() {
				pRaw[j] = p.uniformSampler.SampleN(p.params.ecd.base)
			}

			p.ecd.DecodeRawTo(open.Blinder[t][i*p.params.slots:(i+1)*p.params.slots], pRaw)

			for l, ql := range p.params.op.Modulus() {
				divHi, _ := ql.Div()
				vec.SMulScalarTo(open.Encode[t][i][p.params.rows].Coeffs[l], pRaw, 1, divHi, ql)
			}

			open.Encode[t][i][p.params.rows].IsNTT = false
			p.params.op.FwdNTTTo(open.Encode[t][i][p.params.rows], open.Encode[t][i][p.params.rows])
		}
	}

	for t := range p.params.split {
		for i := range p.params.cols {
			p.commitColTo(t, i, open, v)
		}
	}

	for t := range p.params.split {
		p.outerCommitTo(com.Value[t], open.InCommit[t])
	}
}

// commitColTo commits the t-th split and i-th column.
func (p *Prover[E]) commitColTo(t, i int, open *Opening[E], v []E) {
	pRawPtr := p.pool64.Get().(*[]uint64)
	pRaw := *pRawPtr
	defer p.pool64.Put(pRawPtr)

	rowStart := i * p.params.slots
	rowEnd := (i + 1) * p.params.slots

	for j := range p.params.rows {
		idxStart := (t * p.params.rows * p.params.cols * p.params.slots) + (j * p.params.cols * p.params.slots) + rowStart
		idxEnd := (t * p.params.rows * p.params.cols * p.params.slots) + (j * p.params.cols * p.params.slots) + rowEnd
		if idxStart > len(v) {
			break
		}

		p.ecdAmb.EncodeRawTo(pRaw, v[idxStart:min(idxEnd, len(v))])

		open.Encode[t][i][j].IsNTT = false
		for l, ql := range p.params.op.Modulus() {
			divHi, _ := ql.Div()
			vec.SMulScalarTo(open.Encode[t][i][j].Coeffs[l], pRaw, 1, divHi, ql)
		}
		p.params.op.FwdNTTTo(open.Encode[t][i][j], open.Encode[t][i][j])
	}

	for j := range p.params.inMSISRank + p.params.mlweRank {
		for k := range p.params.op.Rank() {
			pRaw[k] = p.uniformSampler.SampleN(2*p.params.ecd.base) - p.params.ecd.base
		}

		for l, ql := range p.params.op.Modulus() {
			vec.AddScalarTo(open.MLWE[t][i][j].Coeffs[l], pRaw, ql.Value(), nil)
			divHi, _ := ql.Div()
			vec.SMulScalarTo(open.MLWE[t][i][j].Coeffs[l], open.MLWE[t][i][j].Coeffs[l], 1, divHi, ql)
		}

		open.MLWE[t][i][j].IsNTT = false
		p.params.op.FwdNTTTo(open.MLWE[t][i][j], open.MLWE[t][i][j])
	}

	p.innerCommitTo(i, open.InCommit[t], open.Encode[t][i], open.MLWE[t][i])
}

// innerCommitTo computes the inner commitment.
func (p *Prover[E]) innerCommitTo(i int, inCom, ecd, MLWE []*crt.Element) {
	inComModIn := p.pool.Get().(*crt.Element)
	defer p.pool.Put(inComModIn)

	for j := range p.params.inMSISRank {
		p.params.op.SMulTo(inComModIn, ecd[0], p.ck.In[j][0], p.ck.InS[j][0])
		for k := range p.params.rows {
			p.params.op.SMulAddTo(inComModIn, ecd[k+1], p.ck.In[j][1+k], p.ck.InS[j][1+k])
		}
		for k := range p.params.mlweRank {
			p.params.op.SMulAddTo(inComModIn, MLWE[k], p.ck.MLWE[j][k], p.ck.MLWES[j][k])
		}
		p.params.op.AddTo(inComModIn, inComModIn, MLWE[p.params.mlweRank+j])

		p.params.op.InvNTTTo(inComModIn, inComModIn)
		inCom[i*p.params.inMSISRank+j].IsNTT = false
		p.inCut.CutTo(inCom[i*p.params.inMSISRank+j], inComModIn)
		p.params.opOut.FwdNTTTo(inCom[i*p.params.inMSISRank+j], inCom[i*p.params.inMSISRank+j])
	}
}

// outerCommitTo computes the outer commitment.
func (p *Prover[E]) outerCommitTo(com []*crt.Element, inCom []*crt.Element) {
	for i := range p.params.outMSISRank {
		p.params.opOut.SMulTo(com[i], inCom[0], p.ck.Out[i][0], p.ck.OutS[i][0])
		for j := range p.params.cols*p.params.inMSISRank - 1 {
			p.params.opOut.SMulAddTo(com[i], inCom[1+j], p.ck.Out[i][1+j], p.ck.OutS[i][1+j])
		}

		p.params.opOut.InvNTTTo(com[i], com[i])
		p.outCut.CutTo(com[i], com[i])
		p.params.opOut.FwdNTTTo(com[i], com[i])
	}
}

// Evaluate batch evaluates v at x using batch randomness batch and returns the result with proof.
func (p *Prover[E]) Evaluate(x E, y []E, com []*Commitment, open []*Opening[E]) *Proof[E] {
	pf := NewProof(p.params)
	p.EvaluateTo(pf, x, y, com, open)
	return pf
}

// Evaluate batch evaluates v at x using batch randomness batch and returns the result with proof.
func (p *Prover[E]) EvaluateTo(pf *Proof[E], x E, y []E, com []*Commitment, open []*Opening[E]) {
	qLen := len(p.params.op.Modulus())

	var z E

	oracle := sha3.NewShake128()
	oracleBuf := new(bytes.Buffer)

	bufE := make([]uint64, z.Limb())

	mulE := p.ecd.poolE.Get().(E)
	defer p.ecd.poolE.Put(mulE)

	tmpE := p.ecd.poolE.Get().(E)
	defer p.ecd.poolE.Put(tmpE)

	right0Skip := bignum.Exp(x, uint64(p.params.rows*p.params.cols*p.params.slots))
	for i := range p.params.batch {
		pf.BlindEvals[i].SetUint64(0)
		for j := p.params.split - 1; j >= 0; j-- {
			pf.BlindEvals[i].Mul(pf.BlindEvals[i], right0Skip)
			(&bigpoly.Poly[E]{Coeffs: open[i].Blinder[j], IsNTT: false}).EvaluateTo(tmpE, x)
			pf.BlindEvals[i].Add(pf.BlindEvals[i], tmpE)
		}
	}

	p.ck.WriteRawTo(oracleBuf)
	for i := range p.params.batch {
		com[i].WriteToBuf(oracleBuf)
	}
	writeE(oracleBuf, bufE, []E{x})
	writeE(oracleBuf, bufE, y)
	writeE(oracleBuf, bufE, pf.BlindEvals)

	oracle.Write(oracleBuf.Bytes())

	blindOracle := oracle.Clone()

	blindRandRawPtr := p.pool64.Get().(*[]uint64)
	blindRandRaw := *blindRandRawPtr
	defer p.pool64.Put(blindRandRawPtr)

	blindRandE := p.ecd.poolE.Get().(E)
	defer p.ecd.poolE.Put(blindRandE)

	clear(blindRandRaw)
	for i := 0; i < p.params.ecd.exp; i++ {
		blindRandRaw[i*p.params.slots] = sampleN(blindOracle, p.params.ecd.base)
	}
	p.ecd.DecodeConstRawTo(blindRandE, blindRandRaw)

	blindRandAmb := p.poolAmb.Get().(*crt.Element)
	defer p.poolAmb.Put(blindRandAmb)
	blindRandAmbS := p.poolAmbS.Get().(*crt.ShoupElement)
	defer p.poolAmbS.Put(blindRandAmbS)

	for l, ql := range p.params.opAmb.Modulus() {
		vec.ReduceTo(blindRandAmb.Coeffs[l], blindRandRaw, ql)
	}
	blindRandAmb.IsNTT = false
	p.params.opAmb.FwdNTTTo(blindRandAmb, blindRandAmb)
	p.params.opAmb.SFormTo(blindRandAmbS, blindRandAmb)

	blindRand := &crt.Element{
		Coeffs: blindRandAmb.Coeffs[:qLen],
		IsNTT:  true,
	}
	blindRandS := &crt.ShoupElement{
		Coeffs: blindRandAmbS.Coeffs[:qLen],
		IsNTT:  true,
	}

	mulE.SetUint64(1)
	leftSkip := bignum.Exp(x, uint64(p.params.slots*p.params.cols))
	left := make([]*crt.Element, p.params.rows)
	leftS := make([]*crt.ShoupElement, p.params.rows)
	leftAmb := make([]*crt.Element, p.params.rows)
	leftAmbS := make([]*crt.ShoupElement, p.params.rows)
	for i := range p.params.rows {
		leftAmb[i] = p.poolAmb.Get().(*crt.Element)
		p.ecdAmb.EncodeTo(leftAmb[i], []E{mulE})

		leftAmbS[i] = p.poolAmbS.Get().(*crt.ShoupElement)
		p.params.opAmb.SFormTo(leftAmbS[i], leftAmb[i])

		left[i] = &crt.Element{
			Coeffs: leftAmb[i].Coeffs[:len(p.params.op.Modulus())],
			IsNTT:  true,
		}
		leftS[i] = &crt.ShoupElement{
			Coeffs: leftAmbS[i].Coeffs[:len(p.params.op.Modulus())],
			IsNTT:  true,
		}

		mulE.Mul(mulE, leftSkip)
	}

	mulE.SetUint64(1)
	right1Skip := bignum.Exp(x, uint64(p.params.slots))
	right1Amb := make([]*crt.Element, p.params.cols)
	right1AmbS := make([]*crt.ShoupElement, p.params.cols)
	for i := range p.params.cols {
		right1Amb[i] = p.poolAmb.Get().(*crt.Element)
		p.ecdAmb.EncodeTo(right1Amb[i], []E{mulE})

		right1AmbS[i] = p.poolAmbS.Get().(*crt.ShoupElement)
		p.params.opAmb.SFormTo(right1AmbS[i], right1Amb[i])

		mulE.Mul(mulE, right1Skip)
	}

	nttAmb := p.params.opAmb.Transformer()
	splitEvalLeft := p.pool.Get().(*crt.Element)
	splitEvalLeftInvNTT := p.pool.Get().(*crt.Element)
	splitEvalLeftAmb := p.poolAmb.Get().(*crt.Element)
	splitEvalAmb := p.poolAmb.Get().(*crt.Element)
	for i := range p.params.batch {
		for j := range p.params.split {
			splitEvalAmb.Clear()
			for k := range p.params.cols {
				splitEvalLeft.Clear()
				for l := range p.params.rows {
					p.params.op.SMulAddTo(splitEvalLeft, open[i].Encode[j][k][l], left[l], leftS[l])
				}
				p.params.op.SMulAddTo(splitEvalLeft, open[i].Encode[j][k][p.params.rows], blindRand, blindRandS)

				p.params.op.InvNTTTo(splitEvalLeftInvNTT, splitEvalLeft)
				p.embQToQAmb.EmbedTo(splitEvalLeftAmb, splitEvalLeftInvNTT)
				for l := range p.params.op.Modulus() {
					copy(splitEvalLeftAmb.Coeffs[l], splitEvalLeft.Coeffs[l])
				}
				for l := len(p.params.op.Modulus()); l < len(p.params.opAmb.Modulus()); l++ {
					nttAmb[l].ForwardTo(splitEvalLeftAmb.Coeffs[l], splitEvalLeftAmb.Coeffs[l])
				}
				splitEvalLeftAmb.IsNTT = true

				p.params.opAmb.SMulAddTo(splitEvalAmb, splitEvalLeftAmb, right1Amb[k], right1AmbS[k])
			}
			p.params.opAmb.InvNTTTo(splitEvalAmb, splitEvalAmb)
			p.ecdAmb.DecodeTo(pf.SplitEvals[i][j], splitEvalAmb)
		}
	}

	alphaRaw := make([]*[]uint64, p.params.split*p.params.batch)
	alpha := make([]*crt.Element, p.params.split*p.params.batch)
	alphaS := make([]*crt.ShoupElement, p.params.split*p.params.batch)
	alphaOut := make([]*crt.Element, p.params.split*p.params.batch)
	alphaOutS := make([]*crt.ShoupElement, p.params.split*p.params.batch)
	for i := range p.params.split * p.params.batch {
		alphaRaw[i] = p.pool64.Get().(*[]uint64)

		alpha[i] = p.pool.Get().(*crt.Element)
		alphaS[i] = p.poolS.Get().(*crt.ShoupElement)

		alphaOut[i] = p.poolOut.Get().(*crt.Element)
		alphaOutS[i] = p.poolOutS.Get().(*crt.ShoupElement)
	}

	defer func() {
		for i := range p.params.split * p.params.batch {
			p.pool64.Put(alphaRaw[i])

			p.pool.Put(alpha[i])
			p.poolS.Put(alphaS[i])

			p.poolOut.Put(alphaOut[i])
			p.poolOutS.Put(alphaOutS[i])
		}
	}()

	ecdBatch := make([][]*crt.Element, p.params.cols)
	ecdBatchAmb := make([][]*crt.Element, p.params.cols)
	ecdBatchAmbInvNTT := make([][]*crt.Element, p.params.cols)
	ecdBatchNoMask := make([][]*crt.Element, p.params.cols)
	for i := range p.params.cols {
		ecdBatch[i] = make([]*crt.Element, p.params.rows+1)
		ecdBatchAmb[i] = make([]*crt.Element, p.params.rows+1)
		ecdBatchAmbInvNTT[i] = make([]*crt.Element, p.params.rows+1)
		ecdBatchNoMask[i] = make([]*crt.Element, p.params.rows+1)
		for j := range p.params.rows + 1 {
			ecdBatchAmb[i][j] = p.poolAmb.Get().(*crt.Element)
			ecdBatch[i][j] = &crt.Element{
				Coeffs: ecdBatchAmb[i][j].Coeffs[:qLen],
			}
			ecdBatchAmbInvNTT[i][j] = p.poolAmb.Get().(*crt.Element)
			ecdBatchNoMask[i][j] = p.pool.Get().(*crt.Element)
		}
	}

	mlweBatch := make([][]*crt.Element, p.params.cols)
	mlweBatchAmb := make([][]*crt.Element, p.params.cols)
	mlweBatchAmbInvNTT := make([][]*crt.Element, p.params.cols)
	mlweBatchNoMask := make([][]*crt.Element, p.params.cols)
	for i := range p.params.cols {
		mlweBatch[i] = make([]*crt.Element, p.params.mlweRank+p.params.inMSISRank)
		mlweBatchAmb[i] = make([]*crt.Element, p.params.mlweRank+p.params.inMSISRank)
		mlweBatchAmbInvNTT[i] = make([]*crt.Element, p.params.mlweRank+p.params.inMSISRank)
		mlweBatchNoMask[i] = make([]*crt.Element, p.params.mlweRank+p.params.inMSISRank)
		for j := range p.params.mlweRank + p.params.inMSISRank {
			mlweBatchAmb[i][j] = p.poolAmb.Get().(*crt.Element)
			mlweBatch[i][j] = &crt.Element{
				Coeffs: mlweBatchAmb[i][j].Coeffs[:qLen],
			}
			mlweBatchAmbInvNTT[i][j] = p.poolAmb.Get().(*crt.Element)
			mlweBatchNoMask[i][j] = p.pool.Get().(*crt.Element)
		}
	}

	defer func() {
		for i := range p.params.cols {
			for j := range p.params.rows + 1 {
				p.poolAmb.Put(ecdBatchAmb[i][j])
				p.poolAmb.Put(ecdBatchAmbInvNTT[i][j])
				p.pool.Put(ecdBatchNoMask[i][j])
			}
		}

		for i := range p.params.cols {
			for j := range p.params.mlweRank + p.params.inMSISRank {
				p.poolAmb.Put(mlweBatchAmb[i][j])
				p.poolAmb.Put(mlweBatchAmbInvNTT[i][j])
				p.pool.Put(mlweBatchNoMask[i][j])
			}
		}
	}()

	var oracleRej sha3.ShakeHash
	for {
		oracleRej = oracle.Clone()

		for i := range p.params.cols {
			for j := range p.params.rows + 1 {
				ecdBatchAmbInvNTT[i][j].IsNTT = false
				for k := range p.params.op.Rank() {
					c := p.roundedSampler.Sample(0, p.params.maskStdDev)
					for l, ql := range p.params.opAmb.Modulus() {
						ecdBatchAmbInvNTT[i][j].Coeffs[l][k] = num.Reduce(c, ql)
					}
				}
				p.params.opAmb.FwdNTTTo(ecdBatchAmb[i][j], ecdBatchAmbInvNTT[i][j])
				ecdBatch[i][j].IsNTT = true
			}

			for j := range p.params.mlweRank + p.params.inMSISRank {
				mlweBatchAmbInvNTT[i][j].IsNTT = false
				for k := range p.params.op.Rank() {
					c := p.roundedSampler.Sample(0, p.params.maskStdDev)
					for l, ql := range p.params.opAmb.Modulus() {
						mlweBatchAmbInvNTT[i][j].Coeffs[l][k] = num.Reduce(c, ql)
					}
				}
				p.params.opAmb.FwdNTTTo(mlweBatchAmb[i][j], mlweBatchAmbInvNTT[i][j])
				mlweBatch[i][j].IsNTT = true
			}
		}

		splitEvalAmb.Clear()
		for k := range p.params.cols {
			splitEvalLeftAmb.Clear()
			for l := range p.params.rows {
				p.params.opAmb.SMulAddTo(splitEvalLeftAmb, ecdBatchAmb[k][l], leftAmb[l], leftAmbS[l])
			}
			p.params.opAmb.SMulAddTo(splitEvalLeftAmb, ecdBatchAmb[k][p.params.rows], blindRandAmb, blindRandAmbS)
			p.params.opAmb.SMulAddTo(splitEvalAmb, splitEvalLeftAmb, right1Amb[k], right1AmbS[k])
		}
		p.params.opAmb.InvNTTTo(splitEvalAmb, splitEvalAmb)
		p.ecdAmb.DecodeTo(pf.MaskSplitEval, splitEvalAmb)

		for i := range p.params.cols {
			p.innerCommitTo(i, pf.InCommit, ecdBatch[i], mlweBatch[i])
		}
		p.outerCommitTo(pf.MaskCom, pf.InCommit)

		oracleBuf.Reset()

		writeE(oracleBuf, bufE, []E{blindRandE})
		for i := range p.params.batch {
			for j := range p.params.split {
				writeE(oracleBuf, bufE, pf.SplitEvals[i][j])
			}
		}
		for i := range pf.MaskCom {
			pf.MaskCom[i].WriteToBuf(oracleBuf)
		}
		writeE(oracleBuf, bufE, pf.MaskSplitEval)

		oracleRej.Write(oracleBuf.Bytes())

		alphaOracle := oracleRej.Clone()

		for i := range p.params.split * p.params.batch {
			encodeChalRawTo(*alphaRaw[i], alphaOracle)

			for l, ql := range p.params.op.Modulus() {
				divHi, _ := ql.Div()
				vec.AddScalarTo(alpha[i].Coeffs[l], *alphaRaw[i], ql.Value(), nil)
				vec.SMulScalarTo(alpha[i].Coeffs[l], alpha[i].Coeffs[l], 1, divHi, ql)
			}
			alpha[i].IsNTT = false
			p.params.op.FwdNTTTo(alpha[i], alpha[i])
			p.params.op.SFormTo(alphaS[i], alpha[i])

			for l, ql := range p.params.opOut.Modulus() {
				divHi, _ := ql.Div()
				vec.AddScalarTo(alphaOut[i].Coeffs[l], *alphaRaw[i], ql.Value(), nil)
				vec.SMulScalarTo(alphaOut[i].Coeffs[l], alphaOut[i].Coeffs[l], 1, divHi, ql)
			}
			alphaOut[i].IsNTT = false
			p.params.opOut.FwdNTTTo(alphaOut[i], alphaOut[i])
			p.params.opOut.SFormTo(alphaOutS[i], alphaOut[i])
		}

		for k := range p.params.cols {
			for l := range p.params.rows + 1 {
				ecdBatchNoMask[k][l].Clear()
			}
			for l := range p.params.mlweRank + p.params.inMSISRank {
				mlweBatchNoMask[k][l].Clear()
			}
		}

		for i := range p.params.batch {
			for j := range p.params.split {
				for k := range p.params.cols {
					for l := range p.params.rows + 1 {
						p.params.op.SMulAddTo(ecdBatchNoMask[k][l], open[i].Encode[j][k][l], alpha[i*p.params.split+j], alphaS[i*p.params.split+j])
					}
				}

				for k := range p.params.cols {
					for l := range p.params.mlweRank + p.params.inMSISRank {
						p.params.op.SMulAddTo(mlweBatchNoMask[k][l], open[i].MLWE[j][k][l], alpha[i*p.params.split+j], alphaS[i*p.params.split+j])
					}
				}
			}
		}

		if !p.reject(ecdBatchAmbInvNTT, mlweBatchAmbInvNTT, ecdBatchNoMask, mlweBatchNoMask) {
			break
		}
	}

	for k := range p.params.cols {
		for l := range p.params.rows + 1 {
			p.params.op.AddTo(ecdBatch[k][l], ecdBatch[k][l], ecdBatchNoMask[k][l])
		}
	}

	for k := range p.params.cols {
		for l := range p.params.mlweRank + p.params.inMSISRank {
			p.params.op.AddTo(mlweBatch[k][l], mlweBatch[k][l], mlweBatchNoMask[k][l])
		}
	}

	oracle = oracleRej

	p.poolAmb.Put(splitEvalLeftAmb)
	p.pool.Put(splitEvalLeft)
	p.pool.Put(splitEvalLeftInvNTT)
	p.poolAmb.Put(splitEvalAmb)

	for i := range p.params.cols {
		p.poolAmb.Put(right1Amb[i])
		p.poolAmbS.Put(right1AmbS[i])
	}

	for i := range p.params.batch {
		for j := range p.params.split {
			for k := range p.params.cols * p.params.inMSISRank {
				p.params.opOut.SMulAddTo(pf.InCommit[k], open[i].InCommit[j][k], alphaOut[i*p.params.split+j], alphaOutS[i*p.params.split+j])
			}
		}
	}

	for i := range p.params.cols {
		p.params.op.SMulTo(pf.Partial[i], ecdBatch[i][p.params.rows], blindRand, blindRandS)
		for j := range p.params.rows {
			p.params.op.SMulAddTo(pf.Partial[i], ecdBatch[i][j], left[j], leftS[j])
		}
	}

	for i := range p.params.rows {
		p.poolAmb.Put(leftAmb[i])
		p.poolAmbS.Put(leftAmbS[i])
	}

	oracleBuf.Reset()

	for i := range alpha {
		write64(oracleBuf, *alphaRaw[i])
	}
	for i := range pf.Partial {
		pf.Partial[i].WriteToBuf(oracleBuf)
	}

	oracle.Write(oracleBuf.Bytes())

	chalOracle := oracle.Clone()

	chalRawPtr := p.pool64.Get().(*[]uint64)
	chalRaw := *chalRawPtr
	clear(chalRaw)

	chal := make([]*crt.Element, p.params.cols)
	chalS := make([]*crt.ShoupElement, p.params.cols)
	for i := range p.params.cols {
		encodeChalRawTo(chalRaw, chalOracle)

		chal[i] = p.pool.Get().(*crt.Element)
		for l, ql := range p.params.op.Modulus() {
			divHi, _ := ql.Div()
			vec.AddScalarTo(chal[i].Coeffs[l], chalRaw, ql.Value(), nil)
			vec.SMulScalarTo(chal[i].Coeffs[l], chal[i].Coeffs[l], 1, divHi, ql)
		}
		chal[i].IsNTT = false
		p.params.op.FwdNTTTo(chal[i], chal[i])

		chalS[i] = p.poolS.Get().(*crt.ShoupElement)
		p.params.op.SFormTo(chalS[i], chal[i])
	}

	defer p.pool64.Put(chalRawPtr)
	defer func() {
		for i := range p.params.cols {
			p.pool.Put(chal[i])
			p.poolS.Put(chalS[i])
		}
	}()

	for i := range p.params.rows + 1 {
		p.params.op.SMulTo(pf.Encode[i], ecdBatch[0][i], chal[0], chalS[0])
		for j := range p.params.cols - 1 {
			p.params.op.SMulAddTo(pf.Encode[i], ecdBatch[j+1][i], chal[j+1], chalS[j+1])
		}
	}

	for i := range p.params.mlweRank + p.params.inMSISRank {
		p.params.op.SMulTo(pf.MLWE[i], mlweBatch[0][i], chal[0], chalS[0])
		for j := range p.params.cols - 1 {
			p.params.op.SMulAddTo(pf.MLWE[i], mlweBatch[j+1][i], chal[j+1], chalS[j+1])
		}
	}
}

func (p *Prover[E]) reject(ecdMaskInvNTT, mlweMaskInvNTT, ecdBatchNoMask, mlweBatchNoMask [][]*crt.Element) bool {
	eRej := p.poolAmb.Get().(*crt.Element)
	defer p.poolAmb.Put(eRej)

	eInvNTT := p.pool.Get().(*crt.Element)
	defer p.pool.Put(eInvNTT)

	eLeft := p.poolAmb.Get().(*crt.Element)
	defer p.poolAmb.Put(eLeft)

	eRight := p.poolAmb.Get().(*crt.Element)
	defer p.poolAmb.Put(eRight)

	eRej.Clear()
	for i := range p.params.cols {
		for j := range p.params.rows + 1 {
			p.params.op.InvNTTTo(eInvNTT, ecdBatchNoMask[i][j])
			p.embQToQAmb.EmbedTo(eLeft, eInvNTT)

			p.params.opAmb.NegTo(eRight, eLeft)

			p.params.opAmb.AddTo(eLeft, eLeft, ecdMaskInvNTT[i][j])
			p.params.opAmb.AddTo(eLeft, eLeft, ecdMaskInvNTT[i][j])

			for l, ql := range p.params.opAmb.Modulus() {
				vec.MulAddTo(eRej.Coeffs[l], eLeft.Coeffs[l], eRight.Coeffs[l], ql)
			}
		}

		for j := range p.params.mlweRank + p.params.inMSISRank {
			p.params.op.InvNTTTo(eInvNTT, mlweBatchNoMask[i][j])
			p.embQToQAmb.EmbedTo(eLeft, eInvNTT)

			p.params.opAmb.NegTo(eRight, eLeft)

			p.params.opAmb.AddTo(eLeft, eLeft, mlweMaskInvNTT[i][j])
			p.params.opAmb.AddTo(eLeft, eLeft, mlweMaskInvNTT[i][j])

			for l, ql := range p.params.opAmb.Modulus() {
				vec.MulAddTo(eRej.Coeffs[l], eLeft.Coeffs[l], eRight.Coeffs[l], ql)
			}
		}
	}

	for l, ql := range p.params.opAmb.Modulus() {
		for i := 1; i < p.params.op.Rank(); i++ {
			eRej.Coeffs[l][0] = num.Add(eRej.Coeffs[l][0], eRej.Coeffs[l][i], ql)
		}
	}

	for i := range p.ecdAmb.rns.modInSorted {
		eRej.Coeffs[i][1] = eRej.Coeffs[p.ecdAmb.rns.modInMap[i]][0]
	}

	for i := 0; i < len(p.ecdAmb.rns.modInSorted); i++ {
		for j := i + 1; j < len(p.ecdAmb.rns.modInSorted); j++ {
			eRej.Coeffs[j][1] = num.Sub(eRej.Coeffs[j][1], eRej.Coeffs[i][1], p.ecdAmb.rns.modInSorted[j])
			eRej.Coeffs[j][1] = num.SMul(eRej.Coeffs[j][1], p.ecdAmb.rns.modInv[i][j-i-1], p.ecdAmb.rns.modInvS[i][j-i-1], p.ecdAmb.rns.modInSorted[j])
		}
	}

	pRejInt := p.ecdAmb.rns.poolBig.Get().(*big.Int)
	defer p.ecdAmb.rns.poolBig.Put(pRejInt)

	tmpInt := p.ecdAmb.rns.poolBig.Get().(*big.Int)
	defer p.ecdAmb.rns.poolBig.Put(tmpInt)

	pRejInt.SetUint64(eRej.Coeffs[0][1])
	for i := 1; i < len(p.ecdAmb.rns.modInSorted); i++ {
		tmpInt.SetUint64(eRej.Coeffs[i][1])
		tmpInt.Mul(tmpInt, p.ecdAmb.rns.baseBig[i])
		pRejInt.Add(pRejInt, tmpInt)
	}

	tmpInt.Rsh(p.ecdAmb.rns.qProd, 1)
	if pRejInt.Cmp(tmpInt) > 0 {
		pRejInt.Sub(pRejInt, p.ecdAmb.rns.qProd)
	}

	pRej := new(big.Float).SetInt(pRejInt)
	pRej.Quo(pRej, p.maskStdDevQuo)

	pRej64, _ := pRej.Float64()

	return p.uniformSampler.SampleFloat() > math.Exp(pRej64)/rejRate
}
