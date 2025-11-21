package jindo

import (
	"math/big"
	"math/bits"

	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Encoder encodes large integer vector to small ring elements.
type Encoder[E num.Uint[E]] struct {
	params Parameters

	twinCDT *csprng.TwinCDTGaussianSampler
	cosac   *csprng.COSACSampler
	rounded *csprng.RoundedGaussianSampler

	rns *RNSReconstructor

	// deltaInv is a constnat used in randomized encoding.
	// Equals to [-1/p, -b/p, ..., -b^(r-1)/p].
	deltaInv []float64

	buf encoderBuffer[E]
}

// encoderBuffer is a buffer for [Encoder].
type encoderBuffer[E num.Uint[E]] struct {
	// coeff is a buffer for E.
	coeff []uint64
	// fpSample is a buffer for Gaussian samples.
	fpSample []float64
	// pSample is an embedding of fpSample.
	pSample ring.Poly
	// pSampleShift is a buffer for pSample * X^d.
	pSampleShift ring.Poly
	// coeffBig is a buffer for big.Int coefficients.
	coeffBig []*big.Int

	// baseE is a buffer for base in E.
	baseE E
	// coeffE is a buffer for coefficient in E.
	coeffE E
}

// NewEncoder creates a new [Encoder].
func NewEncoder[E num.Uint[E]](params Parameters) *Encoder[E] {
	pBig := new(big.Int).Exp(new(big.Int).SetUint64(params.ecd.base), new(big.Int).SetUint64(uint64(params.ecd.exp)), nil)
	bFloat := new(big.Float).SetPrec(uint(pBig.BitLen())).SetUint64(params.ecd.base)
	pBig.Add(pBig, big.NewInt(1))
	pFloat := new(big.Float).SetPrec(uint(pBig.BitLen())).SetInt(pBig)
	pFloatInv := new(big.Float).Quo(big.NewFloat(1), pFloat)
	pFloatInv.Neg(pFloatInv)

	deltaInv := make([]float64, params.ecd.exp)
	for i := 0; i < params.ecd.exp; i++ {
		deltaInv[i], _ = pFloatInv.Float64()
		pFloatInv.Mul(pFloatInv, bFloat)
	}

	return &Encoder[E]{
		params: params,

		twinCDT: csprng.NewTwinCDTGaussianSampler(params.ecdStdDev),
		cosac:   csprng.NewCOSACSampler(),
		rounded: csprng.NewRoundedGaussianSampler(),

		rns: NewRNSReconstructor(params.ringQ),

		deltaInv: deltaInv,

		buf: newEncoderBuffer[E](params.ringQ),
	}
}

// newEncoderBuffer creates a new [encoderBuffer].
func newEncoderBuffer[E num.Uint[E]](ringQ *ring.Ring) encoderBuffer[E] {
	var z E

	coeffBig := make([]*big.Int, ringQ.N())
	for i := range coeffBig {
		coeffBig[i] = new(big.Int).Set(ringQ.Modulus())
	}

	return encoderBuffer[E]{
		coeff:        make([]uint64, z.New().Limb()),
		fpSample:     make([]float64, ringQ.N()),
		pSample:      ringQ.NewPoly(),
		pSampleShift: ringQ.NewPoly(),
		coeffBig:     coeffBig,

		baseE:  z.New(),
		coeffE: z.New(),
	}
}

// divMod64 computes x = x / y and returns x mod y.
func divMod64(x []uint64, y uint64) uint64 {
	var r uint64
	for i := len(x) - 1; i >= 0; i-- {
		x[i], r = bits.Div64(r, x[i], y)
	}
	return r
}

// Encode returns an encoding of v.
func (e *Encoder[E]) Encode(v []E) ring.Poly {
	pOut := e.params.ringQ.NewPoly()
	e.EncodeTo(pOut, v)
	return pOut
}

// EncodeTo encodes v to pOut.
func (e *Encoder[E]) EncodeTo(pOut ring.Poly, v []E) {
	e.encodeTo(pOut, v)
	e.params.ringQ.MFormLazy(pOut, pOut)
	e.params.ringQ.NTT(pOut, pOut)
}

// encodeTo encodes v to pOut without NTT and MForm.
func (e *Encoder[E]) encodeTo(pOut ring.Poly, v []E) {
	if len(v) > e.params.slots {
		panic("EncodeTo: len(v) > slots")
	}

	for i := range v {
		v[i].Slice(e.buf.coeff)
		for j := 0; j < e.params.ecd.exp-1; j++ {
			r := divMod64(e.buf.coeff, e.params.ecd.base)
			for k := 0; k <= pOut.Level(); k++ {
				pOut.Coeffs[k][j*e.params.slots+i] = r
			}
		}
		r := e.buf.coeff[0]
		for k := 0; k <= pOut.Level(); k++ {
			pOut.Coeffs[k][(e.params.ecd.exp-1)*e.params.slots+i] = r
		}
	}

	for i := len(v); i < e.params.slots; i++ {
		for j := 0; j < e.params.ecd.exp; j++ {
			for k := 0; k <= pOut.Level(); k++ {
				pOut.Coeffs[k][j*e.params.slots+i] = 0
			}
		}
	}
}

// RandEncode returns an randomized encoding of v.
func (e *Encoder[E]) RandEncode(v []E) ring.Poly {
	pOut := e.params.ringQ.NewPoly()
	e.RandEncodeTo(pOut, v)
	return pOut
}

// RandEncodeTo randomized encodes v to pOut.
func (e *Encoder[E]) RandEncodeTo(pOut ring.Poly, v []E) {
	e.encodeTo(pOut, v)

	clear(e.buf.fpSample)
	for i := 0; i < e.params.ecd.exp; i++ {
		d := e.params.ringQ.N() - (i+1)*e.params.slots
		for j, jj := 0, d; jj < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] += e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
		for j, jj := e.params.ringQ.N()-d, 0; j < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] -= e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
	}

	for i := 0; i < e.params.ringQ.N(); i++ {
		c := e.twinCDT.Sample(-e.buf.fpSample[i])
		if c >= 0 {
			for k := 0; k <= pOut.Level(); k++ {
				e.buf.pSample.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= pOut.Level(); k++ {
				qi := int64(e.params.ringQ.SubRings[k].Modulus)
				e.buf.pSample.Coeffs[k][i] = uint64(c%qi + qi)
			}
		}
	}
	e.params.ringQ.MForm(e.buf.pSample, e.buf.pSample)

	for i, ii := 0, e.params.slots; ii < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.buf.pSample.Coeffs[k][i]
		}
	}
	for i, ii := e.params.ringQ.N()-e.params.slots, 0; i < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.params.ringQ.SubRings[k].Modulus - e.buf.pSample.Coeffs[k][i]
		}
	}
	e.params.ringQ.MulScalarThenSub(e.buf.pSample, e.params.ecd.base, e.buf.pSampleShift)

	e.params.ringQ.MForm(pOut, pOut)
	e.params.ringQ.Add(pOut, e.buf.pSampleShift, pOut)
	e.params.ringQ.NTT(pOut, pOut)
}

// RandEncode returns an randomized encoding of v with given stdDev.
func (e *Encoder[E]) RandEncodeStdDev(v []E, stdDev float64) ring.Poly {
	pOut := e.params.ringQ.NewPoly()
	e.RandEncodeTo(pOut, v)
	return pOut
}

// RandEncodeTo randomized encodes v to pOut with given stdDev.
func (e *Encoder[E]) RandEncodeStdDevTo(pOut ring.Poly, v []E, stdDev float64) {
	e.encodeTo(pOut, v)

	clear(e.buf.fpSample)
	for i := 0; i < e.params.ecd.exp; i++ {
		d := e.params.ringQ.N() - (i+1)*e.params.slots
		for j, jj := 0, d; jj < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] += e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
		for j, jj := e.params.ringQ.N()-d, 0; j < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] -= e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
	}

	for i := 0; i < e.params.ringQ.N(); i++ {
		c := e.cosac.Sample(-e.buf.fpSample[i], stdDev)
		if c >= 0 {
			for k := 0; k <= pOut.Level(); k++ {
				e.buf.pSample.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= pOut.Level(); k++ {
				qi := int64(e.params.ringQ.SubRings[k].Modulus)
				e.buf.pSample.Coeffs[k][i] = uint64(c%qi + qi)
			}
		}
	}
	e.params.ringQ.MForm(e.buf.pSample, e.buf.pSample)

	for i, ii := 0, e.params.slots; ii < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.buf.pSample.Coeffs[k][i]
		}
	}
	for i, ii := e.params.ringQ.N()-e.params.slots, 0; i < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.params.ringQ.SubRings[k].Modulus - e.buf.pSample.Coeffs[k][i]
		}
	}
	e.params.ringQ.MulScalarThenSub(e.buf.pSample, e.params.ecd.base, e.buf.pSampleShift)

	e.params.ringQ.MForm(pOut, pOut)
	e.params.ringQ.Add(pOut, e.buf.pSampleShift, pOut)
	e.params.ringQ.NTT(pOut, pOut)
}

// RoundRandEncode returns a randomized encoding of v using rounded Gaussian.
func (e *Encoder[E]) RoundRandEncode(v []E, stdDev float64) ring.Poly {
	pOut := e.params.ringQ.NewPoly()
	e.RoundRandEncodeTo(pOut, v, stdDev)
	return pOut
}

// RoundRandEncodeTo randomized encodes v to pOut using rounded Gaussian.
func (e *Encoder[E]) RoundRandEncodeTo(pOut ring.Poly, v []E, stdDev float64) {
	e.encodeTo(pOut, v)

	clear(e.buf.fpSample)
	for i := 0; i < e.params.ecd.exp; i++ {
		d := e.params.ringQ.N() - (i+1)*e.params.slots
		for j, jj := 0, d; jj < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] += e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
		for j, jj := e.params.ringQ.N()-d, 0; j < e.params.ringQ.N(); j, jj = j+1, jj+1 {
			e.buf.fpSample[jj] -= e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
	}

	for i := 0; i < e.params.ringQ.N(); i++ {
		c := e.rounded.Sample(-e.buf.fpSample[i], stdDev)
		if c >= 0 {
			for k := 0; k <= pOut.Level(); k++ {
				e.buf.pSample.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= pOut.Level(); k++ {
				qi := int64(e.params.ringQ.SubRings[k].Modulus)
				e.buf.pSample.Coeffs[k][i] = uint64(c%qi + qi)
			}
		}
	}
	e.params.ringQ.MForm(e.buf.pSample, e.buf.pSample)

	for i, ii := 0, e.params.slots; ii < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.buf.pSample.Coeffs[k][i]
		}
	}
	for i, ii := e.params.ringQ.N()-e.params.slots, 0; i < e.params.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= pOut.Level(); k++ {
			e.buf.pSampleShift.Coeffs[k][ii] = e.params.ringQ.SubRings[k].Modulus - e.buf.pSample.Coeffs[k][i]
		}
	}
	e.params.ringQ.MulScalarThenSub(e.buf.pSample, e.params.ecd.base, e.buf.pSampleShift)

	e.params.ringQ.MForm(pOut, pOut)
	e.params.ringQ.Add(pOut, e.buf.pSampleShift, pOut)
	e.params.ringQ.NTT(pOut, pOut)
}

// Decode returns a decoding of p.
func (e *Encoder[E]) Decode(p ring.Poly) []E {
	var z E
	vOut := make([]E, e.params.slots)
	for i := range vOut {
		vOut[i] = z.New()
	}
	e.DecodeTo(vOut, p)
	return vOut
}

// DecodeTo decodes p to vOut.
func (e *Encoder[E]) DecodeTo(vOut []E, p ring.Poly) {
	if len(vOut) > e.params.slots {
		panic("DecodeTo: len(vOut) > slots")
	}

	e.rns.ReconstructTo(e.buf.coeffBig, p)
	e.buf.baseE.SetUint64(e.params.ecd.base)
	for i := 0; i < e.params.slots; i++ {
		vOut[i].SetUint64(0)
		for j := e.params.ecd.exp - 1; j >= 0; j-- {
			vOut[i].Mul(vOut[i], e.buf.baseE)
			e.buf.coeffE.SetBigInt(e.buf.coeffBig[j*e.params.slots+i])
			vOut[i].Add(vOut[i], e.buf.coeffE)
		}
	}
}

// SafeCopy returns a thread-safe copy.
func (e *Encoder[E]) SafeCopy() *Encoder[E] {
	return &Encoder[E]{
		params: e.params,

		twinCDT: e.twinCDT.SafeCopy(),
		cosac:   csprng.NewCOSACSampler(),
		rounded: csprng.NewRoundedGaussianSampler(),

		rns: e.rns.SafeCopy(),

		deltaInv: e.deltaInv,

		buf: newEncoderBuffer[E](e.params.ringQ),
	}
}
