package celpc

import (
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

// encoderBase computes the encoding of a polynomial.
type encoderBase struct {
	Parameters Parameters
	*RNSReconstructor

	// baseBig is the big integer representation of the base.
	baseBig *big.Int
	// deltaInv is a constnat used in randomized encoding.
	// Equals to [-1/p, -b/p, ..., -b^(r-1)/p].
	deltaInv []float64

	buffer encoderBaseBuffer
}

type encoderBaseBuffer struct {
	coeffBalanced []*big.Int
	quo           *big.Int
	rem           *big.Int
}

// newEncoderBase creates a new encoderBase.
func newEncoderBase(params Parameters) *encoderBase {
	prec := uint(params.modulus.BitLen())
	modulusInv := big.NewFloat(0).SetPrec(prec)
	modulusInv.SetInt(params.modulus)
	modulusInv.Quo(big.NewFloat(1).SetPrec(prec), modulusInv)
	modulusInv.Neg(modulusInv)

	base := big.NewFloat(float64(params.modulusBase)).SetPrec(prec)
	deltaInv := make([]float64, params.digits)
	for i := 0; i < params.digits; i++ {
		deltaInv[i], _ = modulusInv.Float64()
		modulusInv.Mul(modulusInv, base)
	}

	return &encoderBase{
		Parameters:       params,
		RNSReconstructor: NewRNSReconstructor(params),

		baseBig:  big.NewInt(int64(params.modulusBase)),
		deltaInv: deltaInv,

		buffer: newEncoderBaseBuffer(params),
	}
}

// newEncoderBaseBuffer creates a new encoderBaseBuffer.
func newEncoderBaseBuffer(params Parameters) encoderBaseBuffer {
	coeffBalanced := make([]*big.Int, params.ringQ.N())
	for i := 0; i < params.ringQ.N(); i++ {
		coeffBalanced[i] = big.NewInt(0).Set(params.ringQ.Modulus())
	}

	return encoderBaseBuffer{
		coeffBalanced: coeffBalanced,
		quo:           big.NewInt(0).Set(params.modulus),
		rem:           big.NewInt(0).Set(params.modulus),
	}
}

// ShallowCopy returns a copy of encoderBase that is thread-safe.
func (e *encoderBase) ShallowCopy() *encoderBase {
	return &encoderBase{
		Parameters:       e.Parameters,
		RNSReconstructor: e.RNSReconstructor.ShallowCopy(),

		baseBig:  e.baseBig,
		deltaInv: e.deltaInv,

		buffer: newEncoderBaseBuffer(e.Parameters),
	}
}

// Encode encodes a bigint vector to a polynomial.
func (e *encoderBase) Encode(v []*big.Int) ring.Poly {
	pOut := e.Parameters.ringQ.NewPoly()
	e.EncodeAssign(v, pOut)
	return pOut
}

// EncodeAssign encodes a bigint vector to a polynomial and writes it to pOut.
func (e *encoderBase) EncodeAssign(v []*big.Int, pOut ring.Poly) {
	pOut.Zero()

	for i := 0; i < len(v); i++ {
		e.buffer.quo.Mod(v[i], e.Parameters.modulus)
		for j := 0; j < e.Parameters.digits-1; j++ {
			e.buffer.quo.DivMod(e.buffer.quo, e.baseBig, e.buffer.rem)
			r := e.buffer.rem.Uint64()
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][j*e.Parameters.slots+i] = r
			}
		}
		r := e.buffer.quo.Uint64()
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			pOut.Coeffs[k][(e.Parameters.digits-1)*e.Parameters.slots+i] = r
		}
	}

	e.Parameters.ringQ.NTT(pOut, pOut)
	e.Parameters.ringQ.MForm(pOut, pOut)
}

// EncodeChunk encodes a bigint vector to multiple polynomials.
// The output polynomial vector has length len(v) / Slots.
func (e *encoderBase) EncodeChunk(v []*big.Int) []ring.Poly {
	pOut := make([]ring.Poly, len(v)/e.Parameters.slots)
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		pOut[i] = e.Parameters.ringQ.NewPoly()
	}
	e.EncodeChunkAssign(v, pOut)
	return pOut
}

// EncodeChunkAssign encodes a bigint vector to multiple polynomials and writes it to pOut.
func (e *encoderBase) EncodeChunkAssign(v []*big.Int, pOut []ring.Poly) {
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		e.EncodeAssign(v[i*e.Parameters.slots:(i+1)*e.Parameters.slots], pOut[i])
	}
}

// Decode decodes a polynomial to a BigInt vector.
func (e *encoderBase) Decode(p ring.Poly) []*big.Int {
	vOut := make([]*big.Int, e.Parameters.slots)
	for i := 0; i < e.Parameters.slots; i++ {
		vOut[i] = big.NewInt(0)
	}
	e.DecodeAssign(p, vOut)
	return vOut
}

// DecodeAssign decodes a polynomial to a BigInt vector and writes it to vOut.
// pNTT should be in NTT form.
func (e *encoderBase) DecodeAssign(p ring.Poly, vOut []*big.Int) {
	e.RNSReconstructor.ReconstructAssign(p, e.buffer.coeffBalanced)

	for i := 0; i < e.Parameters.slots; i++ {
		vOut[i].SetUint64(0)
		for j := e.Parameters.digits - 1; j >= 0; j-- {
			vOut[i].Mul(vOut[i], e.baseBig)
			vOut[i].Add(vOut[i], e.buffer.coeffBalanced[j*e.Parameters.slots+i])
		}
		vOut[i].Mod(vOut[i], e.Parameters.modulus)
	}
}

// DecodeChunk decodes multiple polynomials to a BigInt vector.
// The output vector has length len(p) * Slots.
func (e *encoderBase) DecodeChunk(p []ring.Poly) []*big.Int {
	vOut := make([]*big.Int, len(p)*e.Parameters.slots)
	for i := 0; i < len(p)*e.Parameters.slots; i++ {
		vOut[i] = big.NewInt(0)
	}
	e.DecodeChunkAssign(p, vOut)
	return vOut
}

// DecodeChunkAssign decodes multiple polynomials to a BigInt vector and writes it to vOut.
// The output vector should have length len(p) * Slots.
func (e *encoderBase) DecodeChunkAssign(p []ring.Poly, vOut []*big.Int) {
	for i := 0; i < len(p); i++ {
		e.DecodeAssign(p[i], vOut[i*e.Parameters.slots:(i+1)*e.Parameters.slots])
	}
}

// Encoder computes the encoding of a polynomial.
type Encoder struct {
	*encoderBase
	GaussianSampler *COSACSampler

	buffer encoderBuffer
}

type encoderBuffer struct {
	fpSample     []float64
	pSample      ring.Poly
	pSampleShift ring.Poly

	quo *big.Int
	rem *big.Int
}

// NewEncoder creates a new Encoder.
func NewEncoder(params Parameters) *Encoder {
	return &Encoder{
		encoderBase:     newEncoderBase(params),
		GaussianSampler: NewCOSACSampler(params),

		buffer: newEncoderBuffer(params),
	}
}

// newEncoderBuffer creates a new encoderBuffer.
func newEncoderBuffer(params Parameters) encoderBuffer {
	return encoderBuffer{
		fpSample:     make([]float64, params.ringQ.N()),
		pSample:      params.ringQ.NewPoly(),
		pSampleShift: params.ringQ.NewPoly(),

		quo: big.NewInt(0).Set(params.modulus),
		rem: big.NewInt(0).Set(params.modulus),
	}
}

// ShallowCopy returns a copy of Encoder that is thread-safe.
func (e *Encoder) ShallowCopy() *Encoder {
	return &Encoder{
		encoderBase:     e.encoderBase.ShallowCopy(),
		GaussianSampler: NewCOSACSampler(e.Parameters),

		buffer: newEncoderBuffer(e.Parameters),
	}
}

// RandomEncode encodes a bigint vector to a polynomial with randomization.
func (e *Encoder) RandomEncode(v []*big.Int, stdDev float64) ring.Poly {
	pOut := e.Parameters.ringQ.NewPoly()
	e.RandomEncodeAssign(v, stdDev, pOut)
	return pOut
}

// RandomEncodeAssign encodes a bigint vector to a polynomial with randomization and writes it to pOut.
func (e *Encoder) RandomEncodeAssign(v []*big.Int, stdDev float64, pOut ring.Poly) {
	pOut.Zero()

	for i := 0; i < len(v); i++ {
		e.buffer.quo.Mod(v[i], e.Parameters.modulus)
		for j := 0; j < e.Parameters.digits-1; j++ {
			e.buffer.quo.DivMod(e.buffer.quo, e.baseBig, e.buffer.rem)
			r := e.buffer.rem.Uint64()
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][j*e.Parameters.slots+i] = r
			}
		}
		r := e.buffer.quo.Uint64()
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			pOut.Coeffs[k][(e.Parameters.digits-1)*e.Parameters.slots+i] = r
		}
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		e.buffer.fpSample[i] = 0
	}

	for i := 0; i < e.Parameters.digits; i++ {
		d := e.Parameters.ringQ.N() - (i+1)*e.Parameters.slots
		for j, jj := 0, d; jj < e.Parameters.ringQ.N(); j, jj = j+1, jj+1 {
			e.buffer.fpSample[jj] += e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
		for j, jj := e.Parameters.ringQ.N()-d, 0; j < e.Parameters.ringQ.N(); j, jj = j+1, jj+1 {
			e.buffer.fpSample[jj] -= e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		c := e.GaussianSampler.Sample(-e.buffer.fpSample[i], stdDev)
		if c >= 0 {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				e.buffer.pSample.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				e.buffer.pSample.Coeffs[k][i] = uint64(c + int64(e.Parameters.ringQ.SubRings[k].Modulus))
			}
		}
	}

	for i, ii := 0, e.Parameters.slots; ii < e.Parameters.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			e.buffer.pSampleShift.Coeffs[k][ii] = e.buffer.pSample.Coeffs[k][i]
		}
	}
	for i, ii := e.Parameters.ringQ.N()-e.Parameters.slots, 0; i < e.Parameters.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			e.buffer.pSampleShift.Coeffs[k][ii] = e.Parameters.ringQ.SubRings[k].Modulus - e.buffer.pSample.Coeffs[k][i]
		}
	}
	e.Parameters.ringQ.MulScalarThenSub(e.buffer.pSample, uint64(e.Parameters.modulusBase), e.buffer.pSampleShift)

	e.Parameters.ringQ.Add(pOut, e.buffer.pSampleShift, pOut)
	e.Parameters.ringQ.NTT(pOut, pOut)
	e.Parameters.ringQ.MForm(pOut, pOut)
}

// RandomEncodeChunk encodes a bigint vector to multiple polynomials with randomization.
// The output polynomial vector has length len(v) / Slots.
func (e *Encoder) RandomEncodeChunk(v []*big.Int, stdDev float64) []ring.Poly {
	pOut := make([]ring.Poly, len(v)/e.Parameters.slots)
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		pOut[i] = e.Parameters.ringQ.NewPoly()
	}
	e.RandomEncodeChunkAssign(v, stdDev, pOut)
	return pOut
}

// EncodeChunkAssign encodes a bigint vector to multiple polynomials with randomization and writes it to pOut.
func (e *Encoder) RandomEncodeChunkAssign(v []*big.Int, stdDev float64, pOut []ring.Poly) {
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		e.RandomEncodeAssign(v[i*e.Parameters.slots:(i+1)*e.Parameters.slots], stdDev, pOut[i])
	}
}

// EncoderFixedStdDev computes the encoding of a polynomial,
// with a fixed standard deviation for the Gaussian distribution.
type EncoderFixedStdDev struct {
	*encoderBase
	GaussianSampler *TwinCDTSampler

	buffer encoderBuffer
}

// NewEncoderFixedStdDev creates a new EncoderFixedStdDev.
func NewEncoderFixedStdDev(params Parameters, stdDev float64) *EncoderFixedStdDev {
	return &EncoderFixedStdDev{
		encoderBase:     newEncoderBase(params),
		GaussianSampler: NewTwinCDTSampler(params, stdDev),

		buffer: newEncoderBuffer(params),
	}
}

// ShallowCopy returns a copy of Encoder that is thread-safe.
func (e *EncoderFixedStdDev) ShallowCopy() *EncoderFixedStdDev {
	return &EncoderFixedStdDev{
		encoderBase:     e.encoderBase.ShallowCopy(),
		GaussianSampler: e.GaussianSampler.ShallowCopy(),

		buffer: newEncoderBuffer(e.Parameters),
	}
}

// RandomEncode encodes a bigint vector to a polynomial with randomization.
func (e *EncoderFixedStdDev) RandomEncode(v []*big.Int) ring.Poly {
	pOut := e.Parameters.ringQ.NewPoly()
	e.RandomEncodeAssign(v, pOut)
	return pOut
}

// RandomEncodeAssign encodes a bigint vector to a polynomial with randomization and writes it to pOut.
func (e *EncoderFixedStdDev) RandomEncodeAssign(v []*big.Int, pOut ring.Poly) {
	pOut.Zero()

	for i := 0; i < len(v); i++ {
		e.buffer.quo.Mod(v[i], e.Parameters.modulus)
		for j := 0; j < e.Parameters.digits-1; j++ {
			e.buffer.quo.DivMod(e.buffer.quo, e.baseBig, e.buffer.rem)
			r := e.buffer.rem.Uint64()
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][j*e.Parameters.slots+i] = r
			}
		}
		r := e.buffer.quo.Uint64()
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			pOut.Coeffs[k][(e.Parameters.digits-1)*e.Parameters.slots+i] = r
		}
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		e.buffer.fpSample[i] = 0
	}

	for i := 0; i < e.Parameters.digits; i++ {
		d := e.Parameters.ringQ.N() - (i+1)*e.Parameters.slots
		for j, jj := 0, d; jj < e.Parameters.ringQ.N(); j, jj = j+1, jj+1 {
			e.buffer.fpSample[jj] += e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
		for j, jj := e.Parameters.ringQ.N()-d, 0; j < e.Parameters.ringQ.N(); j, jj = j+1, jj+1 {
			e.buffer.fpSample[jj] -= e.deltaInv[i] * float64(pOut.Coeffs[0][j])
		}
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		c := e.GaussianSampler.Sample(-e.buffer.fpSample[i])
		if c >= 0 {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				e.buffer.pSample.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				e.buffer.pSample.Coeffs[k][i] = uint64(c + int64(e.Parameters.ringQ.SubRings[k].Modulus))
			}
		}
	}

	for i, ii := 0, e.Parameters.slots; ii < e.Parameters.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			e.buffer.pSampleShift.Coeffs[k][ii] = e.buffer.pSample.Coeffs[k][i]
		}
	}
	for i, ii := e.Parameters.ringQ.N()-e.Parameters.slots, 0; i < e.Parameters.ringQ.N(); i, ii = i+1, ii+1 {
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			e.buffer.pSampleShift.Coeffs[k][ii] = e.Parameters.ringQ.SubRings[k].Modulus - e.buffer.pSample.Coeffs[k][i]
		}
	}
	e.Parameters.ringQ.MulScalarThenSub(e.buffer.pSample, uint64(e.Parameters.modulusBase), e.buffer.pSampleShift)

	e.Parameters.ringQ.Add(pOut, e.buffer.pSampleShift, pOut)
	e.Parameters.ringQ.NTT(pOut, pOut)
	e.Parameters.ringQ.MForm(pOut, pOut)
}

// RandomEncodeChunk encodes a bigint vector to multiple polynomials with randomization.
// The output polynomial vector has length len(v) / Slots.
func (e *EncoderFixedStdDev) RandomEncodeChunk(v []*big.Int) []ring.Poly {
	pOut := make([]ring.Poly, len(v)/e.Parameters.slots)
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		pOut[i] = e.Parameters.ringQ.NewPoly()
	}
	e.RandomEncodeChunkAssign(v, pOut)
	return pOut
}

// EncodeChunkAssign encodes a bigint vector to multiple polynomials with randomization and writes it to pOut.
func (e *EncoderFixedStdDev) RandomEncodeChunkAssign(v []*big.Int, pOut []ring.Poly) {
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		e.RandomEncodeAssign(v[i*e.Parameters.slots:(i+1)*e.Parameters.slots], pOut[i])
	}
}
