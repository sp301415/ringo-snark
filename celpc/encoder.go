package celpc

import (
	"math"
	"math/big"

	"github.com/sp301415/rlwe-piop/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Encoder computes the encoding of a polynomial.
type Encoder struct {
	Parameters Parameters

	GaussianSampler *csprng.GaussianSampler

	// baseBig is the big integer representation of the base.
	baseBig *big.Int
	// deltaInv is a constnat used in randomized encoding.
	// Equals to [-1/p, -b/p, ..., -b^(r-1)/p].
	deltaInv []float64
}

// NewEncoder creates a new Encoder.
func NewEncoder(params Parameters) *Encoder {
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

	return &Encoder{
		Parameters: params,

		GaussianSampler: csprng.NewGaussianSampler(),

		baseBig:  big.NewInt(int64(params.modulusBase)),
		deltaInv: deltaInv,
	}
}

// ShallowCopy returns a copy of Encoder that is thread-safe.
func (e *Encoder) ShallowCopy() *Encoder {
	return &Encoder{
		Parameters: e.Parameters,

		GaussianSampler: csprng.NewGaussianSampler(),

		baseBig:  e.baseBig,
		deltaInv: e.deltaInv,
	}
}

// Encode encodes a bigint vector to a polynomial.
func (e *Encoder) Encode(v []*big.Int) ring.Poly {
	pOut := e.Parameters.ringQ.NewPoly()
	e.EncodeAssign(v, pOut)
	return pOut
}

// EncodeAssign encodes a bigint vector to a polynomial and writes it to pOut.
func (e *Encoder) EncodeAssign(v []*big.Int, pOut ring.Poly) {
	pOut.Zero()

	coeff, rem := big.NewInt(0), big.NewInt(0)
	for i := 0; i < len(v); i++ {
		coeff.Mod(v[i], e.Parameters.modulus)
		for j := 0; j < e.Parameters.digits-1; j++ {
			coeff.DivMod(coeff, e.baseBig, rem)
			r := rem.Uint64()
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][j*e.Parameters.slots+i] = r
			}
		}
		r := coeff.Uint64()
		for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
			pOut.Coeffs[k][(e.Parameters.digits-1)*e.Parameters.slots+i] = r
		}
	}

	e.Parameters.ringQ.NTT(pOut, pOut)
	e.Parameters.ringQ.MForm(pOut, pOut)
}

// EncodeChunk encodes a bigint vector to multiple polynomials.
// The output polynomial vector has length len(v) / Slots.
func (e *Encoder) EncodeChunk(v []*big.Int) []ring.Poly {
	pOut := make([]ring.Poly, len(v)/e.Parameters.slots)
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		pOut[i] = e.Parameters.ringQ.NewPoly()
	}
	e.EncodeChunkAssign(v, pOut)
	return pOut
}

// EncodeChunkAssign encodes a bigint vector to multiple polynomials and writes it to pOut.
func (e *Encoder) EncodeChunkAssign(v []*big.Int, pOut []ring.Poly) {
	for i := 0; i < len(v)/e.Parameters.slots; i++ {
		e.EncodeAssign(v[i*e.Parameters.slots:(i+1)*e.Parameters.slots], pOut[i])
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
	fpEcd := make([]float64, pOut.N())
	coeff, rem := big.NewInt(0), big.NewInt(0)
	for i := 0; i < len(v); i++ {
		coeff.Mod(v[i], e.Parameters.modulus)
		for j := 0; j < e.Parameters.digits-1; j++ {
			coeff.DivMod(coeff, e.baseBig, rem)
			fpEcd[j*e.Parameters.slots+i], _ = rem.Float64()
		}
		fpEcd[(e.Parameters.digits-1)*e.Parameters.slots+i], _ = coeff.Float64()
	}

	fpSample := make([]float64, e.Parameters.ringQ.N())
	for i := 0; i < e.Parameters.digits; i++ {
		d := e.Parameters.ringQ.N() - (i+1)*e.Parameters.slots
		for j := 0; j < e.Parameters.ringQ.N()-d; j++ {
			fpSample[j+d] += e.deltaInv[i] * fpEcd[j]
		}
		for j := e.Parameters.ringQ.N() - d; j < e.Parameters.ringQ.N(); j++ {
			fpSample[j+d-e.Parameters.ringQ.N()] -= e.deltaInv[i] * fpEcd[j]
		}
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		fpSample[i] = e.GaussianSampler.SampleCoset(fpSample[i], stdDev)
	}

	baseFloat := float64(e.Parameters.modulusBase)
	for i := 0; i < e.Parameters.ringQ.N()-e.Parameters.slots; i++ {
		fpEcd[i+e.Parameters.slots] = fpSample[i] - baseFloat*fpSample[i+e.Parameters.slots]
	}
	for i := e.Parameters.ringQ.N() - e.Parameters.slots; i < e.Parameters.ringQ.N(); i++ {
		fpEcd[i+e.Parameters.slots-e.Parameters.ringQ.N()] = -fpSample[i] - baseFloat*fpSample[i+e.Parameters.slots-e.Parameters.ringQ.N()]
	}

	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		c := int64(math.Round(fpEcd[i]))
		if c >= 0 {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][i] = uint64(c)
			}
		} else {
			for k := 0; k <= e.Parameters.ringQ.Level(); k++ {
				pOut.Coeffs[k][i] = uint64(c + int64(e.Parameters.ringQ.SubRings[k].Modulus))
			}
		}
	}

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

// Decode decodes a polynomial to a BigInt vector.
func (e *Encoder) Decode(p ring.Poly) []*big.Int {
	vOut := make([]*big.Int, e.Parameters.slots)
	for i := 0; i < e.Parameters.slots; i++ {
		vOut[i] = big.NewInt(0)
	}
	e.DecodeAssign(p, vOut)
	return vOut
}

// DecodeAssign decodes a polynomial to a BigInt vector and writes it to vOut.
// pNTT should be in NTT form.
func (e *Encoder) DecodeAssign(p ring.Poly, vOut []*big.Int) {
	pDcdBig := make([]*big.Int, e.Parameters.ringQ.N())
	for i := 0; i < e.Parameters.ringQ.N(); i++ {
		pDcdBig[i] = big.NewInt(0)
	}
	polyToBigIntCenteredAssign(e.Parameters, p, pDcdBig)

	for i := 0; i < e.Parameters.slots; i++ {
		vOut[i].SetInt64(0)
		for j := e.Parameters.digits - 1; j >= 0; j-- {
			vOut[i].Mul(vOut[i], e.baseBig)
			vOut[i].Add(vOut[i], pDcdBig[j*e.Parameters.slots+i])
		}
		vOut[i].Mod(vOut[i], e.Parameters.modulus)
	}
}

// DecodeChunk decodes multiple polynomials to a BigInt vector.
// The output vector has length len(p) * Slots.
func (e *Encoder) DecodeChunk(p []ring.Poly) []*big.Int {
	vOut := make([]*big.Int, len(p)*e.Parameters.slots)
	for i := 0; i < len(p)*e.Parameters.slots; i++ {
		vOut[i] = big.NewInt(0)
	}
	e.DecodeChunkAssign(p, vOut)
	return vOut
}

// DecodeChunkAssign decodes multiple polynomials to a BigInt vector and writes it to vOut.
// The output vector should have length len(p) * Slots.
func (e *Encoder) DecodeChunkAssign(p []ring.Poly, vOut []*big.Int) {
	for i := 0; i < len(p); i++ {
		e.DecodeAssign(p[i], vOut[i*e.Parameters.slots:(i+1)*e.Parameters.slots])
	}
}
