package buckler

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
	"github.com/sp301415/rlwe-piop/num"
)

// Encoder computes the encoding of a vector to a polynomial.
type Encoder struct {
	Parameters  celpc.Parameters
	EmbedDegree int

	UniformSampler *celpc.UniformSampler

	TwInv     []*big.Int
	degreeInv *big.Int
}

// NewEncoder creates a new Encoder.
func NewEncoder(params celpc.Parameters, embedDegree int) *Encoder {
	twInv := make([]*big.Int, params.Degree()/2)

	exp1 := big.NewInt(0).Sub(params.Modulus(), big.NewInt(1))
	exp1.Div(exp1, big.NewInt(int64(params.Degree())))
	exp2 := big.NewInt(int64(params.Degree()) / 2)
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(params.Modulus()) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, params.Modulus())
		gPow := big.NewInt(0).Exp(g, exp2, params.Modulus())
		if gPow.Cmp(big.NewInt(1)) != 0 {
			break
		}
	}

	for i := 0; i < params.Degree()/2; i++ {
		twInv[i] = big.NewInt(0).Exp(g, big.NewInt(int64(params.Degree()-i)), params.Modulus())
	}
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(params.Degree())), params.Modulus())

	return &Encoder{
		Parameters:  params,
		EmbedDegree: embedDegree,

		UniformSampler: celpc.NewUniformSampler(params),

		TwInv:     twInv,
		degreeInv: degreeInv,
	}
}

// Encode encodes a bigint vector to a polynomial.
// v should have length Parameters.Degree.
func (e *Encoder) Encode(x []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.EncodeAssign(x, pOut)
	return pOut
}

// EncodeAssign encodes a bigint vector to a polynomial and writes it to pOut.
// v should have length Parameters.Degree.
func (e *Encoder) EncodeAssign(x []*big.Int, pOut bigring.BigPoly) {
	for i := 0; i < e.Parameters.Degree(); i++ {
		pOut.Coeffs[i].Set(x[i])
	}

	for i := e.Parameters.Degree(); i < e.EmbedDegree; i++ {
		pOut.Coeffs[i].SetInt64(0)
	}

	u, v := big.NewInt(0), big.NewInt(0)

	t := 1
	for m := e.Parameters.Degree() >> 1; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				u.Set(pOut.Coeffs[j])
				v.Set(pOut.Coeffs[j+t])

				pOut.Coeffs[j].Add(u, v)
				if pOut.Coeffs[j].Cmp(e.Parameters.Modulus()) >= 0 {
					pOut.Coeffs[j].Sub(pOut.Coeffs[j], e.Parameters.Modulus())
				}

				pOut.Coeffs[j+t].Sub(u, v)
				pOut.Coeffs[j+t].Mul(pOut.Coeffs[j+t], e.TwInv[i])
				pOut.Coeffs[j+t].Mod(pOut.Coeffs[j+t], e.Parameters.Modulus())
			}
		}
		t <<= 1
	}

	for i := 0; i < e.Parameters.Degree(); i++ {
		pOut.Coeffs[i].Mul(pOut.Coeffs[i], e.degreeInv)
		pOut.Coeffs[i].Mod(pOut.Coeffs[i], e.Parameters.Modulus())
	}
}

// RandomEncode encodes a bigint vector to a polynomial with randomization.
// v should have length Parameters.Degree.
func (e *Encoder) RandomEncode(x []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.RandomEncodeAssign(x, pOut)
	return pOut
}

// RandomEncodeAssign encodes a bigint vector to a polynomial with randomization and writes it to pOut.
// v should have length Parameters.Degree.
func (e *Encoder) RandomEncodeAssign(x []*big.Int, pOut bigring.BigPoly) {
	e.EncodeAssign(x, pOut)
	for i := 0; i < e.Parameters.Degree(); i++ {
		e.UniformSampler.SampleModAssign(pOut.Coeffs[i+e.Parameters.Degree()])
		pOut.Coeffs[i].Sub(pOut.Coeffs[i], pOut.Coeffs[i+e.Parameters.Degree()])
		if pOut.Coeffs[i].Sign() < 0 {
			pOut.Coeffs[i].Add(pOut.Coeffs[i], e.Parameters.Modulus())
		}
	}
}
