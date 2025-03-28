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

	twInv     []*big.Int
	degreeInv *big.Int
}

// NewEncoder creates a new Encoder.
func NewEncoder(params celpc.Parameters, embedDegree int) *Encoder {
	twInv := make([]*big.Int, params.Degree())

	exp1 := big.NewInt(0).Sub(params.Modulus(), big.NewInt(1))
	exp1.Div(exp1, big.NewInt(int64(params.Degree())))
	exp2 := big.NewInt(int64(params.Degree()) / 2)
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(params.Modulus()) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, params.Modulus())
		gPow := big.NewInt(0).Exp(g, exp2, params.Modulus())
		if gPow.Cmp(big.NewInt(1)) == 0 {
			break
		}
	}

	for i := 0; i < params.Degree(); i++ {
		twInv[i] = big.NewInt(0).Exp(g, big.NewInt(int64(params.Degree()-i)), params.Modulus())
	}
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(params.Degree())), params.Modulus())
	return &Encoder{
		Parameters:  params,
		EmbedDegree: embedDegree,

		UniformSampler: celpc.NewUniformSampler(params),

		twInv:     twInv,
		degreeInv: degreeInv,
	}
}

// Encode encodes a bigint vector to a polynomial.
// v should have length Parameters.Degree.
func (e *Encoder) Encode(v []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.EncodeAssign(v, pOut)
	return pOut
}

// EncodeAssign encodes a bigint vector to a polynomial and writes it to pOut.
// v should have length Parameters.Degree.
func (e *Encoder) EncodeAssign(v []*big.Int, pOut bigring.BigPoly) {
	for i := 0; i < e.Parameters.Degree(); i++ {
		pOut.Coeffs[i].Set(v[i])
	}
	for i := e.Parameters.Degree(); i < e.EmbedDegree; i++ {
		pOut.Coeffs[i].SetInt64(0)
	}

	U, V := big.NewInt(0), big.NewInt(0)

	t := 1
	for m := e.Parameters.Degree() >> 1; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				U.Set(pOut.Coeffs[j])
				V.Set(pOut.Coeffs[j+t])

				pOut.Coeffs[j].Add(U, V)
				if pOut.Coeffs[j].Cmp(e.Parameters.Modulus()) >= 0 {
					pOut.Coeffs[j].Sub(pOut.Coeffs[j], e.Parameters.Modulus())
				}

				pOut.Coeffs[j+t].Sub(U, V)
				pOut.Coeffs[j+t].Mul(pOut.Coeffs[j+t], e.twInv[i])
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
func (e *Encoder) RandomEncode(v []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.RandomEncodeAssign(v, pOut)
	return pOut
}

// RandomEncodeAssign encodes a bigint vector to a polynomial with randomization and writes it to pOut.
// v should have length Parameters.Degree.
func (e *Encoder) RandomEncodeAssign(v []*big.Int, pOut bigring.BigPoly) {
	e.EncodeAssign(v, pOut)
	for i := 0; i < e.Parameters.Degree(); i++ {
		e.UniformSampler.SampleModAssign(pOut.Coeffs[i+e.Parameters.Degree()])
		pOut.Coeffs[i].Add(pOut.Coeffs[i], pOut.Coeffs[i+e.Parameters.Degree()])
		if pOut.Coeffs[i].Cmp(e.Parameters.Modulus()) >= 0 {
			pOut.Coeffs[i].Sub(pOut.Coeffs[i], e.Parameters.Modulus())
		}
	}
}
