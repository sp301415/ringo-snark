package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
)

// Encoder computes the encoding of a vector to a polynomial.
type Encoder struct {
	Parameters  celpc.Parameters
	EmbedDegree int

	StreamSampler *celpc.StreamSampler

	ringQ *bigring.CyclicRing
}

// NewEncoder creates a new Encoder.
func NewEncoder(params celpc.Parameters, embedDegree int) *Encoder {
	return &Encoder{
		Parameters:  params,
		EmbedDegree: embedDegree,

		StreamSampler: celpc.NewStreamSampler(params),

		ringQ: bigring.NewCyclicRing(params.Degree(), params.Modulus()),
	}
}

// ShallowCopy creates a copy of Encoder that is thread-safe.
func (e *Encoder) ShallowCopy() *Encoder {
	return &Encoder{
		Parameters:  e.Parameters,
		EmbedDegree: e.EmbedDegree,

		StreamSampler: celpc.NewStreamSampler(e.Parameters),

		ringQ: e.ringQ.ShallowCopy(),
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
// x should have length Parameters.Degree.
func (e *Encoder) EncodeAssign(x []*big.Int, pOut bigring.BigPoly) {
	e.ringQ.ToPolyAssign(
		bigring.BigNTTPoly{Coeffs: x[:e.Parameters.Degree()]},
		bigring.BigPoly{Coeffs: pOut.Coeffs[:e.Parameters.Degree()]},
	)

	for i := e.Parameters.Degree(); i < e.EmbedDegree; i++ {
		pOut.Coeffs[i].SetInt64(0)
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

	e.StreamSampler.SampleModAssign(pOut.Coeffs[e.Parameters.Degree()])
	pOut.Coeffs[0].Sub(pOut.Coeffs[0], pOut.Coeffs[e.Parameters.Degree()])
	if pOut.Coeffs[0].Sign() < 0 {
		pOut.Coeffs[0].Add(pOut.Coeffs[0], e.Parameters.Modulus())
	}
}
