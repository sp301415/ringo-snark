package buckler

import (
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/num"
)

// Encoder computes the encoding of a vector to polynomial.
type Encoder[E num.Uint[E]] struct {
	ntt       *bigpoly.CyclicTransformer[E]
	embedRank int
}

// newEncoder creates a new [Encoder].
func newEncoder[E num.Uint[E]](rank, embedRank int) *Encoder[E] {
	return &Encoder[E]{
		ntt:       bigpoly.NewCyclicTransformer[E](rank),
		embedRank: embedRank,
	}
}

// Encode encodes a bigint vector to a polynomial.
// v should have length rank.
func (e *Encoder[E]) Encode(v []E) *bigpoly.Poly[E] {
	pOut := bigpoly.NewPoly[E](e.embedRank, false)
	e.EncodeTo(pOut, v)
	return pOut
}

// EncodeTo encodes a bigint vector to pOut.
// v should have length rank.
func (e *Encoder[E]) EncodeTo(pOut *bigpoly.Poly[E], v []E) {
	e.ntt.NTTTo(pOut.Coeffs[:e.ntt.Rank()], v[:e.ntt.Rank()])
	for i := e.ntt.Rank(); i < pOut.Rank(); i++ {
		pOut.Coeffs[i].SetUint64(0)
	}
	pOut.IsNTT = false
}

// RandEncodeTo encodes a bigint vector to a polynomial using randomization.
// v should have length rank.
func (e *Encoder[E]) RandEncode(v []E) *bigpoly.Poly[E] {
	pOut := bigpoly.NewPoly[E](e.embedRank, false)
	e.RandEncodeTo(pOut, v)
	return pOut
}

// RandEncodeTo encodes a bigint vector to pOut using randomization.
// v should have length rank.
func (e *Encoder[E]) RandEncodeTo(pOut *bigpoly.Poly[E], v []E) {
	e.EncodeTo(pOut, v)
	pOut.Coeffs[e.ntt.Rank()].MustSetRandom()
	pOut.Coeffs[0].Sub(pOut.Coeffs[0], pOut.Coeffs[e.ntt.Rank()])
}
