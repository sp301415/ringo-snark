package bigpoly

import "github.com/sp301415/ringo-snark/math/bignum"

// CyclicEvaluator evaluates polynomial over power-of-two cyclic ring.
type CyclicEvaluator[E bignum.Uint[E]] struct {
	*baseOperator[E]
}

// NewCyclicEvaluator creates a new [CyclicEvaluator].
func NewCyclicEvaluator[E bignum.Uint[E]](rank int) *CyclicEvaluator[E] {
	return &CyclicEvaluator[E]{
		baseOperator: newBaseOperator(rank, NewCyclicTransformer[E](rank)),
	}
}

// QuoRemByVanishing returns the quotient and remainder of p by the polynomial X^N - 1.
func (e *CyclicEvaluator[E]) QuoRemByVanishing(p *Poly[E], N int) (quo, rem *Poly[E]) {
	switch {
	case p.Rank() != e.rank:
		panic("inputs not consistent")
	case p.IsNTT:
		panic("input in NTT domain")
	}

	quo = e.NewPoly(false)
	rem = e.NewPoly(false)
	rem.CopyFrom(p)

	for i := e.rank - 1; i >= N; i-- {
		quo.Coeffs[i-N].Add(quo.Coeffs[i-N], rem.Coeffs[i])
		rem.Coeffs[i-N].Add(rem.Coeffs[i-N], rem.Coeffs[i])
		rem.Coeffs[i].SetUint64(0)
	}

	return quo, rem
}
