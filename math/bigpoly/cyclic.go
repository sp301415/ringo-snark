package bigpoly

import "github.com/sp301415/ringo-snark/math/bignum"

// CyclicOperator evaluates polynomial over power-of-two cyclic ring.
type CyclicOperator[E bignum.Uint[E]] struct {
	*baseOperator[E]
}

// NewCyclicEvaluator creates a new [CyclicOperator].
func NewCyclicEvaluator[E bignum.Uint[E]](rank int) *CyclicOperator[E] {
	return &CyclicOperator[E]{
		baseOperator: newBaseOperator(rank, NewCyclicTransformer[E](rank)),
	}
}

// QuoRemByVanishing returns the quotient and remainder of p by the polynomial X^N - 1.
func (e *CyclicOperator[E]) QuoRemByVanishing(p *Poly[E], N int) (quo, rem *Poly[E]) {
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
