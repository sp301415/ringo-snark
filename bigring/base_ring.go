package bigring

import (
	"math/big"
)

type baseBigRing struct {
	*Reducer
	degree  int
	modulus *big.Int

	mul *big.Int
}

func newBaseRing(N int, Q *big.Int) *baseBigRing {
	return &baseBigRing{
		Reducer: NewReducer(Q),
		degree:  N,
		modulus: Q,

		mul: big.NewInt(0),
	}
}

// ShallowCopy creates a shallow copy of baseBigRing that is thread-safe.
func (r *baseBigRing) ShallowCopy() *baseBigRing {
	return &baseBigRing{
		Reducer: r.Reducer.ShallowCopy(),
		degree:  r.degree,
		modulus: r.modulus,

		mul: big.NewInt(0),
	}
}

// Degree returns the degree of the BigRing.
func (r *baseBigRing) Degree() int {
	return r.degree
}

// Modulus returns the modulus of the BigRing.
func (r *baseBigRing) Modulus() *big.Int {
	return r.modulus
}

// NewPoly creates a new BigPoly.
func (r *baseBigRing) NewPoly() BigPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigPoly{Coeffs: coeffs}
}

// NewNTTPoly creates a new BigNTTPoly.
func (r *baseBigRing) NewNTTPoly() BigNTTPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigNTTPoly{Coeffs: coeffs}
}
