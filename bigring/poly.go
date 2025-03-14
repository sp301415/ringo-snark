package bigring

import "math/big"

// BigPoly is a polynomial with bigint coefficients.
type BigPoly struct {
	Coeffs []*big.Int
}

// NewBigPoly creates a new BigPoly.
func NewBigPoly(N int) BigPoly {
	coeffs := make([]*big.Int, N)
	for i := 0; i < N; i++ {
		coeffs[i] = big.NewInt(0)
	}

	return BigPoly{
		Coeffs: coeffs,
	}
}

// Degree returns the degree of the BigPoly.
func (p BigPoly) Degree() int {
	return len(p.Coeffs)
}

// Clear clears the BigPoly.
func (p *BigPoly) Clear() {
	for i := 0; i < len(p.Coeffs); i++ {
		p.Coeffs[i].SetInt64(0)
	}
}

// BigNTTPoly is a NTT form of BigPoly.
type BigNTTPoly struct {
	Coeffs []*big.Int
}

// NewBigNTTPoly creates a new BigNTTPoly.
func NewBigNTTPoly(N int) BigNTTPoly {
	coeffs := make([]*big.Int, N)
	for i := 0; i < N; i++ {
		coeffs[i] = big.NewInt(0)
	}

	return BigNTTPoly{
		Coeffs: coeffs,
	}
}

// Degree returns the degree of the BigNTTPoly.
func (p BigNTTPoly) Degree() int {
	return len(p.Coeffs)
}

// Clear clears the BigNTTPoly.
func (p *BigNTTPoly) Clear() {
	for i := 0; i < len(p.Coeffs); i++ {
		p.Coeffs[i].SetInt64(0)
	}
}
