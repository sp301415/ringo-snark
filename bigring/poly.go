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

// CopyFrom copies the coefficients from another BigPoly.
func (p *BigPoly) CopyFrom(p0 BigPoly) {
	for i := 0; i < len(p.Coeffs); i++ {
		p.Coeffs[i].Set(p0.Coeffs[i])
	}
}

// Copy copies the BigPoly.
func (p BigPoly) Copy() BigPoly {
	coeffs := make([]*big.Int, len(p.Coeffs))
	for i := 0; i < len(p.Coeffs); i++ {
		coeffs[i] = big.NewInt(0).Set(p.Coeffs[i])
	}

	return BigPoly{
		Coeffs: coeffs,
	}
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
