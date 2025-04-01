package bigring

import (
	"math/big"
)

// Add returns pOut = p0 + p1.
func (r *BigRing) Add(p0, p1 BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.AddAssign(p0, p1, pOut)
	return pOut
}

// AddAssign assigns pOut = p0 + p1.
func (r *BigRing) AddAssign(p0, p1, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Add(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Cmp(r.modulus) >= 0 {
			pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.modulus)
		}
	}
}

// Sub returns pOut = p0 - p1.
func (r *BigRing) Sub(p0, p1 BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.SubAssign(p0, p1, pOut)
	return pOut
}

// SubAssign assigns pOut = p0 - p1.
func (r *BigRing) SubAssign(p0, p1, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Sign() < 0 {
			pOut.Coeffs[i].Add(pOut.Coeffs[i], r.modulus)
		}
	}
}

// Neg returns pOut = -p.
func (r *BigRing) Neg(p BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.NegAssign(p, pOut)
	return pOut
}

// NegAssign assigns pOut = -p.
func (r *BigRing) NegAssign(p, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(r.modulus, p.Coeffs[i])
	}
}

// ScalarMul returns pOut = p * c.
func (r *BigRing) ScalarMul(p BigPoly, c *big.Int) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.ScalarMulAssign(p, c, pOut)
	return pOut
}

// ScalarMulAssign assigns pOut = p * c.
func (r *BigRing) ScalarMulAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Mod(pOut.Coeffs[i], r.modulus)
	}
}

// ScalarMulAddAssign assigns pOut += p * c.
func (r *BigRing) ScalarMulAddAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	tmp := big.NewInt(0)
	for i := 0; i < r.degree; i++ {
		tmp.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Add(pOut.Coeffs[i], tmp)
		pOut.Coeffs[i].Mod(pOut.Coeffs[i], r.modulus)
	}
}

// ScalarMulSubAssign assigns pOut -= p * c.
func (r *BigRing) ScalarMulSubAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	tmp := big.NewInt(0)
	for i := 0; i < r.degree; i++ {
		tmp.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Sub(pOut.Coeffs[i], tmp)
		pOut.Coeffs[i].Mod(pOut.Coeffs[i], r.modulus)
	}
}

// Evaluate evaluates the polynomial p at x.
func (r *BigRing) Evaluate(p BigPoly, x *big.Int) *big.Int {
	rOut := big.NewInt(0)
	for i := r.degree - 1; i >= 0; i-- {
		rOut.Mul(rOut, x)
		rOut.Add(rOut, p.Coeffs[i])
		rOut.Mod(rOut, r.modulus)
	}
	return rOut
}

// QuoRemByVanishing returns quotient and remainder of p by the polynomial x^N - 1.
func (r *BigRing) QuoRemByVanishing(p BigPoly, N int) (BigPoly, BigPoly) {
	quo := r.NewPoly()
	rem := p.Copy()

	c := big.NewInt(0)
	for i := r.N() - 1; i >= N; i-- {
		c.Set(rem.Coeffs[i])
		quo.Coeffs[i-N].Add(quo.Coeffs[i-N], c)
		if quo.Coeffs[i-N].Cmp(r.modulus) >= 0 {
			quo.Coeffs[i-N].Sub(quo.Coeffs[i-N], r.modulus)
		}

		rem.Coeffs[i].Sub(rem.Coeffs[i], c)
		if rem.Coeffs[i].Sign() < 0 {
			rem.Coeffs[i].Add(rem.Coeffs[i], r.modulus)
		}
		rem.Coeffs[i-N].Add(rem.Coeffs[i-N], c)
		if rem.Coeffs[i-N].Cmp(r.modulus) >= 0 {
			rem.Coeffs[i-N].Sub(rem.Coeffs[i-N], r.modulus)
		}
	}

	return quo, rem
}
