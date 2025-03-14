package bigring

import "math/big"

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
