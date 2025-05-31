package bigring

import "math/big"

// AddNTT returns pOut = p0 + p1.
func (r *BigRing) AddNTT(p0, p1 BigNTTPoly) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.AddNTTAssign(p0, p1, pOut)
	return pOut
}

// AddNTTAssign assigns pOut = p0 + p1.
func (r *BigRing) AddNTTAssign(p0, p1, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Add(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Cmp(r.modulus) >= 0 {
			pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.modulus)
		}
	}
}

// SubNTT returns pOut = p0 - p1.
func (r *BigRing) SubNTT(p0, p1 BigNTTPoly) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.SubNTTAssign(p0, p1, pOut)
	return pOut
}

// SubNTTAssign assigns pOut = p0 - p1.
func (r *BigRing) SubNTTAssign(p0, p1, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Sign() < 0 {
			pOut.Coeffs[i].Add(pOut.Coeffs[i], r.modulus)
		}
	}
}

// NegNTT returns pOut = -p.
func (r *BigRing) NegNTT(p BigNTTPoly) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.NegNTTAssign(p, pOut)
	return pOut
}

// NegNTTAssign assigns pOut = -p.
func (r *BigRing) NegNTTAssign(p, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(r.modulus, p.Coeffs[i])
	}
}

// ScalarMulNTT returns pOut = p * c.
func (r *BigRing) ScalarMulNTT(p BigNTTPoly, c *big.Int) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.ScalarMulNTTAssign(p, c, pOut)
	return pOut
}

// ScalarMulNTTAssign assigns pOut = p * c.
func (r *BigRing) ScalarMulNTTAssign(p BigNTTPoly, c *big.Int, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Mod(pOut.Coeffs[i], r.modulus)
	}
}

// ScalarMulAddNTTAssign assigns pOut += p * c.
func (r *BigRing) ScalarMulAddNTTAssign(p BigNTTPoly, c *big.Int, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		r.buffer.mul.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Add(pOut.Coeffs[i], r.buffer.mul)
		r.Mod(pOut.Coeffs[i])
	}
}

// ScalarMulSubNTTAssign assigns pOut -= p * c.
func (r *BigRing) ScalarMulSubNTTAssign(p BigNTTPoly, c *big.Int, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		r.buffer.mul.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.buffer.mul)
		r.Mod(pOut.Coeffs[i])
	}
}

// MulNTT returns pOut = p0 * p1.
func (r *BigRing) MulNTT(p0, p1 BigNTTPoly) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.MulNTTAssign(p0, p1, pOut)
	return pOut
}

// MulNTTAssign assigns pOut = p0 * p1.
func (r *BigRing) MulNTTAssign(p0, p1, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Mul(p0.Coeffs[i], p1.Coeffs[i])
		r.Mod(pOut.Coeffs[i])
	}
}

// MulAddNTTAssign assigns pOut += p0 * p1.
func (r *BigRing) MulAddNTTAssign(p0, p1 BigNTTPoly, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		r.buffer.mul.Mul(p0.Coeffs[i], p1.Coeffs[i])
		pOut.Coeffs[i].Add(pOut.Coeffs[i], r.buffer.mul)
		r.Mod(pOut.Coeffs[i])
	}
}

// MulSubNTTAssign assigns pOut -= p0 * p1.
func (r *BigRing) MulSubNTTAssign(p0, p1 BigNTTPoly, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		r.buffer.mul.Mul(p0.Coeffs[i], p1.Coeffs[i])
		pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.buffer.mul)
		r.Mod(pOut.Coeffs[i])
	}
}

// AutomorphismNTT returns pOut = p(X^d).
func (r *BigRing) AutomorphismNTT(p BigNTTPoly, d int) BigNTTPoly {
	pOut := NewBigNTTPoly(r.degree)
	r.AutomorphismNTTAssign(p, d, pOut)
	return pOut
}

// AutomorphismNTTAssign assigns pOut = p(X^d).
func (r *BigRing) AutomorphismNTTAssign(p BigNTTPoly, d int, pOut BigNTTPoly) {
	d %= 2 * r.degree
	if d < 0 {
		d += 2 * r.degree
	}

	for i := 0; i < r.degree; i++ {
		j := ((2*i + 1) * d) % (2 * r.degree)
		j = (j - 1) >> 1
		pOut.Coeffs[i].Set(p.Coeffs[j])
	}
}
