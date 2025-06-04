package bigring

import (
	"math/big"
)

// Add returns pOut = p0 + p1.
func (r *baseBigRing) Add(p0, p1 BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.AddAssign(p0, p1, pOut)
	return pOut
}

// AddAssign assigns pOut = p0 + p1.
func (r *baseBigRing) AddAssign(p0, p1, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Add(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Cmp(r.modulus) >= 0 {
			pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.modulus)
		}
	}
}

// Sub returns pOut = p0 - p1.
func (r *baseBigRing) Sub(p0, p1 BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.SubAssign(p0, p1, pOut)
	return pOut
}

// SubAssign assigns pOut = p0 - p1.
func (r *baseBigRing) SubAssign(p0, p1, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(p0.Coeffs[i], p1.Coeffs[i])
		if pOut.Coeffs[i].Sign() < 0 {
			pOut.Coeffs[i].Add(pOut.Coeffs[i], r.modulus)
		}
	}
}

// Neg returns pOut = -p.
func (r *baseBigRing) Neg(p BigPoly) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.NegAssign(p, pOut)
	return pOut
}

// NegAssign assigns pOut = -p.
func (r *baseBigRing) NegAssign(p, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Sub(r.modulus, p.Coeffs[i])
	}
}

// ScalarMul returns pOut = p * c.
func (r *baseBigRing) ScalarMul(p BigPoly, c *big.Int) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.ScalarMulAssign(p, c, pOut)
	return pOut
}

// ScalarMulAssign assigns pOut = p * c.
func (r *baseBigRing) ScalarMulAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		r.mul.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Set(r.mul)
		r.Reduce(pOut.Coeffs[i])
	}
}

// ScalarMulAddAssign assigns pOut += p * c.
func (r *baseBigRing) ScalarMulAddAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		r.mul.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Add(pOut.Coeffs[i], r.mul)
		r.Reduce(pOut.Coeffs[i])
	}
}

// ScalarMulSubAssign assigns pOut -= p * c.
func (r *baseBigRing) ScalarMulSubAssign(p BigPoly, c *big.Int, pOut BigPoly) {
	for i := 0; i < r.degree; i++ {
		r.mul.Mul(p.Coeffs[i], c)
		pOut.Coeffs[i].Sub(pOut.Coeffs[i], r.mul)
		r.Reduce(pOut.Coeffs[i])
	}
}

// Automorphism returns pOut = p(X^d).
func (r *baseBigRing) Automorphism(p BigPoly, d int) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.AutomorphismAssign(p, d, pOut)
	return pOut
}

// AutomorphismAssign assigns pOut = p(X^d).
func (r *baseBigRing) AutomorphismAssign(p BigPoly, d int, pOut BigPoly) {
	d %= 2 * r.degree
	if d < 0 {
		d += 2 * r.degree
	}

	for i := 0; i < r.degree; i++ {
		j := (i * d) % (2 * r.degree)
		if j < r.degree {
			pOut.Coeffs[j].Set(p.Coeffs[i])
		} else {
			j -= r.degree
			pOut.Coeffs[j].Neg(p.Coeffs[i])
			pOut.Coeffs[j].Add(pOut.Coeffs[j], r.modulus)
		}
	}
}

// Evaluate evaluates the polynomial p at x.
func (r *baseBigRing) EvaluateAssign(p BigPoly, x, xOut *big.Int) {
	xOut.SetUint64(0)
	for i := r.degree - 1; i >= 0; i-- {
		r.mul.Mul(xOut, x)
		xOut.Add(r.mul, p.Coeffs[i])
		r.Reduce(xOut)
	}
}

// QuoRemByVanishing returns quotient and remainder of p by the polynomial x^N - 1.
func (r *baseBigRing) QuoRemByVanishingAssign(p BigPoly, N int, quo, rem BigPoly) {
	quo.Clear()
	rem.CopyFrom(p)

	for i := r.Degree() - 1; i >= N; i-- {
		quo.Coeffs[i-N].Add(quo.Coeffs[i-N], rem.Coeffs[i])
		if quo.Coeffs[i-N].Cmp(r.modulus) >= 0 {
			quo.Coeffs[i-N].Sub(quo.Coeffs[i-N], r.modulus)
		}

		rem.Coeffs[i-N].Add(rem.Coeffs[i-N], rem.Coeffs[i])
		if rem.Coeffs[i-N].Cmp(r.modulus) >= 0 {
			rem.Coeffs[i-N].Sub(rem.Coeffs[i-N], r.modulus)
		}
		rem.Coeffs[i].SetUint64(0)
	}
}
