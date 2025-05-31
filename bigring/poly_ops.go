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

// Automorphism returns pOut = p(X^d).
func (r *BigRing) Automorphism(p BigPoly, d int) BigPoly {
	pOut := NewBigPoly(r.degree)
	r.AutomorphismAssign(p, d, pOut)
	return pOut
}

// AutomorphismAssign assigns pOut = p(X^d).
func (r *BigRing) AutomorphismAssign(p BigPoly, d int, pOut BigPoly) {
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
func (r *BigRing) EvaluateAssign(p BigPoly, x, xOut *big.Int) {
	xOut.SetUint64(0)
	for i := r.degree - 1; i >= 0; i-- {
		xOut.Mul(xOut, x)
		xOut.Add(xOut, p.Coeffs[i])
		r.Mod(xOut)
	}
}

// QuoRemByVanishing returns quotient and remainder of p by the polynomial x^N - 1.
func (r *BigRing) QuoRemByVanishingAssign(p BigPoly, N int, quo, rem BigPoly) {
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
