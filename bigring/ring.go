package bigring

import (
	"math/big"

	"github.com/sp301415/cyclone/num"
)

// BigRing is a negacyclic ring.
type BigRing struct {
	degree  int
	modulus *big.Int

	tw        []*big.Int
	twInv     []*big.Int
	degreeInv *big.Int
}

// NewBigRing creates a new BigRing.
func NewBigRing(N int, Q *big.Int) *BigRing {
	tw := make([]*big.Int, N)
	twInv := make([]*big.Int, N)

	exp1 := big.NewInt(0).Sub(Q, big.NewInt(1))
	exp1.Div(exp1, big.NewInt(2*int64(N)))
	exp2 := big.NewInt(int64(N))
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(Q) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, Q)
		gPow := big.NewInt(0).Exp(g, exp2, Q)
		if gPow.Cmp(big.NewInt(1)) != 0 {
			break
		}
	}

	for i := 0; i < N; i++ {
		tw[i] = big.NewInt(0).Exp(g, big.NewInt(int64(i)), Q)
		twInv[i] = big.NewInt(0).Exp(g, big.NewInt(int64(2*N-i)), Q)
	}
	num.BitReverseInPlace(tw)
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(N)), Q)

	return &BigRing{
		degree:  N,
		modulus: Q,

		tw:        tw,
		twInv:     twInv,
		degreeInv: degreeInv,
	}
}

// Degree returns the degree of the BigRing.
func (r *BigRing) Degree() int {
	return r.degree
}

// Modulus returns the modulus of the BigRing.
func (r *BigRing) Modulus() *big.Int {
	return r.modulus
}

// NewPoly creates a new BigPoly.
func (r *BigRing) NewPoly() BigPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigPoly{Coeffs: coeffs}
}

// NewNTTPoly creates a new BigNTTPoly.
func (r *BigRing) NewNTTPoly() BigNTTPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigNTTPoly{Coeffs: coeffs}
}

// ToNTTPoly computes NTT of p.
func (r *BigRing) ToNTTPoly(p BigPoly) BigNTTPoly {
	pOut := r.NewNTTPoly()
	r.ToNTTPolyAssign(p, pOut)
	return pOut
}

// ToNTTPolyAssign computes NTT of p and assigns it to pOut.
func (r *BigRing) ToNTTPolyAssign(p BigPoly, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.NTTInPlace(pOut.Coeffs)
}

// ToPoly computes inverse NTT of p.
func (r *BigRing) ToPoly(p BigNTTPoly) BigPoly {
	pOut := r.NewPoly()
	r.ToPolyAssign(p, pOut)
	return pOut
}

// ToPolyAssign computes inverse NTT of p and assigns it to pOut.
func (r *BigRing) ToPolyAssign(p BigNTTPoly, pOut BigPoly) {
	for i := 0; i < pOut.Degree(); i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.InvNTTInPlace(pOut.Coeffs)
	r.NormalizeInPlace(pOut.Coeffs)
}

// NTTInPlace computes the NTT of a bigint vector in-place.
func (r *BigRing) NTTInPlace(coeffs []*big.Int) {
	u, v := big.NewInt(0), big.NewInt(0)

	t := r.degree
	for m := 1; m < r.degree; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				u.Set(coeffs[j])
				v.Set(coeffs[j+t])

				v.Mul(v, r.tw[m+i])
				v.Mod(v, r.modulus)

				coeffs[j].Add(u, v)
				if coeffs[j].Cmp(r.modulus) >= 0 {
					coeffs[j].Sub(coeffs[j], r.modulus)
				}

				coeffs[j+t].Sub(u, v)
				if coeffs[j+t].Sign() < 0 {
					coeffs[j+t].Add(coeffs[j+t], r.modulus)
				}
			}
		}
	}

	num.BitReverseInPlace(coeffs)
}

// InvNTTInPlace computes the inverse NTT of a bigint vector in-place,
// without normalization.
func (r *BigRing) InvNTTInPlace(coeffs []*big.Int) {
	num.BitReverseInPlace(coeffs)

	u, v := big.NewInt(0), big.NewInt(0)

	t := 1
	for m := r.degree >> 1; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				u.Set(coeffs[j])
				v.Set(coeffs[j+t])

				coeffs[j].Add(u, v)
				if coeffs[j].Cmp(r.modulus) >= 0 {
					coeffs[j].Sub(coeffs[j], r.modulus)
				}

				coeffs[j+t].Sub(u, v)
				coeffs[j+t].Mul(coeffs[j+t], r.twInv[m+i])
				coeffs[j+t].Mod(coeffs[j+t], r.modulus)
			}
		}
		t <<= 1
	}

}

// NormalizeInPlace normalizes a vector of bigints in-place.
func (r *BigRing) NormalizeInPlace(coeffs []*big.Int) {
	for i := 0; i < r.degree; i++ {
		coeffs[i].Mul(coeffs[i], r.degreeInv)
		coeffs[i].Mod(coeffs[i], r.modulus)
	}
}
