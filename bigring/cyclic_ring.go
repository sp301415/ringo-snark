package bigring

import (
	"math/big"

	"github.com/sp301415/ringo-snark/num"
)

// CyclicRing is a cyclic ring.
type CyclicRing struct {
	*baseBigRing

	root      *big.Int
	tw        []*big.Int
	twInv     []*big.Int
	degreeInv *big.Int

	buffer ringBuffer
}

// NewCyclicRing creates a new CyclicRing with the given degree and modulus.
func NewCyclicRing(N int, Q *big.Int) *CyclicRing {
	QSubOne := big.NewInt(0).Sub(Q, big.NewInt(1))
	if big.NewInt(0).Mod(QSubOne, big.NewInt(int64(2*N))).Sign() != 0 {
		panic("no 2Nth root of unity")
	}

	exp1 := big.NewInt(0).Sub(Q, big.NewInt(1))
	exp1.Div(exp1, big.NewInt(int64(N)))
	exp2 := big.NewInt(int64(N / 2))
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(Q) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, Q)
		gPow := big.NewInt(0).Exp(g, exp2, Q)
		if gPow.Cmp(big.NewInt(1)) != 0 {
			break
		}
	}

	return NewCyclicRingFromRoot(N, Q, g)
}

// NewCyclicRingFromRoot creates a new CyclicRing from a given primitive Nth root of unity.
func NewCyclicRingFromRoot(N int, Q *big.Int, root *big.Int) *CyclicRing {
	rootPowNHalf := big.NewInt(0).Exp(root, big.NewInt(int64(N/2)), Q)
	rootPowN := big.NewInt(0).Exp(root, big.NewInt(int64(N)), Q)
	if rootPowNHalf.Cmp(big.NewInt(1)) == 0 || rootPowN.Cmp(big.NewInt(1)) != 0 {
		panic("root is not a primitive Nth root of unity")
	}

	tw := make([]*big.Int, N/2)
	twInv := make([]*big.Int, N/2)
	for i := 0; i < N/2; i++ {
		tw[i] = big.NewInt(0).Exp(root, big.NewInt(int64(i)), Q)
		twInv[i] = big.NewInt(0).Exp(root, big.NewInt(int64(N-i)), Q)
	}
	num.BitReverseInPlace(tw)
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(N)), Q)

	return &CyclicRing{
		baseBigRing: newBaseRing(N, Q),

		root:      root,
		tw:        tw,
		twInv:     twInv,
		degreeInv: degreeInv,

		buffer: ringBuffer{
			u: big.NewInt(0),
			v: big.NewInt(0),
		},
	}
}

// ShallowCopy creates a shallow copy of CyclicRing that is thread-safe.
func (r *CyclicRing) ShallowCopy() *CyclicRing {
	return &CyclicRing{
		baseBigRing: r.baseBigRing.ShallowCopy(),

		root:      r.root,
		tw:        r.tw,
		twInv:     r.twInv,
		degreeInv: r.degreeInv,

		buffer: ringBuffer{
			u: big.NewInt(0),
			v: big.NewInt(0),
		},
	}
}

// TwoNthRoot returns the Nth primitive root of unity.
func (r *CyclicRing) NthRoot() *big.Int {
	return r.root
}

// ToNTTPoly computes NTT of p.
func (r *CyclicRing) ToNTTPoly(p BigPoly) BigNTTPoly {
	pOut := r.NewNTTPoly()
	r.ToNTTPolyAssign(p, pOut)
	return pOut
}

// ToNTTPolyAssign computes NTT of p and assigns it to pOut.
func (r *CyclicRing) ToNTTPolyAssign(p BigPoly, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.NTTInPlace(pOut.Coeffs)
}

// ToPoly computes inverse NTT of p.
func (r *CyclicRing) ToPoly(p BigNTTPoly) BigPoly {
	pOut := r.NewPoly()
	r.ToPolyAssign(p, pOut)
	return pOut
}

// ToPolyAssign computes inverse NTT of p and assigns it to pOut.
func (r *CyclicRing) ToPolyAssign(p BigNTTPoly, pOut BigPoly) {
	for i := 0; i < pOut.Degree(); i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.InvNTTInPlace(pOut.Coeffs)
	r.NormalizeInPlace(pOut.Coeffs)
}

// NTTInPlace computes the NTT of a bigint vector in-place.
func (r *CyclicRing) NTTInPlace(coeffs []*big.Int) {
	t := r.degree
	for m := 1; m < r.degree; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				r.buffer.u.Set(coeffs[j])
				r.buffer.v.Set(coeffs[j+t])

				r.buffer.v.Mul(r.buffer.v, r.tw[i])
				r.Mod(r.buffer.v)

				coeffs[j].Add(r.buffer.u, r.buffer.v)
				if coeffs[j].Cmp(r.modulus) >= 0 {
					coeffs[j].Sub(coeffs[j], r.modulus)
				}

				coeffs[j+t].Sub(r.buffer.u, r.buffer.v)
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
func (r *CyclicRing) InvNTTInPlace(coeffs []*big.Int) {
	num.BitReverseInPlace(coeffs)

	t := 1
	for m := r.degree >> 1; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				r.buffer.u.Set(coeffs[j])
				r.buffer.v.Set(coeffs[j+t])

				coeffs[j].Add(r.buffer.u, r.buffer.v)
				if coeffs[j].Cmp(r.modulus) >= 0 {
					coeffs[j].Sub(coeffs[j], r.modulus)
				}

				coeffs[j+t].Sub(r.buffer.u, r.buffer.v)
				coeffs[j+t].Add(coeffs[j+t], r.modulus)
				coeffs[j+t].Mul(coeffs[j+t], r.twInv[i])
				r.Mod(coeffs[j+t])
			}
		}
		t <<= 1
	}
}

// NormalizeInPlace normalizes a vector of bigints in-place.
func (r *CyclicRing) NormalizeInPlace(coeffs []*big.Int) {
	for i := 0; i < r.degree; i++ {
		coeffs[i].Mul(coeffs[i], r.degreeInv)
		r.Mod(coeffs[i])
	}
}
