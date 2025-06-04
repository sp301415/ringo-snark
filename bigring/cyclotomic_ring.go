package bigring

import (
	"math/big"

	"github.com/sp301415/ringo-snark/num"
)

type ringBuffer struct {
	u    *big.Int
	v    *big.Int
	uOut *big.Int
	vOut *big.Int
}

// CyclotomicRing is a cyclotomic ring.
type CyclotomicRing struct {
	*baseBigRing

	root      *big.Int
	tw        []*big.Int
	twInv     []*big.Int
	degreeInv *big.Int

	buffer ringBuffer
}

// NewCyclotomicRing creates a new CyclotomicRing with the given degree and modulus.
func NewCyclotomicRing(N int, Q *big.Int) *CyclotomicRing {
	QSubOne := big.NewInt(0).Sub(Q, big.NewInt(1))
	if big.NewInt(0).Mod(QSubOne, big.NewInt(int64(2*N))).Sign() != 0 {
		panic("no 2Nth root of unity")
	}

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

	return NewCyclotomicRingFromRoot(N, Q, g)
}

// NewCyclotomicRingFromRoot creates a new CyclotomicRing from a given primitive 2Nth root of unity.
func NewCyclotomicRingFromRoot(N int, Q *big.Int, root *big.Int) *CyclotomicRing {
	rootPowN := big.NewInt(0).Exp(root, big.NewInt(int64(N)), Q)
	rootPow2N := big.NewInt(0).Exp(root, big.NewInt(int64(2*N)), Q)
	if rootPowN.Cmp(big.NewInt(1)) == 0 || rootPow2N.Cmp(big.NewInt(1)) != 0 {
		panic("root is not a primitive 2Nth root of unity")
	}

	tw := make([]*big.Int, N)
	twInv := make([]*big.Int, N)
	for i := 0; i < N; i++ {
		tw[i] = big.NewInt(0).Exp(root, big.NewInt(int64(i)), Q)
		twInv[i] = big.NewInt(0).Exp(root, big.NewInt(int64(2*N-i)), Q)
	}
	num.BitReverseInPlace(tw)
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(N)), Q)

	return &CyclotomicRing{
		baseBigRing: newBaseRing(N, Q),

		root:      root,
		tw:        tw,
		twInv:     twInv,
		degreeInv: degreeInv,

		buffer: ringBuffer{
			u:    big.NewInt(0),
			v:    big.NewInt(0),
			uOut: big.NewInt(0),
			vOut: big.NewInt(0),
		},
	}
}

// ShallowCopy creates a shallow copy of CyclotomicRing that is thread-safe.
func (r *CyclotomicRing) ShallowCopy() *CyclotomicRing {
	return &CyclotomicRing{
		baseBigRing: r.baseBigRing.ShallowCopy(),

		root:      r.root,
		tw:        r.tw,
		twInv:     r.twInv,
		degreeInv: r.degreeInv,

		buffer: ringBuffer{
			u:    big.NewInt(0),
			v:    big.NewInt(0),
			uOut: big.NewInt(0),
			vOut: big.NewInt(0),
		},
	}
}

// TwoNthRoot returns the 2Nth primitive root of unity.
func (r *CyclotomicRing) TwoNthRoot() *big.Int {
	return r.root
}

// ToNTTPoly computes NTT of p.
func (r *CyclotomicRing) ToNTTPoly(p BigPoly) BigNTTPoly {
	pOut := r.NewNTTPoly()
	r.ToNTTPolyAssign(p, pOut)
	return pOut
}

// ToNTTPolyAssign computes NTT of p and assigns it to pOut.
func (r *CyclotomicRing) ToNTTPolyAssign(p BigPoly, pOut BigNTTPoly) {
	for i := 0; i < r.degree; i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.NTTInPlace(pOut.Coeffs)
}

// ToPoly computes inverse NTT of p.
func (r *CyclotomicRing) ToPoly(p BigNTTPoly) BigPoly {
	pOut := r.NewPoly()
	r.ToPolyAssign(p, pOut)
	return pOut
}

// ToPolyAssign computes inverse NTT of p and assigns it to pOut.
func (r *CyclotomicRing) ToPolyAssign(p BigNTTPoly, pOut BigPoly) {
	for i := 0; i < pOut.Degree(); i++ {
		pOut.Coeffs[i].Set(p.Coeffs[i])
	}
	r.InvNTTInPlace(pOut.Coeffs)
	r.NormalizeInPlace(pOut.Coeffs)
}

// NTTInPlace computes the NTT of a bigint vector in-place.
func (r *CyclotomicRing) NTTInPlace(coeffs []*big.Int) {
	t := r.degree
	for m := 1; m < r.degree; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				r.buffer.u.Set(coeffs[j])
				r.buffer.v.Set(coeffs[j+t])

				r.buffer.vOut.Mul(r.buffer.v, r.tw[m+i])
				r.Reduce(r.buffer.vOut)

				coeffs[j].Add(r.buffer.u, r.buffer.vOut)
				if coeffs[j].Cmp(r.modulus) >= 0 {
					coeffs[j].Sub(coeffs[j], r.modulus)
				}

				coeffs[j+t].Sub(r.buffer.u, r.buffer.vOut)
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
func (r *CyclotomicRing) InvNTTInPlace(coeffs []*big.Int) {
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

				r.buffer.vOut.Sub(r.buffer.u, r.buffer.v)
				coeffs[j+t].Mul(r.buffer.vOut, r.twInv[m+i])
				r.Reduce(coeffs[j+t])
			}
		}
		t <<= 1
	}
}

// NormalizeInPlace normalizes a vector of bigints in-place.
func (r *CyclotomicRing) NormalizeInPlace(coeffs []*big.Int) {
	for i := 0; i < r.degree; i++ {
		r.buffer.u.Set(coeffs[i])
		coeffs[i].Mul(r.buffer.u, r.degreeInv)
		r.Reduce(coeffs[i])
	}
}
