package bigring

import (
	"math/big"

	"github.com/sp301415/ringo-snark/num"
)

// BigRing is a negacyclic ring.
type BigRing struct {
	degree      int
	modulus     *big.Int
	barretConst *big.Int
	qBitLen     uint

	tw        []*big.Int
	twInv     []*big.Int
	degreeInv *big.Int

	buffer ringBuffer
}

type ringBuffer struct {
	quo *big.Int
	u   *big.Int
	v   *big.Int

	mul *big.Int
}

// NewBigRing creates a new BigRing.
func NewBigRing(N int, Q *big.Int) *BigRing {
	QSubOne := big.NewInt(0).Sub(Q, big.NewInt(1))
	if big.NewInt(0).Mod(QSubOne, big.NewInt(int64(2*N))).Sign() != 0 {
		panic("no 2Nth root of unity")
	}

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

	barretExp := big.NewInt(0).Lsh(big.NewInt(1), uint(2*Q.BitLen()))
	barretConst := big.NewInt(0).Div(barretExp, Q)

	return &BigRing{
		degree:      N,
		modulus:     Q,
		barretConst: barretConst,
		qBitLen:     uint(Q.BitLen()),

		tw:        tw,
		twInv:     twInv,
		degreeInv: degreeInv,

		buffer: newRingBuffer(Q),
	}
}

// newRingBuffer creates a new ringBuffer.
func newRingBuffer(Q *big.Int) ringBuffer {
	return ringBuffer{
		quo: big.NewInt(0).Set(Q),
		u:   big.NewInt(0).Set(Q),
		v:   big.NewInt(0).Set(Q),
		mul: big.NewInt(0).Set(Q),
	}
}

// ShallowCopy creates a copy of BigRing that is thread-safe.
func (r *BigRing) ShallowCopy() *BigRing {
	return &BigRing{
		degree:      r.degree,
		modulus:     r.modulus,
		barretConst: r.barretConst,
		qBitLen:     r.qBitLen,

		tw:        r.tw,
		twInv:     r.twInv,
		degreeInv: r.degreeInv,

		buffer: newRingBuffer(r.modulus),
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

// Mod reduces x using Barrett reduction.
func (r *BigRing) Mod(x *big.Int) {
	r.buffer.quo.Mul(x, r.barretConst)
	r.buffer.quo.Rsh(r.buffer.quo, r.qBitLen<<1)
	r.buffer.quo.Mul(r.buffer.quo, r.modulus)
	x.Sub(x, r.buffer.quo)
	if x.Cmp(r.modulus) >= 0 {
		x.Sub(x, r.modulus)
	}
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
	t := r.degree
	for m := 1; m < r.degree; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				r.buffer.u.Set(coeffs[j])
				r.buffer.v.Set(coeffs[j+t])

				r.buffer.v.Mul(r.buffer.v, r.tw[m+i])
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
func (r *BigRing) InvNTTInPlace(coeffs []*big.Int) {
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
				coeffs[j+t].Mul(coeffs[j+t], r.twInv[m+i])
				r.Mod(coeffs[j+t])
			}
		}
		t <<= 1
	}
}

// NormalizeInPlace normalizes a vector of bigints in-place.
func (r *BigRing) NormalizeInPlace(coeffs []*big.Int) {
	for i := 0; i < r.degree; i++ {
		coeffs[i].Mul(coeffs[i], r.degreeInv)
		r.Mod(coeffs[i])
	}
}
