package bigring

import (
	"math/big"
)

type baseBigRing struct {
	degree      int
	modulus     *big.Int
	barretConst *big.Int
	qBitLen     uint

	buffer baseRingBuffer
}

type baseRingBuffer struct {
	quo *big.Int
	mul *big.Int
}

func newBaseRing(N int, Q *big.Int) *baseBigRing {
	barretExp := big.NewInt(0).Lsh(big.NewInt(1), uint((Q.BitLen()<<1)+1))
	barretConst := big.NewInt(0).Quo(barretExp, Q)

	return &baseBigRing{
		degree:      N,
		modulus:     Q,
		barretConst: barretConst,
		qBitLen:     uint(Q.BitLen()),

		buffer: baseRingBuffer{
			quo: big.NewInt(0).Set(Q),
			mul: big.NewInt(0).Set(Q),
		},
	}
}

// ShallowCopy creates a shallow copy of baseBigRing that is thread-safe.
func (r *baseBigRing) ShallowCopy() *baseBigRing {
	return &baseBigRing{
		degree:      r.degree,
		modulus:     r.modulus,
		barretConst: r.barretConst,
		qBitLen:     r.qBitLen,

		buffer: baseRingBuffer{
			quo: big.NewInt(0),
			mul: big.NewInt(0),
		},
	}
}

// Degree returns the degree of the BigRing.
func (r *baseBigRing) Degree() int {
	return r.degree
}

// Modulus returns the modulus of the BigRing.
func (r *baseBigRing) Modulus() *big.Int {
	return r.modulus
}

// NewPoly creates a new BigPoly.
func (r *baseBigRing) NewPoly() BigPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigPoly{Coeffs: coeffs}
}

// NewNTTPoly creates a new BigNTTPoly.
func (r *baseBigRing) NewNTTPoly() BigNTTPoly {
	coeffs := make([]*big.Int, r.degree)
	for i := 0; i < r.degree; i++ {
		coeffs[i] = big.NewInt(0)
	}
	return BigNTTPoly{Coeffs: coeffs}
}

// Mod reduces x using Barrett reduction.
func (r *baseBigRing) Mod(x *big.Int) {
	if x.Sign() < 0 {
		x.Mod(x, r.modulus)
		return
	}

	r.buffer.quo.Mul(x, r.barretConst)
	r.buffer.quo.Rsh(r.buffer.quo, (r.qBitLen<<1)+1)
	r.buffer.quo.Mul(r.buffer.quo, r.modulus)
	x.Sub(x, r.buffer.quo)
	if x.Cmp(r.modulus) >= 0 {
		x.Sub(x, r.modulus)
	}
}
