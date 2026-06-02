// Package modops implements modular arithmetic operations for internal usage.
package modops

import (
	"math"
	"math/bits"
)

// Unsigned represents the unsigned Integer type.
type Unsigned interface {
	~uint | ~uint8 | ~uint16 | ~uint32 | ~uint64
}

// Integer represents the Integer type.
type Integer interface {
	Unsigned | ~int | ~int8 | ~int16 | ~int32 | ~int64
}

// Add returns x0 + x1 mod q.
func Add(x0, x1, q uint64) uint64 {
	xOut := x0 + x1
	if xOut >= q {
		xOut -= q
	}
	return xOut
}

// Sub returns x0 - x1 mod q.
func Sub(x0, x1, q uint64) uint64 {
	xOut := x0 - x1
	if xOut >= q {
		xOut += q
	}
	return xOut
}

// Neg returns -x mod q.
func Neg(x, q uint64) uint64 {
	if x == 0 {
		return 0
	}
	return q - x
}

// BMul returns x0 * x1 mod q using Barrett reduction.
func BMul(x0, x1, q, divHi, divLo uint64) uint64 {
	xOutHi, xOutLo := bits.Mul64(x0, x1)

	quo := xOutHi * divHi

	quoLo, _ := bits.Mul64(xOutLo, divLo)

	quoMid0, quoMid0Lo := bits.Mul64(xOutLo, divHi)
	quo += quoMid0

	quoMid1, quoMid1Lo := bits.Mul64(xOutHi, divLo)
	quo += quoMid1

	quoMidSum, quoMidCarry := bits.Add64(quoMid0Lo, quoMid1Lo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	_, quoMidCarry = bits.Add64(quoMidSum, quoLo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	xOut := xOutLo - quo*q
	if xOut >= q {
		xOut -= q
	}
	return xOut
}

// BMulLazy returns x0 * x1 mod q using Barrett reduction,
// but the result is in [0, 2q).
func BMulLazy(x0, x1, q, divHi, divLo uint64) uint64 {
	xOutHi, xOutLo := bits.Mul64(x0, x1)

	quo := xOutHi * divHi

	quoLo, _ := bits.Mul64(xOutLo, divLo)

	quoMid0, quoMid0Lo := bits.Mul64(xOutLo, divHi)
	quo += quoMid0

	quoMid1, quoMid1Lo := bits.Mul64(xOutHi, divLo)
	quo += quoMid1

	quoMidSum, quoMidCarry := bits.Add64(quoMid0Lo, quoMid1Lo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	_, quoMidCarry = bits.Add64(quoMidSum, quoLo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	return xOutLo - quo*q
}

// BMod128 returns x mod q using Barrett reduction.
func BMod128(xHi, xLo, q, divHi, divLo uint64) uint64 {
	quo := xHi * divHi

	quoLo, _ := bits.Mul64(xLo, divLo)

	quoMid0, quoMid0Lo := bits.Mul64(xLo, divHi)
	quo += quoMid0

	quoMid1, quoMid1Lo := bits.Mul64(xHi, divLo)
	quo += quoMid1

	quoMidSum, quoMidCarry := bits.Add64(quoMid0Lo, quoMid1Lo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	_, quoMidCarry = bits.Add64(quoMidSum, quoLo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	xOut := xLo - quo*q
	if xOut >= q {
		xOut -= q
	}
	return xOut
}

// BMod128Lazy returns x mod q using Barrett reduction,
// but the result is in [0, 2q).
func BMod128Lazy(xHi, xLo, q, divHi, divLo uint64) uint64 {
	quo := xHi * divHi

	quoLo, _ := bits.Mul64(xLo, divLo)

	quoMid0, quoMid0Lo := bits.Mul64(xLo, divHi)
	quo += quoMid0

	quoMid1, quoMid1Lo := bits.Mul64(xHi, divLo)
	quo += quoMid1

	quoMidSum, quoMidCarry := bits.Add64(quoMid0Lo, quoMid1Lo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	_, quoMidCarry = bits.Add64(quoMidSum, quoLo, 0)
	quo, _ = bits.Add64(quo, 0, quoMidCarry)

	return xLo - quo*q
}

// BMod64 returns x mod q using Barrett reduction.
func BMod64(x, q, divHi uint64) uint64 {
	quo, _ := bits.Mul64(x, divHi)
	xOut := x - quo*q
	if xOut >= q {
		xOut -= q
	}
	return xOut
}

// BMod returns x mod q using Barrett reduction.
func BMod[T Integer](x T, q, divHi uint64) uint64 {
	if x < 0 {
		return Neg(BMod64(uint64(-x), q, divHi), q)
	}
	return BMod64(uint64(x), q, divHi)
}

// SForm transforms x into Shoup form.
func SForm(x, q uint64) uint64 {
	xS, _ := bits.Div64(x, 0, q)
	return xS
}

// SMul returns x0 * x1 mod q using Shoup multiplication.
func SMul(x0, x1, x1S, q uint64) uint64 {
	quo, _ := bits.Mul64(x0, x1S)

	xOut := x0*x1 - quo*q
	if xOut >= q {
		xOut -= q
	}
	return xOut
}

// SMulLazy returns x0 * x1 mod q using Shoup multiplication,
// but the result is in [0, 2q).
func SMulLazy(x0, x1, x1S, q uint64) uint64 {
	quo, _ := bits.Mul64(x0, x1S)

	return x0*x1 - quo*q
}

// FMul returns x0 * x1 mod q using float64 multiplication.
// It assumes x0, x1 are in [0, q) and q < 2^50.
func FMul(x0, x1, q uint64) uint64 {
	eps := math.Nextafter(1, 2) - 1

	qf := float64(q)
	qfInv := (1 + eps) / qf

	x0f := math.Ceil(float64(x0))
	x1f := math.Ceil(float64(x1))

	hi := x0f * x1f
	lo := math.FMA(x0f, x1f, -hi)

	quo := math.Floor(hi * qfInv)
	rem := -math.FMA(quo, qf, -hi)

	xOutf := rem + lo
	if xOutf < 0 {
		xOutf += qf
	}

	return uint64(math.Ceil(xOutf))
}
