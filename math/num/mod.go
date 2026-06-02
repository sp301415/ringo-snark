package num

import (
	"cmp"
	"fmt"
	"math/bits"

	"github.com/sp301415/ringo-snark/math/internal/modops"
)

const (
	// MaxModulusBits equals to log2(MaxModulus).
	// See [MaxModulus] for details.
	MaxModulusBits = 50
	// MaxModulus is the maximum possible modulus value for the reduction.
	// All numbers in HIENAA are assumed to be less than this value.
	MaxModulus = 1 << MaxModulusBits
)

// Modulus holds precomputed constants for efficient modulus reduction.
type Modulus struct {
	// modulus is the raw modulus value.
	modulus uint64

	// divHi is a constant used for Barrett reduction.
	// Equals to floor(2^128 / modulus).
	divHi uint64
	// divLo is a constant used for Barrett reduction.
	// Equals to floor(2^128 / modulus).
	divLo uint64
}

// NewModulus creates a new [Modulus].
func NewModulus[T Integer](mod T) *Modulus {
	if mod <= 1 {
		panic("modulus must be greater than 1")
	} else if uint64(mod) >= MaxModulus {
		panic("modulus must be less than MaxModulus")
	}

	q := uint64(mod)

	var divHi, divLo, rem uint64
	divHi, rem = bits.Div64(1, 0, q)
	divLo, _ = bits.Div64(rem, 0, q)

	return &Modulus{
		modulus: q,

		divHi: divHi,
		divLo: divLo,
	}
}

// Value returns the modulus value.
func (q *Modulus) Value() uint64 {
	return q.modulus
}

// Div is a constant used for Barrett reduction.
// Equals to floor(2^128 / modulus).
func (q *Modulus) Div() (hi, lo uint64) {
	return q.divHi, q.divLo
}

// String implements the [fmt.Stringer] interface.
func (q *Modulus) String() string {
	return fmt.Sprintf("%v", q.modulus)
}

// Add returns x0 + x1 mod q.
// x0 and x1 must be in [0, q).
// If q is nil, then it returns x0 + x1.
func Add(x0, x1 uint64, q *Modulus) uint64 {
	if q != nil {
		return modops.Add(x0, x1, q.modulus)
	}
	return x0 + x1
}

// Sub returns x0 - x1 mod q.
// x0 and x1 must be in [0, q).
// If q is nil, then it returns x0 - x1.
func Sub(x0, x1 uint64, q *Modulus) uint64 {
	if q != nil {
		return modops.Sub(x0, x1, q.modulus)
	}
	return x0 - x1
}

// Neg returns -x mod q.
// x must be in [0, q).
// If q is nil, then it returns -x.
func Neg(x uint64, q *Modulus) uint64 {
	if q != nil {
		return modops.Neg(x, q.modulus)
	}
	return -x
}

// Mul returns x0 * x1 mod q using Barrett reduction.
// If q is nil, then it returns x0 * x1.
func Mul(x0, x1 uint64, q *Modulus) uint64 {
	if q != nil {
		return modops.BMul(x0, x1, q.modulus, q.divHi, q.divLo)
	}
	return x0 * x1
}

// MulLazy returns x0 * x1 mod q using Barrett reduction,
// but the result is in [0, 2q).
//
// Panics if q is nil.
func MulLazy(x0, x1 uint64, q *Modulus) uint64 {
	return modops.BMulLazy(x0, x1, q.modulus, q.divHi, q.divLo)
}

// Reduce returns x mod q using Barrett reduction.
//
// Panics if q is nil.
func Reduce[T Integer](x T, q *Modulus) uint64 {
	return modops.BMod(x, q.modulus, q.divHi)
}

// Reduce128 returns x mod q using Barrett reduction.
//
// Panics if q is nil.
func Reduce128(xHi, xLo uint64, q *Modulus) uint64 {
	return modops.BMod128(xHi, xLo, q.modulus, q.divHi, q.divLo)
}

// Reduce128Lazy returns x mod q using Barret reduction,
// but the result is in [0, 2q).
//
// Panics if q is nil.
func Reduce128Lazy(xHi, xLo uint64, q *Modulus) uint64 {
	return modops.BMod128Lazy(xHi, xLo, q.modulus, q.divHi, q.divLo)
}

// SForm transforms x into Shoup form.
//
// Panics if q is nil.
func SForm(x uint64, q *Modulus) uint64 {
	return modops.SForm(x, q.modulus)
}

// SMul returns x0 * x1 mod q using Shoup multiplication.
//
// Panics if q is nil.
func SMul(x0, x1, x1S uint64, q *Modulus) uint64 {
	return modops.SMul(x0, x1, x1S, q.modulus)
}

// SMulLazy returns x0 * x1 mod q using Shoup multiplication,
// but the result is in [0, 2q).
//
// Panics if q is nil.
func SMulLazy(x0, x1, x1S uint64, q *Modulus) uint64 {
	return modops.SMulLazy(x0, x1, x1S, q.modulus)
}

// Exp returns x^e mod q.
// If q is nil, then it returns x^e.
func Exp(x, e uint64, q *Modulus) uint64 {
	switch e {
	case 0:
		return 1
	case 1:
		return x
	}

	r := uint64(1)
	if q == nil {
		for e > 0 {
			if e%2 == 1 {
				r = r * x
			}
			e >>= 1
			x = x * x
		}
	} else {
		for e > 0 {
			if e%2 == 1 {
				r = Mul(r, x, q)
			}
			e >>= 1
			x = Mul(x, x, q)
		}
	}

	return r
}

// Inv returns the inverse of x modulo q.
//
// Panics if q is nil.
func Inv(x uint64, q *Modulus) uint64 {
	rr, r := x, q.Value()

	ssSign, sSign := true, true
	ss, s := uint64(1), uint64(0)

	for r != 0 {
		quo := rr / r
		rr, r = r, rr-quo*r
		if sSign != ssSign {
			ss, s = s, ss+quo*s
			ssSign, sSign = sSign, ssSign
		} else {
			if ss > quo*s {
				ss, s = s, ss-quo*s
				ssSign, sSign = sSign, ssSign
			} else {
				ss, s = s, quo*s-ss
				ssSign, sSign = sSign, !sSign
			}
		}
	}

	if rr != 1 {
		panic("input not invertible")
	}

	if !ssSign {
		return q.Value() - ss
	}
	return ss
}

// CmpModulus implements [cmp.Ordered] functionality for [Modulus].
func CmpModulus(a, b *Modulus) int {
	return cmp.Compare(a.Value(), b.Value())
}
