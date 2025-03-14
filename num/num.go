// Package num implements various utility functions regarding numeric types.
package num

// ModInverse returns the modular inverse of x modulo m.
// Output is always positive.
// Panics if x and m are not coprime.
func ModInverse(x, m uint64) uint64 {
	x %= m

	a, b := x, m
	u, v := uint64(1), uint64(0)
	for b != 0 {
		q := a / b
		a, b = b, a-q*b
		u, v = v, u-q*v
	}

	if a != 1 {
		panic("modular inverse does not exist")
	}

	return u % m
}

// ModExp returns x^y mod q.
func ModExp(x, y, q uint64) uint64 {
	r := uint64(1)
	x %= q
	for y > 0 {
		if y&1 == 1 {
			r = (r * x) % q
		}
		x = (x * x) % q
		y >>= 1
	}
	return r
}

// BitReverseInPlace reorders v into bit-reversal order in-place.
func BitReverseInPlace[T any](v []T) {
	var bit, j int
	for i := 1; i < len(v); i++ {
		bit = len(v) >> 1
		for j >= bit {
			j -= bit
			bit >>= 1
		}
		j += bit
		if i < j {
			v[i], v[j] = v[j], v[i]
		}
	}
}
