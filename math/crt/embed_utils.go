package crt

import (
	"github.com/sp301415/ringo-snark/math/num"
)

// embedToModOut returns sign(x) mod qOut for x in [0, qIn).
func embedToModOut(x uint64, qOut *num.Modulus, qIn, halfQIn uint64) uint64 {
	if x <= halfQIn {
		return num.Reduce(x, qOut)
	}
	return num.Neg(num.Reduce(qIn-x, qOut), qOut)
}

// isMixedRadixNegative checks if i-th index of v is negative in signed mixed radix representation.
func isMixedRadixNegative(v [][]uint64, i int, modInHalf []uint64) uint64 {
	for j := len(v) - 1; j >= 0; j-- {
		x := v[j][i]
		qHalf := modInHalf[j]

		if x > qHalf {
			return 1
		}
		if x < qHalf {
			return 0
		}
	}
	return 0
}
