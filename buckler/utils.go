package buckler

import (
	"math"
	"math/big"
)

// getDcmpBase returns the base for the decomposition.
func getDcmpBase(n uint64) []uint64 {
	dcmpLen := int(math.Floor(math.Log2(float64(n)))) + 1
	base := make([]uint64, dcmpLen)

	for i := 0; i < dcmpLen-1; i++ {
		var sum uint64
		for j := 0; j < i; j++ {
			sum += base[j]
		}

		base[i] = ((n - sum) >> 1) + ((n - sum) & 1)
	}
	base[dcmpLen-1] = 1

	return base
}

// bigSignedDecompose ternary decomposes x.
func bigSignedDecompose(x *big.Int, q *big.Int, base []uint64) []*big.Int {
	dcmp := make([]*big.Int, len(base))

	v := big.NewInt(0).Set(x)
	qHalf := big.NewInt(0).Rsh(q, 1)
	if v.Cmp(qHalf) > 0 {
		v.Sub(v, q)
	}

	for i := 0; i < len(dcmp); i++ {
		b := big.NewInt(0).SetUint64(base[i])
		bNeg := big.NewInt(0).Neg(b)

		if v.Cmp(b) >= 0 {
			dcmp[i] = big.NewInt(1)
			v.Sub(v, b)
		} else if v.Cmp(bNeg) <= 0 {
			dcmp[i] = big.NewInt(-1)
			v.Add(v, b)
		} else {
			dcmp[i] = big.NewInt(0)
		}
	}

	return dcmp
}
