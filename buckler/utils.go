package buckler

import (
	"math/big"
)

func decomposeBase(x *big.Int) []*big.Int {
	one := big.NewInt(1)

	dcmpLen := x.BitLen()
	if new(big.Int).Lsh(one, x.TrailingZeroBits()).Cmp(x) == 0 {
		dcmpLen -= 1
	}

	base := make([]*big.Int, dcmpLen)
	b, quo, rem := new(big.Int), new(big.Int), new(big.Int)
	for i := 0; i < dcmpLen-1; i++ {
		sum := new(big.Int)
		for j := 0; j < i; j++ {
			sum.Add(sum, base[j])
		}

		b.Sub(x, sum)
		quo.Rsh(b, 1)
		rem.And(b, one)

		base[i] = new(big.Int).Add(quo, rem)
	}

	base[dcmpLen-1] = new(big.Int).Set(one)
	return base
}

func decomposeBig(x *big.Int, base []*big.Int, q *big.Int) []int64 {
	xSigned := new(big.Int).Set(x)
	qHalf := new(big.Int).Rsh(q, 1)
	if xSigned.Cmp(qHalf) > 0 {
		xSigned.Sub(xSigned, q)
	}

	dcmpOut := make([]int64, len(base))
	for i := range base {
		baseNeg := new(big.Int).Neg(base[i])
		switch {
		case xSigned.Cmp(base[i]) >= 0:
			dcmpOut[i] = 1
			xSigned.Sub(xSigned, base[i])
		case xSigned.Cmp(baseNeg) <= 0:
			dcmpOut[i] = -1
			xSigned.Add(xSigned, base[i])
		default:
			dcmpOut[i] = 0
		}
	}
	return dcmpOut
}
