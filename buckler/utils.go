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
