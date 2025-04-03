package buckler

import (
	"math/big"
	"slices"
)

// bigSignedDecompose ternary decomposes x.
func bigSignedDecompose(x *big.Int, q *big.Int, n int) []*big.Int {
	dcmp := make([]*big.Int, n+1)
	v := big.NewInt(0).Set(x)

	qHalf := big.NewInt(0).Rsh(q, 1)
	if v.Cmp(qHalf) > 0 {
		v.Sub(v, q)
	}

	for i := 0; i < n; i++ {
		b := big.NewInt(0).Lsh(big.NewInt(1), uint(n-1-i))
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

	b := big.NewInt(1)
	bNeg := big.NewInt(-1)
	if v.Cmp(b) >= 0 {
		dcmp[n] = big.NewInt(1)
	} else if v.Cmp(bNeg) <= 0 {
		dcmp[n] = big.NewInt(-1)
	} else {
		dcmp[n] = big.NewInt(0)
	}

	slices.Reverse(dcmp)

	return dcmp
}
