package celpc

import (
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

func toBalanced(x uint64, q uint64) int64 {
	if x > q>>1 {
		return int64(x) - int64(q)
	}
	return int64(x)
}

// polyToBigIntCenteredAssign converts a polynomial to a big.Int vector.
func polyToBigIntCenteredAssign(params Parameters, p ring.Poly, v []*big.Int) {
	pInv := params.ringQ.NewPoly()
	params.ringQ.IMForm(p, pInv)
	params.ringQ.INTT(pInv, pInv)

	qFull := params.ringQ.Modulus()
	qHalf := big.NewInt(0).Rsh(qFull, 1)

	c := big.NewInt(0)
	for i := 0; i < params.ringQ.N(); i++ {
		isSmall := true
		cInt64 := toBalanced(pInv.Coeffs[0][i], params.ringQ.SubRings[0].Modulus)
		for j := 1; j <= params.ringQ.Level(); j++ {
			if cInt64 != toBalanced(pInv.Coeffs[j][i], params.ringQ.SubRings[j].Modulus) {
				isSmall = false
				break
			}
		}

		if isSmall {
			v[i].SetInt64(cInt64)
			continue
		}

		v[i].SetInt64(0)
		for j := 0; j <= params.ringQ.Level(); j++ {
			c.SetUint64(pInv.Coeffs[j][i])
			c.Mul(c, params.rnsGadget[j])
			v[i].Add(v[i], c)
		}
		v[i].Mod(v[i], qFull)
		if v[i].Cmp(qHalf) == 1 {
			v[i].Sub(v[i], qFull)
		}
	}
}
