package buckler

import (
	"math/big"
)

func getDecomposeBase(n *big.Int) []*big.Int {
	dcmpLen := n.BitLen()
	if big.NewInt(0).And(n, big.NewInt(0).Sub(n, big.NewInt(1))).Sign() == 0 {
		dcmpLen -= 1
	}

	base := make([]*big.Int, dcmpLen)

	for i := 0; i < dcmpLen-1; i++ {
		sum := big.NewInt(0)
		for j := 0; j < i; j++ {
			sum.Add(sum, base[j])
		}

		b := big.NewInt(0).Sub(n, sum)
		quo := big.NewInt(0).Rsh(b, 1)
		rem := big.NewInt(0).And(b, big.NewInt(1))

		base[i] = big.NewInt(0).Add(quo, rem)
	}

	base[dcmpLen-1] = big.NewInt(1)
	return base
}

func (p *Prover) bigSignedDecomposeAssign(x *big.Int, base []*big.Int, xOut []*big.Int) {
	p.buffer.dcmpSigned.Set(x)
	if p.buffer.dcmpSigned.Cmp(p.buffer.qHalf) > 0 {
		p.buffer.dcmpSigned.Sub(p.buffer.dcmpSigned, p.Parameters.Modulus())
	}

	for i := 0; i < len(xOut); i++ {
		p.buffer.baseNeg.Neg(base[i])

		if p.buffer.dcmpSigned.Cmp(base[i]) >= 0 {
			xOut[i].SetInt64(1)
			p.buffer.dcmpSigned.Sub(p.buffer.dcmpSigned, base[i])
		} else if p.buffer.dcmpSigned.Cmp(p.buffer.baseNeg) <= 0 {
			xOut[i].SetInt64(-1)
			p.buffer.dcmpSigned.Add(p.buffer.dcmpSigned, base[i])
		} else {
			xOut[i].SetInt64(0)
		}
	}
}
