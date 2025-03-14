package bigring

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/num"
)

// BigRing is a negacyclic ring.
type BigRing struct {
	degree  int
	modulus *big.Int

	tw        []*big.Int
	twInv     []*big.Int
	degreeInv *big.Int
}

// NewBigRing creates a new BigRing.
func NewBigRing(N int, Q *big.Int) *BigRing {
	tw := make([]*big.Int, N)
	twInv := make([]*big.Int, N)

	exp1 := big.NewInt(0).Sub(Q, big.NewInt(1))
	exp1.Div(exp1, big.NewInt(2*int64(N)))
	exp2 := big.NewInt(int64(N))
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(Q) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, Q)
		gPow := big.NewInt(0).Exp(g, exp2, Q)
		if gPow.Cmp(big.NewInt(1)) == 0 {
			break
		}
	}

	for i := 0; i < N; i++ {
		tw[i] = big.NewInt(0).Exp(g, big.NewInt(int64(i)), Q)
		twInv[i] = big.NewInt(0).Exp(g, big.NewInt(int64(2*N-i)), Q)
	}
	num.BitReverseInPlace(tw)
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(N)), Q)

	return &BigRing{
		degree:  N,
		modulus: Q,

		tw:        tw,
		twInv:     twInv,
		degreeInv: degreeInv,
	}
}

// N returns the degree of the BigRing.
func (r *BigRing) N() int {
	return r.degree
}

// Modulus returns the modulus of the BigRing.
func (r *BigRing) Modulus() *big.Int {
	return r.modulus
}
