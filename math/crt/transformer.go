package crt

import (
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

// Transformer computes the forward/inverse number theoretic transform (NTT).
type Transformer struct {
	rank int
	mod  *num.Modulus

	// tw is the twiddle factor for NTT.
	tw []uint64
	// twS is the Shoup form of tw.
	twS []uint64
	// twInv is the twiddle factor for InvNTT.
	twInv []uint64
	// twInvS is the Shoup form of twInv.
	twInvS []uint64

	// rankInv is the modular inverse of the rank.
	rankInv uint64
	// rankInvS is the Shoup form of rankInv.
	rankInvS uint64
}

func NewTransformer(rank int, mod *num.Modulus) *Transformer {
	root := num.Generators(mod)

	tw := make([]uint64, rank)
	twInv := make([]uint64, rank)
	tw[0], tw[1] = 1, num.NthRoot(rank<<1, root, mod)
	twInv[0], twInv[1] = 1, num.Inv(tw[1], mod)
	for i := 2; i < rank; i++ {
		tw[i] = num.Mul(tw[i-1], tw[1], mod)
		twInv[i] = num.Mul(twInv[i-1], twInv[1], mod)
	}
	vec.BitReverseInPlace(tw)
	vec.BitReverseInPlace(twInv)

	rankInv := num.Inv(uint64(rank), mod)

	return &Transformer{
		rank: rank,
		mod:  mod,

		tw:     tw,
		twS:    vec.SForm(tw, mod),
		twInv:  twInv,
		twInvS: vec.SForm(twInv, mod),

		rankInv:  rankInv,
		rankInvS: num.SForm(rankInv, mod),
	}
}

// ForwardTo transforms the uint64 vector to NTT form.
func (ntt *Transformer) ForwardTo(vNTT, v []uint64) {
	checkLength(ntt.rank, len(vNTT), len(v))

	copy(vNTT, v)
	fwdNTTInPlacePow2(vNTT, ntt.tw, ntt.twS, ntt.mod.Value())
}

// InverseTo transforms the uint64 vector to Standard form.
func (ntt *Transformer) InverseTo(v, vNTT []uint64) {
	checkLength(ntt.rank, len(vNTT), len(v))

	copy(v, vNTT)
	invNTTInPlacePow2(v, ntt.twInv, ntt.twInvS, ntt.mod.Value())
	vec.SMulScalarTo(v, v, ntt.rankInv, ntt.rankInvS, ntt.mod)
}
