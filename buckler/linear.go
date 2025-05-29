package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/num"
)

// TransposeTransformer implements the linear transformation x -> M^T*x for some matrix M.
type TransposeTransformer interface {
	TransposeTransform([]*big.Int) []*big.Int
}

type nttTransformer struct {
	ringQ *bigring.BigRing
}

// NewNTTTransformer returns a TransposeTransformer for NTT.
func NewNTTTransformer(ringQ *bigring.BigRing) TransposeTransformer {
	return &nttTransformer{
		ringQ: ringQ,
	}
}

func (t *nttTransformer) TransposeTransform(v []*big.Int) []*big.Int {
	if len(v) != t.ringQ.Degree() {
		panic("invalid vector length for NTT transformation")
	}

	vOut := make([]*big.Int, t.ringQ.Degree())
	for i := 0; i < t.ringQ.Degree(); i++ {
		vOut[i] = big.NewInt(0).Set(v[t.ringQ.Degree()-1-i])
	}
	t.ringQ.InvNTTInPlace(vOut)
	return vOut
}

type autNTTTransformer struct {
	ringQ     *bigring.BigRing
	autIdx    int
	autIdxInv int
}

// NewAutNTTTransformer returns a TransposeTransformer for an automorphism over NTT vector.
func NewAutNTTTransformer(ringQ *bigring.BigRing, autIdx int) TransposeTransformer {
	autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*ringQ.Degree())))
	return &autNTTTransformer{
		ringQ:     ringQ,
		autIdx:    autIdx,
		autIdxInv: autIdxInv,
	}
}

func (t *autNTTTransformer) TransposeTransform(v []*big.Int) []*big.Int {
	if len(v) != t.ringQ.Degree() {
		panic("invalid vector length for automorphism transformation")
	}

	vOut := t.ringQ.AutomorphismNTT(bigring.BigNTTPoly{Coeffs: v}, t.autIdxInv).Coeffs
	return vOut
}
