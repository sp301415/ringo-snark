package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/num"
)

// LinearCheckTransformer implements the linear transformation x -> M^T*x for some matrix M.
//
// Note that we are computing the *transpose* of the matrix.
type LinearCheckTransformer interface {
	TransformAssign(xIn, xOut []*big.Int)
}

type nttTransformer struct {
	ringQ *bigring.BigRing
}

// NewNTTTransformer returns a TransposeTransformer for NTT.
func NewNTTTransformer(ringQ *bigring.BigRing) LinearCheckTransformer {
	return &nttTransformer{
		ringQ: ringQ,
	}
}

func (t *nttTransformer) TransformAssign(xIn, xOut []*big.Int) {
	for i := 0; i < t.ringQ.Degree(); i++ {
		xOut[i].Set(xIn[t.ringQ.Degree()-1-i])
	}
	t.ringQ.InvNTTInPlace(xOut)
}

type autTransformer struct {
	ringQ     *bigring.BigRing
	autIdx    int
	autIdxInv int
}

// NewAutTransformer returns a TransposeTransformer for an automorphism over coeff vector.
func NewAutTransformer(ringQ *bigring.BigRing, autIdx int) LinearCheckTransformer {
	autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*ringQ.Degree())))
	return &autTransformer{
		ringQ:     ringQ,
		autIdx:    autIdx,
		autIdxInv: autIdxInv,
	}
}

func (t *autTransformer) TransformAssign(vIn, vOut []*big.Int) {
	t.ringQ.AutomorphismAssign(bigring.BigPoly{Coeffs: vIn}, t.autIdxInv, bigring.BigPoly{Coeffs: vOut})
}

type autNTTTransformer struct {
	ringQ     *bigring.BigRing
	autIdx    int
	autIdxInv int
}

// NewAutNTTTransformer returns a TransposeTransformer for an automorphism over NTT vector.
func NewAutNTTTransformer(ringQ *bigring.BigRing, autIdx int) LinearCheckTransformer {
	autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*ringQ.Degree())))
	return &autNTTTransformer{
		ringQ:     ringQ,
		autIdx:    autIdx,
		autIdxInv: autIdxInv,
	}
}

func (t *autNTTTransformer) TransformAssign(xIn, xOut []*big.Int) {
	t.ringQ.AutomorphismNTTAssign(bigring.BigNTTPoly{Coeffs: xIn}, t.autIdxInv, bigring.BigNTTPoly{Coeffs: xOut})
}
