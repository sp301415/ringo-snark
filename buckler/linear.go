package buckler

import (
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/num"
)

// LinearTransformer implements the necessary methods to check linear relations.
// It must support two mappings: x -> Mx and x -> M^Tx for some matrix M.
type LinearTransformer[E num.Uint[E]] interface {
	// TransformTo computes vOut = Mv.
	TransformTo(vOut, v []E)
	// TransposeTo computes vOut = M^Tv.
	TransposeTo(vOut, v []E)
}

// nttTransformer computes the negacyclic NTT transform.
type nttTransformer[E num.Uint[E]] struct {
	ntt   *bigpoly.CyclotomicTransformer[E]
	scale E
}

// NewNTTTransformer creates a new [nttTransformer].
func NewNTTTransformer[E num.Uint[E]](rank int) LinearTransformer[E] {
	var scale E
	return &nttTransformer[E]{
		ntt:   bigpoly.NewCyclotomicTransformer[E](rank),
		scale: scale.New().SetUint64(uint64(rank)),
	}
}

func (ntt *nttTransformer[E]) TransformTo(vOut, v []E) {
	ntt.ntt.NTTTo(vOut, v)
}

func (ntt *nttTransformer[E]) TransposeTo(vOut, v []E) {
	for i := 0; i < ntt.ntt.Rank(); i++ {
		vOut[i].Mul(v[ntt.ntt.Rank()-1-i], ntt.scale)
	}
	ntt.ntt.InvNTTTo(vOut, vOut)
}
