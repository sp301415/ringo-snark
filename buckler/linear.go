package buckler

import (
	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
)

// LinearChecker implements the necessary methods to check linear relations.
// It must support two mappings: x -> Mx and x -> M^Tx for some matrix M.
type LinearChecker[E bignum.Uint[E]] interface {
	// TransformTo computes vOut = Mv.
	TransformTo(vOut, v []E)
	// TransposeTo computes vOut = M^Tv.
	TransposeTo(vOut, v []E)
}

// nttChecker computes the negacyclic NTT transform.
type nttChecker[E bignum.Uint[E]] struct {
	ntt   *bigpoly.CyclotomicTransformer[E]
	scale E
}

// NewNTTChecker creates a new [nttChecker].
func NewNTTChecker[E bignum.Uint[E]](rank int) LinearChecker[E] {
	var scale E
	return &nttChecker[E]{
		ntt:   bigpoly.NewCyclotomicTransformer[E](rank),
		scale: scale.New().SetUint64(uint64(rank)),
	}
}

func (ntt *nttChecker[E]) TransformTo(vOut, v []E) {
	ntt.ntt.FwdNTTTo(vOut, v)
}

func (ntt *nttChecker[E]) TransposeTo(vOut, v []E) {
	for i := 0; i < ntt.ntt.Rank(); i++ {
		vOut[i].Mul(v[ntt.ntt.Rank()-1-i], ntt.scale)
	}
	ntt.ntt.InvNTTTo(vOut, vOut)
}

// autChecker computes the automrophism on coefficients.
type autChecker[E bignum.Uint[E]] struct {
	eval   *bigpoly.CyclotomicEvaluator[E]
	isNTT  bool
	idx    int
	idxInv int
}

// NewAutChecker creates a new [autChecker].
func NewAutChecker[E bignum.Uint[E]](eval *bigpoly.CyclotomicEvaluator[E], idx int, isNTT bool) LinearChecker[E] {
	return &autChecker[E]{
		eval:   eval,
		isNTT:  isNTT,
		idx:    idx,
		idxInv: int(modInverse(uint64(idx), uint64(2*eval.Rank()))),
	}
}

func (t *autChecker[E]) TransformTo(vOut, v []E) {
	p := &bigpoly.Poly[E]{Coeffs: v, IsNTT: t.isNTT}
	pOut := &bigpoly.Poly[E]{Coeffs: vOut}
	t.eval.AutTo(pOut, p, t.idx)
}

func (t *autChecker[E]) TransposeTo(vOut, v []E) {
	p := &bigpoly.Poly[E]{Coeffs: v, IsNTT: t.isNTT}
	pOut := &bigpoly.Poly[E]{Coeffs: vOut}
	t.eval.AutTo(pOut, p, t.idxInv)
}

func modInverse(x, m uint64) uint64 {
	x %= m

	a, b := x, m
	u, v := uint64(1), uint64(0)
	for b != 0 {
		q := a / b
		a, b = b, a-q*b
		u, v = v, u-q*v
	}

	if a != 1 {
		panic("modular inverse does not exist")
	}

	return u % m
}
