package buckler

import (
	"math/big"

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

// projChecker computes the random projection on coefficients.
type projChecker[E bignum.Uint[E]] struct {
	proj [][]bool
}

func newProjChecker[E bignum.Uint[E]](rank int) LinearChecker[E] {
	proj := make([][]bool, 128)
	for i := range proj {
		proj[i] = make([]bool, rank)
	}
	return &projChecker[E]{
		proj: proj,
	}
}

func (c *projChecker[E]) TransformTo(vOut, v []E) {
	for i := range c.proj {
		vOut[i].SetUint64(0)
	}

	for i := range c.proj {
		for j := range c.proj[i] {
			if c.proj[i][j] {
				vOut[i].Add(vOut[i], v[j])
			}
		}
	}
	for i := len(c.proj); i < len(vOut); i++ {
		vOut[i].SetUint64(0)
	}
}

func (c *projChecker[E]) TransposeTo(vOut, v []E) {
	for i := range c.proj[0] {
		vOut[i].SetUint64(0)
	}

	for i := range c.proj {
		for j := range c.proj[i] {
			if c.proj[i][j] {
				vOut[j].Add(vOut[j], v[i])
			}
		}
	}
}

// projRecomposeChecker recomposes the decomposed projection result.
type projRecomposeChecker[E bignum.Uint[E]] struct {
	dcmpBase []E
}

func newProjRecomposeChecker[E bignum.Uint[E]](bound *big.Int) LinearChecker[E] {
	dcmpBaseBig := decomposeBase(bound)
	dcmpBase := make([]E, len(dcmpBaseBig))
	for i := range dcmpBaseBig {
		dcmpBase[i] = dcmpBase[i].New().SetBigInt(dcmpBaseBig[i])
	}
	return &projRecomposeChecker[E]{
		dcmpBase: dcmpBase,
	}
}

func (c *projRecomposeChecker[E]) TransformTo(vOut, v []E) {
	var mul E
	mul = mul.New()

	for i := 0; i < len(vOut)/len(c.dcmpBase); i++ {
		vOut[i].SetUint64(0)
		for j := 0; j < len(c.dcmpBase); j++ {
			mul.Mul(c.dcmpBase[j], v[i*len(c.dcmpBase)+j])
			vOut[i].Add(vOut[i], mul)
		}
	}
	for i := len(vOut) / len(c.dcmpBase); i < len(vOut); i++ {
		vOut[i].SetUint64(0)
	}
}

func (c *projRecomposeChecker[E]) TransposeTo(vOut, v []E) {
	for i := 0; i < len(vOut)/len(c.dcmpBase); i++ {
		for j := 0; j < len(c.dcmpBase); j++ {
			vOut[i*len(c.dcmpBase)+j].Mul(c.dcmpBase[j], v[i])
		}
	}
	for i := (len(vOut) / len(c.dcmpBase)) * len(c.dcmpBase); i < len(vOut); i++ {
		vOut[i].SetUint64(0)
	}
}
