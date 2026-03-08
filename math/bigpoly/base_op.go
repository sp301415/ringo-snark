package bigpoly

import (
	"sync"

	"github.com/sp301415/ringo-snark/math/bignum"
)

// baseOperator is a base operator.
type baseOperator[E bignum.Uint[E]] struct {
	rank int
	ntt  transformer[E]

	pool *sync.Pool
}

// newBaseOperator creates a new [baseOperator].
func newBaseOperator[E bignum.Uint[E]](rank int, ntt transformer[E]) *baseOperator[E] {
	return &baseOperator[E]{
		rank: rank,
		ntt:  ntt,

		pool: &sync.Pool{
			New: func() any {
				return NewPoly[E](rank, true)
			},
		},
	}
}

// NewPoly creates a new polynomial in the ring.
func (op *baseOperator[E]) NewPoly(isNTT bool) *Poly[E] {
	return NewPoly[E](op.rank, isNTT)
}

// Rank returns the rank.
func (op *baseOperator[E]) Rank() int {
	return op.rank
}

// Add returns p0 + p1.
func (op *baseOperator[E]) Add(p0, p1 *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(p0.IsNTT)
	op.AddTo(pOut, p0, p1)
	return pOut
}

// AddTo computes pOut = p0 + p1.
func (op *baseOperator[E]) AddTo(pOut, p0, p1 *Poly[E]) {
	checkBinaryOperable(op.rank, pOut, p0, p1)

	addVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = p0.IsNTT
}

// Sub returns p0 - p1.
func (op *baseOperator[E]) Sub(p0, p1 *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(p0.IsNTT)
	op.SubTo(pOut, p0, p1)
	return pOut
}

// SubTo computes pOut = p0 - p1.
func (op *baseOperator[E]) SubTo(pOut, p0, p1 *Poly[E]) {
	checkBinaryOperable(op.rank, pOut, p0, p1)

	subVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = p0.IsNTT
}

// Neg returns -p.
func (op *baseOperator[E]) Neg(p *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(p.IsNTT)
	op.NegTo(pOut, p)
	return pOut
}

// NegTo computes pOut = -p.
func (op *baseOperator[E]) NegTo(pOut, p *Poly[E]) {
	checkUnaryOperable(op.rank, pOut, p)

	negVecTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// ScalarMul returns pOut = c * p.
func (op *baseOperator[E]) ScalarMul(p *Poly[E], c E) *Poly[E] {
	pOut := op.NewPoly(p.IsNTT)
	op.ScalarMulTo(pOut, p, c)
	return pOut
}

// ScalarMulTo computes pOut = c * p.
func (op *baseOperator[E]) ScalarMulTo(pOut, p *Poly[E], c E) {
	checkUnaryOperable(op.rank, pOut, p)

	scalarMulVecTo(pOut.Coeffs, p.Coeffs, c)
	pOut.IsNTT = p.IsNTT
}

// ScalarMulAddTo computes pOut += c * p.
func (op *baseOperator[E]) ScalarMulAddTo(pOut, p *Poly[E], c E) {
	checkUnaryOperable(op.rank, pOut, p)

	pBuf := op.pool.Get().(*Poly[E])
	defer op.pool.Put(pBuf)

	scalarMulVecTo(pBuf.Coeffs, p.Coeffs, c)
	addVecTo(pOut.Coeffs, pOut.Coeffs, pBuf.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// ScalarMulSubTo computes pOut -= c * p.
func (op *baseOperator[E]) ScalarMulSubTo(pOut, p *Poly[E], c E) {
	checkUnaryOperable(op.rank, pOut, p)

	pBuf := op.pool.Get().(*Poly[E])
	defer op.pool.Put(pBuf)

	scalarMulVecTo(pBuf.Coeffs, p.Coeffs, c)
	subVecTo(pOut.Coeffs, pOut.Coeffs, pBuf.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// Mul returns pOut = p0 * p1.
func (op *baseOperator[E]) Mul(p0, p1 *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(true)
	op.MulTo(pOut, p0, p1)
	return pOut
}

// MulTo computes pOut =  p0 * p1.
func (op *baseOperator[E]) MulTo(pOut, p0, p1 *Poly[E]) {
	checkBinaryOperable(op.rank, pOut, p0, p1)
	if !p0.IsNTT || !p1.IsNTT {
		panic("input(s) not in NTT domain")
	}

	mulVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = true
}

// MulAddTo computes pOut +=  p0 * p1.
func (op *baseOperator[E]) MulAddTo(pOut, p0, p1 *Poly[E]) {
	checkBinaryOperable(op.rank, pOut, p0, p1)
	if !p0.IsNTT || !p1.IsNTT {
		panic("input(s) not in NTT domain")
	}

	pBuf := op.pool.Get().(*Poly[E])
	defer op.pool.Put(pBuf)

	mulVecTo(pBuf.Coeffs, p0.Coeffs, p1.Coeffs)
	addVecTo(pOut.Coeffs, pOut.Coeffs, pBuf.Coeffs)
	pOut.IsNTT = true
}

// MulSubTo computes pOut -= p0 * p1.
func (op *baseOperator[E]) MulSubTo(pOut, p0, p1 *Poly[E]) {
	checkBinaryOperable(op.rank, pOut, p0, p1)
	if !p0.IsNTT || !p1.IsNTT {
		panic("input(s) not in NTT domain")
	}

	pBuf := op.pool.Get().(*Poly[E])
	defer op.pool.Put(pBuf)

	mulVecTo(pBuf.Coeffs, p0.Coeffs, p1.Coeffs)
	subVecTo(pOut.Coeffs, pOut.Coeffs, pBuf.Coeffs)
	pOut.IsNTT = true
}

// NTT returns NTT(p).
func (op *baseOperator[E]) NTT(p *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(true)
	op.NTTTo(pOut, p)
	return pOut
}

// NTTTo computes pOut = NTT(p).
func (op *baseOperator[E]) NTTTo(pOut, p *Poly[E]) {
	checkUnaryOperable(op.rank, pOut, p)
	if p.IsNTT {
		panic("input already in NTT domain")
	}

	op.ntt.FwdNTTTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = true
}

// InvNTT returns InvNTT(p).
func (op *baseOperator[E]) InvNTT(p *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(false)
	op.InvNTTTo(pOut, p)
	return pOut
}

// InvNTTTo computes pOut = InvNTT(p).
func (op *baseOperator[E]) InvNTTTo(pOut, p *Poly[E]) {
	checkUnaryOperable(op.rank, pOut, p)
	if !p.IsNTT {
		panic("input not in NTT domain")
	}

	op.ntt.InvNTTTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = false
}
