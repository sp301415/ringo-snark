package bigpoly

import "github.com/sp301415/ringo-snark/math/num"

// CyclotomicEvaluator evaluates polynomial over power-of-two cyclotomic ring.
type CyclotomicEvaluator[E num.Uint[E]] struct {
	rank int

	ntt *CyclotomicTransformer[E]

	buf evaluatorBuffer[E]
}

// NewCyclotomicEvaluator creates a new [CyclotomicEvaluator].
func NewCyclotomicEvaluator[E num.Uint[E]](rank int) *CyclotomicEvaluator[E] {
	return &CyclotomicEvaluator[E]{
		rank: rank,

		ntt: NewCyclotomicTransformer[E](rank),

		buf: newEvaluatorBuffer[E](rank),
	}
}

// NewPoly creates a new polynomial in the ring.
func (e *CyclotomicEvaluator[E]) NewPoly(isNTT bool) *Poly[E] {
	return NewPoly[E](e.rank, isNTT)
}

// Add returns p0 + p1.
func (e *CyclotomicEvaluator[E]) Add(p0, p1 *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(p0.IsNTT)
	e.AddTo(pOut, p0, p1)
	return pOut
}

// AddTo computes pOut = p0 + p1.
func (e *CyclotomicEvaluator[E]) AddTo(pOut, p0, p1 *Poly[E]) {
	if !isTernaryOperable(e.rank, pOut, p0, p1) {
		panic("AddTo: inputs not consistent")
	}

	addVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = p0.IsNTT
}

// Sub returns p0 - p1.
func (e *CyclotomicEvaluator[E]) Sub(p0, p1 *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(p0.IsNTT)
	e.SubTo(pOut, p0, p1)
	return pOut
}

// SubTo computes pOut = p0 - p1.
func (e *CyclotomicEvaluator[E]) SubTo(pOut, p0, p1 *Poly[E]) {
	if !isTernaryOperable(e.rank, pOut, p0, p1) {
		panic("SubTo: inputs not consistent")
	}

	subVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = p0.IsNTT
}

// Neg computes pOut = -p.
func (e *CyclotomicEvaluator[E]) Neg(p *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(p.IsNTT)
	e.NegTo(pOut, p)
	return pOut
}

// NegTo computes pOut = -p.
func (e *CyclotomicEvaluator[E]) NegTo(pOut, p *Poly[E]) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("NegTo: inputs not consistent")
	}

	negVecTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// ScalarMul computes pOut = c * p.
func (e *CyclotomicEvaluator[E]) ScalarMul(p *Poly[E], c E) *Poly[E] {
	pOut := e.NewPoly(p.IsNTT)
	e.ScalarMulTo(pOut, p, c)
	return pOut
}

// ScalarMulTo computes pOut = c * p.
func (e *CyclotomicEvaluator[E]) ScalarMulTo(pOut, p *Poly[E], c E) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("ScalarMulTo: inputs not consistent")
	}

	scalarMulVecTo(pOut.Coeffs, p.Coeffs, c)
	pOut.IsNTT = p.IsNTT
}

// ScalarMulAddTo computes pOut += c * p.
func (e *CyclotomicEvaluator[E]) ScalarMulAddTo(pOut, p *Poly[E], c E) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("ScalarMulAddTo: inputs not consistent")
	}

	scalarMulVecTo(e.buf.p.Coeffs, p.Coeffs, c)
	addVecTo(pOut.Coeffs, pOut.Coeffs, e.buf.p.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// ScalarMulSubTo computes pOut -= c * p.
func (e *CyclotomicEvaluator[E]) ScalarMulSubTo(pOut, p *Poly[E], c E) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("ScalarMulSubTo: inputs not consistent")
	}

	scalarMulVecTo(e.buf.p.Coeffs, p.Coeffs, c)
	subVecTo(pOut.Coeffs, pOut.Coeffs, e.buf.p.Coeffs)
	pOut.IsNTT = p.IsNTT
}

// Mul returns p0 * p1.
func (e *CyclotomicEvaluator[E]) Mul(p0, p1 *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(p0.IsNTT && p1.IsNTT)
	e.MulTo(pOut, p0, p1)
	return pOut
}

// MulTo computes pOut = p0 * p1.
func (e *CyclotomicEvaluator[E]) MulTo(pOut, p0, p1 *Poly[E]) {
	if !isTernaryOperable(e.rank, pOut, p0, p1) {
		panic("MulTo: inputs not consistent")
	}
	if !p0.IsNTT || !p1.IsNTT {
		panic("MulTo: inputs not in NTT domain")
	}

	mulVecTo(pOut.Coeffs, p0.Coeffs, p1.Coeffs)
	pOut.IsNTT = true
}

// MulAddTo computes pOut += p0 * p1.
func (e *CyclotomicEvaluator[E]) MulAddTo(pOut, p0, p1 *Poly[E]) {
	if !isTernaryOperable(e.rank, pOut, p0, p1) {
		panic("MulAddTo: inputs not consistent")
	}
	if !p0.IsNTT || !p1.IsNTT {
		panic("MulAddTo: inputs not in NTT domain")
	}

	mulVecTo(e.buf.p.Coeffs, p0.Coeffs, p1.Coeffs)
	addVecTo(pOut.Coeffs, pOut.Coeffs, e.buf.p.Coeffs)
	pOut.IsNTT = true
}

// MulSubTo computes pOut -= p0 * p1.
func (e *CyclotomicEvaluator[E]) MulSubTo(pOut, p0, p1 *Poly[E]) {
	if !isTernaryOperable(e.rank, pOut, p0, p1) {
		panic("MulSubTo: inputs not consistent")
	}
	if !p0.IsNTT || !p1.IsNTT {
		panic("MulSubTo: inputs not in NTT domain")
	}

	mulVecTo(e.buf.p.Coeffs, p0.Coeffs, p1.Coeffs)
	subVecTo(pOut.Coeffs, pOut.Coeffs, e.buf.p.Coeffs)
	pOut.IsNTT = true
}

// NTT returns NTT(p).
func (e *CyclotomicEvaluator[E]) NTT(p *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(true)
	e.NTTTo(pOut, p)
	return pOut
}

// NTTTo computes pOut = NTT(p).
func (e *CyclotomicEvaluator[E]) NTTTo(pOut, p *Poly[E]) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("NTTTo: inputs not consistent")
	}
	if p.IsNTT {
		panic("NTTTo: input already in NTT domain")
	}

	e.ntt.NTTTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = true
}

// InvNTT returns InvNTT(p).
func (e *CyclotomicEvaluator[E]) InvNTT(p *Poly[E]) *Poly[E] {
	pOut := e.NewPoly(false)
	e.InvNTTTo(pOut, p)
	return pOut
}

// InvNTTTo computes pOut = InvNTT(p).
func (e *CyclotomicEvaluator[E]) InvNTTTo(pOut, p *Poly[E]) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("InvNTTTo: inputs not consistent")
	}
	if !p.IsNTT {
		panic("InvNTTTo: input not in NTT domain")
	}

	e.ntt.InvNTTTo(pOut.Coeffs, p.Coeffs)
	pOut.IsNTT = false
}

// SafeCopy returns a thread-safe copy.
func (e *CyclotomicEvaluator[E]) SafeCopy() *CyclotomicEvaluator[E] {
	return &CyclotomicEvaluator[E]{
		rank: e.rank,

		ntt: e.ntt,

		buf: newEvaluatorBuffer[E](e.rank),
	}
}
