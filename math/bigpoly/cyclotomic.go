package bigpoly

import (
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
)

// CyclotomicEvaluator evaluates polynomial over power-of-two cyclotomic ring.
type CyclotomicEvaluator[E bignum.Uint[E]] struct {
	rank int

	ntt *CyclotomicTransformer[E]

	buf evaluatorBuffer[E]
}

// NewCyclotomicEvaluator creates a new [CyclotomicEvaluator].
func NewCyclotomicEvaluator[E bignum.Uint[E]](rank int) *CyclotomicEvaluator[E] {
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

// Rank returns the rank of the evaluator.
func (e *CyclotomicEvaluator[E]) Rank() int {
	return e.rank
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

// Aut returns Aut(p, idx).
func (e *CyclotomicEvaluator[E]) Aut(p *Poly[E], idx int) *Poly[E] {
	pOut := e.NewPoly(p.IsNTT)
	e.AutTo(pOut, p, idx)
	return pOut
}

// AutTo computes pOut = Aut(p, idx).
func (e *CyclotomicEvaluator[E]) AutTo(pOut, p *Poly[E], idx int) {
	if !isBinaryOperable(e.rank, pOut, p) {
		panic("AutTo: inputs not consistent")
	}

	if idx%2 == 0 {
		panic("AutTo: idx must be odd")
	}

	idx %= 2 * e.rank
	if idx < 0 {
		idx += 2 * e.rank
	}

	if p.IsNTT {
		e.autNTTTo(pOut, p, idx)
	} else {
		e.autTo(pOut, p, idx)
	}
}

// autTo computes pOut = Aut(p, idx).
func (e *CyclotomicEvaluator[E]) autTo(pOut, p *Poly[E], idx int) {
	for i := 0; i < e.rank; i++ {
		j := (i * idx) % (2 * e.rank)
		if j < e.rank {
			e.buf.p.Coeffs[j].Set(p.Coeffs[i])
		} else {
			e.buf.p.Coeffs[j-e.rank].Neg(p.Coeffs[i])
		}
	}

	pOut.CopyFrom(e.buf.p)
	pOut.IsNTT = false
}

// autNTTTo computes pOut = Aut(p, idx).
func (e *CyclotomicEvaluator[E]) autNTTTo(pOut, p *Poly[E], idx int) {
	e.buf.p.CopyFrom(p)
	bitReverseInPlace(e.buf.p.Coeffs)

	for i := 0; i < e.rank; i++ {
		j := ((2*i + 1) * idx) % (2 * e.rank)
		j = (j - 1) >> 1
		pOut.Coeffs[i].Set(e.buf.p.Coeffs[j])
	}

	bitReverseInPlace(pOut.Coeffs)
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

// ModSwitch switches the modulus of pBig of modulus qBig.
func (e *CyclotomicEvaluator[E]) ModSwitch(pBig []*big.Int, qBig *big.Int) *Poly[E] {
	pOut := e.NewPoly(false)
	e.ModSwitchTo(pOut, pBig, qBig)
	return pOut
}

// ModSwitchTo switches the modulus of pBig of modulus q and writes to pOut.
func (e *CyclotomicEvaluator[E]) ModSwitchTo(pOut *Poly[E], pBig []*big.Int, qBig *big.Int) {
	if len(pBig) != e.rank {
		panic("ModSwitch: input size not consistent")
	}

	var z E

	q := z.New().SetInt64(-1).BigInt(new(big.Int))
	q.Add(q, big.NewInt(1))
	qBigHalf := new(big.Int).Rsh(qBig, 1)

	c, cRem := new(big.Int), new(big.Int)
	for i := range e.rank {
		c.Mul(pBig[i], q)
		cRem.Mod(c, qBig)
		if cRem.Cmp(qBigHalf) > 0 {
			cRem.Sub(cRem, qBig)
		}
		c.Sub(c, cRem)
		c.Div(c, qBig)
		c.Mod(c, q)
		pOut.Coeffs[i].SetBigInt(c)
	}

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
