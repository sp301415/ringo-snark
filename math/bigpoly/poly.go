package bigpoly

import (
	"bytes"
	"unsafe"

	"github.com/sp301415/ringo-snark/math/num"
)

// Poly represents a polynomial with elements of type [Uint].
type Poly[E num.Uint[E]] struct {
	Coeffs []E
	IsNTT  bool
}

// NewPoly creates a new [Poly].
func NewPoly[E num.Uint[E]](rank int, isNTT bool) *Poly[E] {
	coeffs := make([]E, rank)
	for i := range coeffs {
		coeffs[i] = coeffs[i].New()
	}

	return &Poly[E]{
		Coeffs: coeffs,
		IsNTT:  isNTT,
	}
}

// Rank returns the rank of the polynomial.
func (p *Poly[E]) Rank() int {
	return len(p.Coeffs)
}

// Marshal returns the binary encoding of the polynomial.
func (p *Poly[E]) Marshal() []byte {
	var buf bytes.Buffer
	for i := range p.Coeffs {
		buf.Write(p.Coeffs[i].Marshal())
	}
	return buf.Bytes()
}

// CopyFrom copies p0 to p.
func (p *Poly[E]) CopyFrom(p0 *Poly[E]) {
	for i := 0; i < len(p.Coeffs); i += 8 {
		cOut := (*[8]E)(unsafe.Pointer(&p.Coeffs[i]))
		c0 := (*[8]E)(unsafe.Pointer(&p0.Coeffs[i]))

		cOut[0].Set(c0[0])
		cOut[1].Set(c0[1])
		cOut[2].Set(c0[2])
		cOut[3].Set(c0[3])

		cOut[4].Set(c0[4])
		cOut[5].Set(c0[5])
		cOut[6].Set(c0[6])
		cOut[7].Set(c0[7])
	}

	p.IsNTT = p0.IsNTT
}

// Evaluate evaluates p at x.
func (p *Poly[E]) Evaluate(x E) E {
	if p.IsNTT {
		panic("Evaluate: p is in NTT form")
	}

	var z E
	z = z.New().SetUint64(0)
	for i := len(p.Coeffs) - 1; i >= 0; i-- {
		z.Mul(z, x)
		z.Add(z, p.Coeffs[i])
	}
	return z
}

// Clear clears the polynomial.
func (p *Poly[E]) Clear() {
	for i := range p.Coeffs {
		p.Coeffs[i].SetUint64(0)
	}
}

// isBinaryOperable checks if pOut, p is operable.
func isBinaryOperable[E num.Uint[E]](rank int, pOut, p *Poly[E]) bool {
	switch {
	case len(pOut.Coeffs) != rank || len(p.Coeffs) != rank:
		return false
	}
	return true
}

// isTernaryOperable checks if pOut, p0, p1 is operable.
func isTernaryOperable[E num.Uint[E]](rank int, pOut, p0, p1 *Poly[E]) bool {
	switch {
	case len(pOut.Coeffs) != rank || len(p0.Coeffs) != rank || len(p1.Coeffs) != rank:
		return false
	case pOut.IsNTT != p1.IsNTT:
		return false
	}
	return true
}

// evaluatorBuffer is a buffer for polynomial evaluators.
type evaluatorBuffer[E num.Uint[E]] struct {
	p *Poly[E]
}

// newEvaluatorBuffer creates a new [evaluatorBuffer].
func newEvaluatorBuffer[E num.Uint[E]](rank int) evaluatorBuffer[E] {
	return evaluatorBuffer[E]{
		p: NewPoly[E](rank, false),
	}
}
