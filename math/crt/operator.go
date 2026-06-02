package crt

import (
	"math/bits"
	"sync"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

const (
	// MinRank is the minimum rank possible.
	MinRank = 8
)

// Operator evaluates ring operations over [Element].
//
// Operations usually take two forms: for example,
//   - Add(p0, p1) adds p0, p1, allocates a new vector to store the result and returns it.
//   - AddTo(pOut, p0, p1) adds p0, p1 and writes the result to pre-allocated pOut without returning.
//
// Moreover, operations panics when inputs are not consistent with the
// Operator's parameters, or operations itself are not valid.
type Operator struct {
	rank int
	mod  []*num.Modulus

	ntt []*Transformer

	pool *sync.Pool
}

// NewOperator creates a new [Operator].
func NewOperator(rank int, mod []*num.Modulus) *Operator {
	if rank < MinRank {
		panic("rank should be larger than or equal to MinRank")
	}

	ntt := make([]*Transformer, len(mod))
	for i := range mod {
		ntt[i] = NewTransformer(rank, mod[i])
	}

	return &Operator{
		rank: rank,
		mod:  mod,

		ntt: ntt,
		pool: &sync.Pool{
			New: func() any {
				v := make([]uint64, rank)
				return &v
			},
		},
	}
}

// Rank returns the rank.
func (op *Operator) Rank() int {
	return op.rank
}

// Modulus returns the modulus.
func (op *Operator) Modulus() []*num.Modulus {
	return op.mod
}

// Transformers returns the underlying [Transformer].
func (op *Operator) Transformer() []*Transformer {
	return op.ntt
}

// NewPoly creates a new polynomial element.
func (op *Operator) NewPoly() *Element {
	return NewPoly(op.rank, len(op.mod))
}

// NewNTTPoly creates a new polynomial element in NTT form.
func (op *Operator) NewNTTPoly() *Element {
	return NewNTTPoly(op.rank, len(op.mod))
}

// NewPolyCustom creates a new polynomial element.
func (op *Operator) NewPolyCustom(isNTT bool) *Element {
	return NewPolyCustom(op.rank, len(op.mod), isNTT)
}

// FwdNTT returns FwdNTT(e).
func (op *Operator) FwdNTT(e *Element) *Element {
	eOut := NewPoly(e.Rank(), len(op.mod))
	op.FwdNTTTo(eOut, e)
	return eOut
}

// FwdNTTTo computes eOut = NTT(e).
func (op *Operator) FwdNTTTo(eOut, e *Element) {
	isUnaryOperable(op.rank, len(op.mod), eOut, e)

	if e.Type() == TypeScalar {
		eOut.CopyFrom(e)
		return
	}

	if e.IsNTT {
		panic("input(s) must be in standard form")
	}

	for i := range op.ntt {
		op.ntt[i].ForwardTo(eOut.Coeffs[i], e.Coeffs[i])
	}

	eOut.IsNTT = true
}

// InvNTT returns InvNTT(e).
func (op *Operator) InvNTT(e *Element) *Element {
	eOut := NewPoly(e.Rank(), len(op.mod))
	op.InvNTTTo(eOut, e)
	return eOut
}

// InvNTTTo computes eOut = InvNTT(e).
func (op *Operator) InvNTTTo(eOut, e *Element) {
	isUnaryOperable(op.rank, len(op.mod), eOut, e)

	if e.Type() == TypeScalar {
		eOut.CopyFrom(e)
		return
	}

	if !e.IsNTT {
		panic("input(s) must be in NTT form")
	}

	for i := range op.ntt {
		op.ntt[i].InverseTo(eOut.Coeffs[i], e.Coeffs[i])
	}

	eOut.IsNTT = false
}

// Add returns e0 + e1.
func (op *Operator) Add(e0, e1 *Element) *Element {
	eOut := NewPoly(max(e0.Rank(), e1.Rank()), len(op.mod))
	op.AddTo(eOut, e0, e1)
	return eOut
}

// AddTo computes eOut = e0 + e1.
func (op *Operator) AddTo(eOut, e0, e1 *Element) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Add(e0.Coeffs[i][0], e1.Coeffs[i][0], op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		for i := range op.mod {
			vec.AddTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], op.mod[i])
		}
		eOut.IsNTT = e0.IsNTT
	default:
		c, p := orderByType(e0, e1)
		for i := range op.mod {
			if p.IsNTT {
				vec.AddScalarTo(eOut.Coeffs[i], p.Coeffs[i], c.Coeffs[i][0], op.mod[i])
			} else {
				copy(eOut.Coeffs[i], p.Coeffs[i])
				eOut.Coeffs[i][0] = num.Add(eOut.Coeffs[i][0], c.Coeffs[i][0], op.mod[i])
			}
		}
		eOut.IsNTT = p.IsNTT
	}
}

// Sub returns e0 - e1.
func (op *Operator) Sub(e0, e1 *Element) *Element {
	eOut := NewPoly(max(e0.Rank(), e1.Rank()), len(op.mod))
	op.SubTo(eOut, e0, e1)
	return eOut
}

// SubTo computes eOut = e0 - e1.
func (op *Operator) SubTo(eOut, e0, e1 *Element) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Sub(e0.Coeffs[i][0], e1.Coeffs[i][0], op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		for i := range op.mod {
			vec.SubTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], op.mod[i])
		}
		eOut.IsNTT = e0.IsNTT
	default:
		c, p := orderByType(e0, e1)
		for i := range op.mod {
			if p.IsNTT {
				vec.SubScalarTo(eOut.Coeffs[i], p.Coeffs[i], c.Coeffs[i][0], op.mod[i])
			} else {
				copy(eOut.Coeffs[i], p.Coeffs[i])
				eOut.Coeffs[i][0] = num.Sub(eOut.Coeffs[i][0], c.Coeffs[i][0], op.mod[i])
			}
		}
		if e0.Type() == TypeScalar {
			for i := range op.mod {
				vec.NegTo(eOut.Coeffs[i], eOut.Coeffs[i], op.mod[i])
			}
		}
		eOut.IsNTT = p.IsNTT
	}
}

// Neg returns -e.
func (op *Operator) Neg(e *Element) *Element {
	eOut := NewPolyCustom(e.Rank(), len(op.mod), e.IsNTT)
	op.NegTo(eOut, e)
	return eOut
}

// NegTo computes eOut = -e.
func (op *Operator) NegTo(eOut, e *Element) {
	isUnaryOperable(op.rank, len(op.mod), eOut, e)

	switch e.Type() {
	case TypeScalar:
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Neg(e.Coeffs[i][0], op.mod[i])
		}
	case TypePoly:
		for i := range op.mod {
			vec.NegTo(eOut.Coeffs[i], e.Coeffs[i], op.mod[i])
		}
		eOut.IsNTT = e.IsNTT
	}
}

// Mul returns e0 * e1.
// When e0, e1 are both polynomials, they must be in NTT form.
func (op *Operator) Mul(e0, e1 *Element) *Element {
	eOut := NewPoly(max(e0.Rank(), e1.Rank()), len(op.mod))
	op.MulTo(eOut, e0, e1)
	return eOut
}

// MulTo computes eOut = e0 * e1.
// When e0, e1 are both polynomials, they must be in NTT form.
func (op *Operator) MulTo(eOut, e0, e1 *Element) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Mul(e0.Coeffs[i][0], e1.Coeffs[i][0], op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.MulTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		c, p := orderByType(e0, e1)
		for i := range op.mod {
			vec.MulScalarTo(eOut.Coeffs[i], p.Coeffs[i], c.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = p.IsNTT
	}
}

// MulAddTo computes eOut += e0 * e1.
func (op *Operator) MulAddTo(eOut, e0, e1 *Element) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Add(eOut.Coeffs[i][0], num.Mul(e0.Coeffs[i][0], e1.Coeffs[i][0], op.mod[i]), op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.MulAddTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		c, p := orderByType(e0, e1)
		for i := range op.mod {
			vec.MulAddScalarTo(eOut.Coeffs[i], p.Coeffs[i], c.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = p.IsNTT
	}
}

// MulSubTo computes eOut -= e0 * e1.
func (op *Operator) MulSubTo(eOut, e0, e1 *Element) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Sub(eOut.Coeffs[i][0], num.Mul(e0.Coeffs[i][0], e1.Coeffs[i][0], op.mod[i]), op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.MulSubTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		c, p := orderByType(e0, e1)
		for i := range op.mod {
			vec.MulSubScalarTo(eOut.Coeffs[i], p.Coeffs[i], c.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = p.IsNTT
	}
}

// SMul returns e0 * e1.
// When e0, e1 are both polynomials, they must be in NTT form.
func (op *Operator) SMul(e0, e1 *Element, e1S *ShoupElement) *Element {
	eOut := NewPoly(max(e0.Rank(), e1.Rank()), len(op.mod))
	op.SMulTo(eOut, e0, e1, e1S)
	return eOut
}

// SMulTo computes eOut = e0 * e1.
// When e0, e1 are both polynomials, they must be in NTT form.
func (op *Operator) SMulTo(eOut, e0, e1 *Element, e1S *ShoupElement) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, (*Element)(e1S))

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.SMul(e0.Coeffs[i][0], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.SMulTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], e1S.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		if e0.Type() == TypeScalar {
			panic("(e0, e1) must be (Poly, Scalar)")
		}

		for i := range op.mod {
			vec.SMulScalarTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = e0.IsNTT
	}
}

// SMulAddTo computes eOut += e0 * e1.
func (op *Operator) SMulAddTo(eOut, e0, e1 *Element, e1S *ShoupElement) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, (*Element)(e1S))

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Add(eOut.Coeffs[i][0], num.SMul(e0.Coeffs[i][0], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i]), op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.SMulAddTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], e1S.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		if e0.Type() == TypeScalar {
			panic("(e0, e1) must be (Poly, Scalar)")
		}

		for i := range op.mod {
			vec.SMulAddScalarTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = e0.IsNTT
	}
}

// SMulSubTo computes eOut -= e0 * e1.
func (op *Operator) SMulSubTo(eOut, e0, e1 *Element, e1S *ShoupElement) {
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, e1)
	isBinaryOperable(op.rank, len(op.mod), eOut, e0, (*Element)(e1S))

	switch {
	case isEqualType(e0, e1, TypeScalar):
		for i := range op.mod {
			eOut.Coeffs[i][0] = num.Sub(eOut.Coeffs[i][0], num.SMul(e0.Coeffs[i][0], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i]), op.mod[i])
		}
	case isEqualType(e0, e1, TypePoly):
		if !e0.IsNTT || !e1.IsNTT {
			panic("input(s) must be in NTT form")
		}

		for i := range op.mod {
			vec.SMulSubTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i], e1S.Coeffs[i], op.mod[i])
		}

		eOut.IsNTT = true
	default:
		if e0.Type() == TypeScalar {
			panic("(e0, e1) must be (Poly, Scalar)")
		}

		for i := range op.mod {
			vec.SMulSubScalarTo(eOut.Coeffs[i], e0.Coeffs[i], e1.Coeffs[i][0], e1S.Coeffs[i][0], op.mod[i])
		}
		eOut.IsNTT = e0.IsNTT
	}
}

// SForm returns Shoup Form of e.
func (op *Operator) SForm(e *Element) *ShoupElement {
	eOutS := (*ShoupElement)(NewPoly(e.Rank(), len(op.mod)))
	op.SFormTo(eOutS, e)
	return eOutS
}

// SFormTo computes eS = SForm(e).
func (op *Operator) SFormTo(eOutS *ShoupElement, e *Element) {
	isUnaryOperable(op.rank, len(op.mod), (*Element)(eOutS), e)

	switch e.Type() {
	case TypeScalar:
		for i := range op.mod {
			eOutS.Coeffs[i][0] = num.SForm(e.Coeffs[i][0], op.mod[i])
		}
	case TypePoly:
		for i := range op.mod {
			vec.SFormTo(eOutS.Coeffs[i], e.Coeffs[i], op.mod[i])
		}
	}

	eOutS.IsNTT = e.IsNTT
}

// CanAut returns whether the given automorphism index is valid.
func (op *Operator) CanAut(idx int) bool {
	cycloOrd := op.rank << 1
	idx = (idx%cycloOrd + cycloOrd) % cycloOrd
	return idx%2 == 1
}

// Aut returns aut(e, idx).
// Panics when the automorphism index is invalid.
func (op *Operator) Aut(e *Element, idx int) *Element {
	eOut := NewPoly(e.Rank(), len(op.mod))
	op.AutTo(eOut, e, idx)
	return eOut
}

// AutTo computes eOut = aut(e, idx).
// Panics when the automorphism index is invalid.
func (op *Operator) AutTo(eOut, e *Element, idx int) {
	isUnaryOperable(op.rank, len(op.mod), eOut, e)

	switch e.Type() {
	case TypeScalar:
		eOut.CopyFrom(e)
	case TypePoly:
		if !op.CanAut(idx) {
			panic("invalid automorphism index")
		}

		cycloOrd, rank := op.rank<<1, op.rank
		idx = (idx%cycloOrd + cycloOrd) % cycloOrd

		if idx == 1 {
			eOut.CopyFrom(e)
			return
		}

		eBufPtr := op.pool.Get().(*[]uint64)
		eBuf := *eBufPtr
		defer op.pool.Put(eBufPtr)

		for i := range op.mod {
			if e.IsNTT {
				copy(eBuf, e.Coeffs[i])
				revShiftBits := 64 - int(num.Log2(rank))
				for j := 0; j < rank; j++ {
					jOut := ((2*j + 1) * idx) & (cycloOrd - 1)
					idxIn := int(bits.Reverse64((uint64(jOut)-1)/2) >> revShiftBits)
					idxOut := int(bits.Reverse64(uint64(j)) >> revShiftBits)
					eOut.Coeffs[i][idxOut] = eBuf[idxIn]
				}
			} else {
				clear(eBuf)
				for j := 0; j < rank; j++ {
					idxOut := (j * idx) & (cycloOrd - 1)
					if idxOut >= rank {
						eBuf[idxOut-rank] = num.Neg(e.Coeffs[i][j], op.mod[i])
					} else {
						eBuf[idxOut] = e.Coeffs[i][j]
					}
				}
				copy(eOut.Coeffs[i], eBuf)
			}
		}

		eOut.IsNTT = e.IsNTT
	}
}
