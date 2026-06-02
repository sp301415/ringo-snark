// Package poly implements polynomial and its operations.
package crt

import (
	"bytes"
	"encoding/binary"
	"math/big"
	"unsafe"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

// ElementType is the type of [Element].
type ElementType int

const (
	// TypeScalar is a scalar.
	TypeScalar ElementType = iota
	// TypePoly is a polynomial.
	TypePoly
)

// Element represents an element with CRT representation.
// Can be a scalar or a polynomial.
//
// A polynomial can have Standard or NTT form.
// All coefficients in NTT form are also in Montgomery form.
type Element struct {
	// Coeffs are the coefficients of the element.
	// Ordered as [ModLen][Rank].
	//
	// When rank is 1, the element represents a scalar.
	Coeffs [][]uint64

	// IsNTT indicates whether the polynomial is in NTT form.
	// Ignored for scalars.
	IsNTT bool
}

// NewScalar creates a new scalar [Element].
func NewScalar(modLen int) *Element {
	return NewPolyCustom(1, modLen, false)
}

// NewScalarFrom creates a new scalar [Element] from x.
func NewScalarFrom[T num.Integer | *big.Int](x T, mod []*num.Modulus) *Element {
	r := NewScalar(len(mod))

	var z T
	switch any(z).(type) {
	case *big.Int:
		u := any(x).(*big.Int)
		q, t := new(big.Int), new(big.Int)
		for i := range r.Coeffs {
			q.SetUint64(mod[i].Value())
			r.Coeffs[i][0] = t.Mod(u, q).Uint64()
		}

	case int8:
		u := any(x).(int8)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case int16:
		u := any(x).(int16)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case int32:
		u := any(x).(int32)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case int64:
		u := any(x).(int64)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case int:
		u := any(x).(int)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case uint8:
		u := any(x).(uint8)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case uint16:
		u := any(x).(uint16)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case uint32:
		u := any(x).(uint32)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case uint64:
		u := any(x).(uint64)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	case uint:
		u := any(x).(uint)
		for i := range r.Coeffs {
			r.Coeffs[i][0] = num.Reduce(u, mod[i])
		}
	}

	return r
}

// NewPoly creates a new polynomial [Element] in Standard form.
func NewPoly(rank, modLen int) *Element {
	return NewPolyCustom(rank, modLen, false)
}

// NewNTTPoly creates a new polynomial [Element] in NTT form.
func NewNTTPoly(rank, modLen int) *Element {
	return NewPolyCustom(rank, modLen, true)
}

// NewPolyCustom creates a new polynomial [Element].
func NewPolyCustom(rank, modLen int, isNTT bool) *Element {
	if 1 < rank && rank < MinRank {
		panic("rank should be larger than or equal to MinRank")
	}

	coeffs := make([][]uint64, modLen)
	for i := 0; i < modLen; i++ {
		coeffs[i] = make([]uint64, rank)
	}

	return &Element{
		Coeffs: coeffs,
		IsNTT:  isNTT,
	}
}

// Rank returns the length of the coefficients of p.
func (p *Element) Rank() int {
	if len(p.Coeffs) == 0 {
		return 0
	}

	rank := len(p.Coeffs[0])
	for i := 1; i < len(p.Coeffs); i++ {
		if len(p.Coeffs[i]) != rank {
			panic("inconsistent rank")
		}
	}

	return rank
}

// ModLen returns the number of RNS moduli of p.
func (p *Element) ModLen() int {
	return len(p.Coeffs)
}

// Clear clears p.
func (p *Element) Clear() {
	for i := range p.Coeffs {
		clear(p.Coeffs[i])
	}
}

// WithModIdx returns a shallow copy of p with the given modulus indices.
//
// Panics when idx is out of range.
func (p *Element) WithModIdx(idx ...int) *Element {
	for i := range idx {
		if idx[i] < 0 || idx[i] >= p.ModLen() {
			panic("index out of range")
		}
	}

	coeffs := make([][]uint64, len(idx))
	for i := range idx {
		coeffs[i] = p.Coeffs[idx[i]]
	}

	return &Element{
		Coeffs: coeffs,
		IsNTT:  p.IsNTT,
	}
}

// Copy returns a copy of p.
func (p *Element) Copy() *Element {
	pOut := NewPolyCustom(p.Rank(), p.ModLen(), p.IsNTT)
	for i := range p.Coeffs {
		copy(pOut.Coeffs[i], p.Coeffs[i])
	}
	return pOut
}

// CopyFrom copies the coefficients from pIn to p.
//
// Panics when p and pIn are not consistent.
func (p *Element) CopyFrom(pIn *Element) {
	if !p.IsConsistent(pIn) {
		panic("input(s) not consistent")
	}

	for i := range p.Coeffs {
		copy(p.Coeffs[i], pIn.Coeffs[i])
	}
	p.IsNTT = pIn.IsNTT
}

// IsEqual checks if p is equal to p0.
func (p *Element) IsEqual(p0 *Element) bool {
	if !p.IsConsistent(p0) {
		return false
	}

	for i := range p.Coeffs {
		for j := range p.Coeffs[i] {
			if p.Coeffs[i][j] != p0.Coeffs[i][j] {
				return false
			}
		}
	}

	return true
}

// IsConsistent checks if p has the same shape as p0.
func (p *Element) IsConsistent(p0 *Element) bool {
	if len(p.Coeffs) != len(p0.Coeffs) {
		return false
	}

	for i := range p.Coeffs {
		if len(p.Coeffs[i]) != len(p0.Coeffs[i]) {
			return false
		}
	}

	return true
}

// Type returns the type of p.
func (p *Element) Type() ElementType {
	if p.Rank() == 1 {
		return TypeScalar
	}
	return TypePoly
}

// WriteToBuf writes the value to [bytes.Buffer].
func (p *Element) WriteToBuf(buf *bytes.Buffer) {
	M := (p.Rank() >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	var buf64 [64]byte

	for i := range p.Coeffs {
		r := unsafe.Pointer(unsafe.SliceData(p.Coeffs[i]))

		for j := 0; j < M; j += 8 {
			w := (*[8]uint64)(unsafe.Add(r, uintptr(j)*L))

			binary.BigEndian.PutUint64(buf64[0*8:1*8], w[0])
			binary.BigEndian.PutUint64(buf64[1*8:2*8], w[1])
			binary.BigEndian.PutUint64(buf64[2*8:3*8], w[2])
			binary.BigEndian.PutUint64(buf64[3*8:4*8], w[3])

			binary.BigEndian.PutUint64(buf64[4*8:5*8], w[4])
			binary.BigEndian.PutUint64(buf64[5*8:6*8], w[5])
			binary.BigEndian.PutUint64(buf64[6*8:7*8], w[6])
			binary.BigEndian.PutUint64(buf64[7*8:8*8], w[7])

			buf.Write(buf64[:])
		}

		for j := M; j < len(p.Coeffs[i]); j++ {
			binary.BigEndian.PutUint64(buf64[0:8], p.Coeffs[i][j])
			buf.Write(buf64[0:8])
		}
	}

	var isNTTByte byte
	if p.IsNTT {
		isNTTByte = 1
	}
	buf.WriteByte(isNTTByte)
}

// ShoupElement is the Shoup form of [Element], precomputed for fast multiplication.
type ShoupElement Element

// GenShoupElement generates a new [ShoupElement] from [Element].
func GenShoupElement(e *Element, mod []*num.Modulus) *ShoupElement {
	checkShape(e.Rank(), len(mod), e)

	coeffs := make([][]uint64, len(mod))
	for i := range coeffs {
		coeffs[i] = vec.SForm(e.Coeffs[i], mod[i])
	}

	return &ShoupElement{
		Coeffs: coeffs,
		IsNTT:  e.IsNTT,
	}
}
