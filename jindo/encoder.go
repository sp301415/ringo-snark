package jindo

import (
	"math"
	"math/big"
	"math/bits"
	"sync"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/num"
)

// Encoder encodes large integer vector to small ring elements.
type Encoder[E bignum.Uint[E]] struct {
	op        *crt.Operator
	ecdParams EncodeParameters[E]

	rns *RNSReconstructor[E]

	baseSq    uint64
	baseDivHi uint64

	pool64El *sync.Pool
	pool64   *sync.Pool
	poolE    *sync.Pool
	poolEEl  *sync.Pool
	poolBig  *sync.Pool
}

// NewEncoder creates a new [Encoder].
func NewEncoder[E bignum.Uint[E]](op *crt.Operator, ecdParams EncodeParameters[E]) *Encoder[E] {
	var z E
	l := z.New().Limb()

	baseMod := num.NewModulus(ecdParams.base)
	baseDivHi, _ := baseMod.Div()

	return &Encoder[E]{
		op:        op,
		ecdParams: ecdParams,

		rns: NewRNSReconstructor[E](op),

		baseSq:    ecdParams.base * ecdParams.base,
		baseDivHi: baseDivHi,

		pool64: &sync.Pool{
			New: func() any {
				v := make([]uint64, l)
				return &v
			},
		},
		poolE: &sync.Pool{
			New: func() any {
				var z E
				return z.New()
			},
		},
		poolEEl: &sync.Pool{
			New: func() any {
				v := make([]E, op.Rank())
				for i := range v {
					v[i] = v[i].New()
				}
				return &v
			},
		},
		poolBig: &sync.Pool{
			New: func() any {
				modBits := 0.0
				for _, ql := range op.Modulus() {
					modBits += num.Log2(ql.Value())
				}

				coeffs := make([]*big.Int, op.Rank())
				for i := range coeffs {
					b := make([]byte, int(math.Ceil(modBits/8)))
					coeffs[i] = new(big.Int).SetBytes(b)
				}
				return &coeffs
			},
		},
	}
}

// Encode returns an encoding of v.
func (e *Encoder[E]) Encode(v []E) *crt.Element {
	pOut := e.op.NewPoly()
	e.EncodeTo(pOut, v)
	return pOut
}

// EncodeRawTo encodes v to uint64 slice.
func (e *Encoder[E]) EncodeRawTo(pOut []uint64, v []E) {
	slots := e.op.Rank() / e.ecdParams.exp

	if len(v) > slots {
		panic("inconsistent input(s)")
	}

	clear(pOut)

	vBufPtr := e.pool64.Get().(*[]uint64)
	vBuf := *vBufPtr
	defer e.pool64.Put(vBufPtr)

	for i := range v {
		v[i].Slice(vBuf)
		for j := 0; j < e.ecdParams.exp; j += 2 {
			rSq := divMod64(vBuf, e.baseSq)
			q, _ := bits.Mul64(rSq, e.baseDivHi)
			r := rSq - q*e.ecdParams.base
			if r >= e.ecdParams.base {
				r -= e.ecdParams.base
				q += 1
			}
			pOut[j*slots+i] = r
			pOut[(j+1)*slots+i] = q
		}
		pOut[(e.ecdParams.exp-1)*slots+i] += vBuf[0] * e.ecdParams.base
	}
}

// EncodeTo encodes v to pOut.
func (e *Encoder[E]) EncodeTo(pOut *crt.Element, v []E) {
	e.EncodeRawTo(pOut.Coeffs[0], v)

	for l := 1; l < pOut.ModLen(); l++ {
		copy(pOut.Coeffs[l], pOut.Coeffs[0])
	}

	pOut.IsNTT = false
	e.op.FwdNTTTo(pOut, pOut)
}

// DecodeConstRawSignedTo decodes uint64 slice to vOut.
func (e *Encoder[E]) DecodeConstRawTo(vOut E, p []uint64) {
	slots := e.op.Rank() / e.ecdParams.exp

	baseE := e.poolE.Get().(E)
	defer e.poolE.Put(baseE)
	coeffE := e.poolE.Get().(E)
	defer e.poolE.Put(coeffE)

	baseE.SetUint64(e.ecdParams.base)
	vOut.SetUint64(0)
	for j := e.ecdParams.exp - 1; j >= 0; j-- {
		vOut.Mul(vOut, baseE)
		coeffE.SetUint64(p[j*slots])
		vOut.Add(vOut, coeffE)
	}
}

// DecodeConstRawSignedTo decodes uint64 slice to vOut.
func (e *Encoder[E]) DecodeConstRawSignedTo(vOut E, p []int64) {
	slots := e.op.Rank() / e.ecdParams.exp

	baseE := e.poolE.Get().(E)
	defer e.poolE.Put(baseE)
	coeffE := e.poolE.Get().(E)
	defer e.poolE.Put(coeffE)

	baseE.SetUint64(e.ecdParams.base)
	vOut.SetUint64(0)
	for j := e.ecdParams.exp - 1; j >= 0; j-- {
		vOut.Mul(vOut, baseE)
		coeffE.SetInt64(p[j*slots])
		vOut.Add(vOut, coeffE)
	}
}

// DecodeRawTo decodes uint64 slice to vOut.
func (e *Encoder[E]) DecodeRawTo(vOut []E, p []uint64) {
	slots := e.op.Rank() / e.ecdParams.exp

	if len(vOut) > slots {
		panic("inconsistent input(s)")
	}

	baseE := e.poolE.Get().(E)
	defer e.poolE.Put(baseE)
	coeffE := e.poolE.Get().(E)
	defer e.poolE.Put(coeffE)

	baseE.SetUint64(e.ecdParams.base)
	for i := 0; i < slots; i++ {
		vOut[i].SetUint64(0)
		for j := e.ecdParams.exp - 1; j >= 0; j-- {
			vOut[i].Mul(vOut[i], baseE)
			coeffE.SetInt64(int64(p[j*slots+i]))
			vOut[i].Add(vOut[i], coeffE)
		}
	}
}

// DecodeTo decodes p to vOut.
func (e *Encoder[E]) DecodeTo(vOut []E, p *crt.Element) {
	slots := e.op.Rank() / e.ecdParams.exp

	if p.IsNTT == true || len(vOut) > slots {
		panic("inconsistent input(s)")
	}

	coeffEPtr := e.poolEEl.Get().(*[]E)
	coeffE := *coeffEPtr
	defer e.poolEEl.Put(coeffEPtr)

	baseE := e.poolE.Get().(E)
	defer e.poolE.Put(baseE)

	e.rns.ReconstructToE(coeffE, p)
	baseE.SetUint64(e.ecdParams.base)
	for i := 0; i < slots; i++ {
		vOut[i].SetUint64(0)
		for j := e.ecdParams.exp - 1; j >= 0; j-- {
			vOut[i].Mul(vOut[i], baseE)
			vOut[i].Add(vOut[i], coeffE[j*slots+i])
		}
	}
}
