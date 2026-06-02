package crt

import (
	"slices"
	"sync"
	"unsafe"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

// Embedder embeds a vector or polynomial into different modulus.
// In other words, it computes
//
//	[p]_modIn -> [p]_modOut
//
// It uses mixed-radix representation conversion, so the computation is exact.
type Embedder struct {
	// rank is the rank of inputs.
	rank int
	// modIn is the sorted input modulus.
	modIn []*num.Modulus
	// modOut is the output modulus.
	modOut []*num.Modulus

	// modInMap is the mapping between modIn and modIn sorted.
	modInMap []int

	// modInHalf is half of modIn.
	modInHalf []uint64

	// modInv is the inverse of modIn.
	modInv [][]uint64
	// modInvS is the Shoup form of modIn.
	modInvS [][]uint64

	// base is the mixed-radix basis of modIn.
	base [][]uint64
	// baseS is the Shoup form of base.
	baseS [][]uint64

	// inModOut equals modIn modulo modOut.
	inModOut []uint64

	// idx holds the index of the input modulus limb if it overlaps with the output modulus limb.
	// For example, if modOut[i] = modIn[j], then idx[i] = j.
	// -1 if the input modulus limb does not overlap with the output modulus limb.
	idx []int

	pool   *sync.Pool
	poolIn *sync.Pool
}

// NewEmbedder creates a new [Embedder].
func NewEmbedder(rank int, modOut, modIn []*num.Modulus) *Embedder {
	// if !isCoprime(modIn) || !isCoprime(modOut) {
	// 	panic("modulus must be coprime")
	// }

	modInSorted := make([]*num.Modulus, len(modIn))
	copy(modInSorted, modIn)

	modInMap := make([]int, len(modInSorted))
	for i := range modInSorted {
		for j := range modIn {
			if modInSorted[i].Value() == modIn[j].Value() {
				modInMap[i] = j
				break
			}
		}
	}

	modInHalf := make([]uint64, len(modInSorted))
	for i := 0; i < len(modInSorted); i++ {
		modInHalf[i] = modInSorted[i].Value() >> 1
	}

	modInv := make([][]uint64, len(modInSorted))
	modInvS := make([][]uint64, len(modInSorted))
	for i := 0; i < len(modInSorted); i++ {
		modInv[i] = make([]uint64, len(modInSorted)-i-1)
		modInvS[i] = make([]uint64, len(modInSorted)-i-1)
		for j := 0; j < len(modInSorted)-i-1; j++ {
			modInv[i][j] = num.Inv(modInSorted[i].Value(), modInSorted[i+j+1])
			modInvS[i][j] = num.SForm(modInv[i][j], modInSorted[i+j+1])
		}
	}

	base := make([][]uint64, len(modOut))
	baseS := make([][]uint64, len(modOut))
	for i := 0; i < len(modOut); i++ {
		base[i] = make([]uint64, len(modInSorted))
		baseS[i] = make([]uint64, len(modInSorted))

		base[i][0] = 1
		baseS[i][0] = num.SForm(1, modOut[i])
		for j := 1; j < len(modInSorted); j++ {
			base[i][j] = num.Mul(base[i][j-1], modInSorted[j-1].Value(), modOut[i])
			baseS[i][j] = num.SForm(base[i][j], modOut[i])
		}
	}

	inModOut := make([]uint64, len(modOut))
	idx := make([]int, len(modOut))
	for i := 0; i < len(modOut); i++ {
		inModOut[i] = 1
		idx[i] = -1
		for j := 0; j < len(modInSorted); j++ {
			inModOut[i] = num.Mul(inModOut[i], modInSorted[j].Value(), modOut[i])

			if modOut[i].Value() == modInSorted[j].Value() {
				idx[i] = j
			}
		}
	}

	return &Embedder{
		rank:   rank,
		modIn:  modInSorted,
		modOut: modOut,

		modInMap:  modInMap,
		modInHalf: modInHalf,

		modInv:  modInv,
		modInvS: modInvS,

		base:  base,
		baseS: baseS,

		inModOut: inModOut,

		idx: idx,

		pool: &sync.Pool{
			New: func() any {
				v := make([]uint64, rank)
				return &v
			},
		},
		poolIn: &sync.Pool{
			New: func() any {
				return NewPoly(rank, len(modIn))
			},
		},
	}
}

// EmbedVec returns the embedding of e to the output modulus.
func (emb *Embedder) Embed(e *Element) *Element {
	eOut := NewPoly(e.Rank(), len(emb.modOut))
	emb.EmbedTo(eOut, e)
	return eOut
}

// EmbedTo embeds e to eOut.
// If len(eOut) < len(emb.modOut), it only embeds to len(vOut) elements.
func (emb *Embedder) EmbedTo(eOut, e *Element) {
	M := (emb.rank >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	inLen, outLen := e.ModLen(), eOut.ModLen()
	if e.IsNTT != false || e.Rank() != emb.rank || eOut.Rank() != emb.rank ||
		inLen != len(emb.modIn) || outLen > len(emb.modOut) {
		panic("input(s) not consistent")
	}

	if inLen == 1 {
		qv := emb.modIn[0].Value()
		halfQv := qv >> 1

		vBufPtr := emb.pool.Get().(*[]uint64)
		vBuf := *vBufPtr
		defer emb.pool.Put(vBufPtr)

		r := unsafe.Pointer(unsafe.SliceData(e.Coeffs[0]))

		for i := 0; i < emb.rank; i += 8 {
			wIn := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))
			copy(vBuf[:], wIn[:])

			for j := 0; j < outLen; j++ {
				rOut := unsafe.Pointer(unsafe.SliceData(eOut.Coeffs[j]))
				wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))

				modOut := emb.modOut[j]

				if emb.idx[j] == 0 {
					copy(wOut[:], vBuf[:])
				} else {
					wOut[0] = embedToModOut(vBuf[0], modOut, qv, halfQv)
					wOut[1] = embedToModOut(vBuf[1], modOut, qv, halfQv)
					wOut[2] = embedToModOut(vBuf[2], modOut, qv, halfQv)
					wOut[3] = embedToModOut(vBuf[3], modOut, qv, halfQv)

					wOut[4] = embedToModOut(vBuf[4], modOut, qv, halfQv)
					wOut[5] = embedToModOut(vBuf[5], modOut, qv, halfQv)
					wOut[6] = embedToModOut(vBuf[6], modOut, qv, halfQv)
					wOut[7] = embedToModOut(vBuf[7], modOut, qv, halfQv)
				}
			}
		}

		eOut.IsNTT = false
		return
	}

	eBuf := emb.poolIn.Get().(*Element)
	defer emb.poolIn.Put(eBuf)

	vBoolPtr := emb.pool.Get().(*[]uint64)
	vBool := *vBoolPtr
	defer emb.pool.Put(vBoolPtr)

	vCorrPtr := emb.pool.Get().(*[]uint64)
	vCorr := *vCorrPtr
	defer emb.pool.Put(vCorrPtr)

	for i := 0; i < inLen; i++ {
		copy(eBuf.Coeffs[i], e.Coeffs[emb.modInMap[i]])
	}

	for i := 0; i < outLen; i++ {
		if 0 <= emb.idx[i] && emb.idx[i] < inLen {
			copy(eOut.Coeffs[i], eBuf.Coeffs[emb.idx[i]])
		}
	}

	for i := 0; i < inLen; i++ {
		for j := i + 1; j < inLen; j++ {
			vec.SubTo(eBuf.Coeffs[j], eBuf.Coeffs[j], eBuf.Coeffs[i], emb.modIn[j])
			vec.SMulScalarTo(eBuf.Coeffs[j], eBuf.Coeffs[j], emb.modInv[i][j-i-1], emb.modInvS[i][j-i-1], emb.modIn[j])
		}
	}

	clear(vBool[:])
	for i := 0; i < M; i += 8 {
		vBool[i+0] = isMixedRadixNegative(eBuf.Coeffs, i+0, emb.modInHalf)
		vBool[i+1] = isMixedRadixNegative(eBuf.Coeffs, i+1, emb.modInHalf)
		vBool[i+2] = isMixedRadixNegative(eBuf.Coeffs, i+2, emb.modInHalf)
		vBool[i+3] = isMixedRadixNegative(eBuf.Coeffs, i+3, emb.modInHalf)

		vBool[i+4] = isMixedRadixNegative(eBuf.Coeffs, i+4, emb.modInHalf)
		vBool[i+5] = isMixedRadixNegative(eBuf.Coeffs, i+5, emb.modInHalf)
		vBool[i+6] = isMixedRadixNegative(eBuf.Coeffs, i+6, emb.modInHalf)
		vBool[i+7] = isMixedRadixNegative(eBuf.Coeffs, i+7, emb.modInHalf)
	}
	for i := M; i < emb.rank; i++ {
		vBool[i] = isMixedRadixNegative(eBuf.Coeffs, i, emb.modInHalf)
	}

	for i := 0; i < outLen; i++ {
		if 0 <= emb.idx[i] && emb.idx[i] < inLen {
			continue
		}

		vec.SMulScalarTo(eOut.Coeffs[i], eBuf.Coeffs[0], emb.base[i][0], emb.baseS[i][0], emb.modOut[i])
		for j := 1; j < inLen; j++ {
			vec.SMulAddScalarTo(eOut.Coeffs[i], eBuf.Coeffs[j], emb.base[i][j], emb.baseS[i][j], emb.modOut[i])
		}
		vec.MulScalarTo(vCorr, vBool, emb.inModOut[i], nil)
		vec.SubTo(eOut.Coeffs[i], eOut.Coeffs[i], vCorr, emb.modOut[i])
	}

	eOut.IsNTT = false
}

// Pow2Cutter scales a polynomial to different modulus.
// In other words, it computes
//
//	[p]_modIn -> [(1 / 2^logCut) * p]_modOut
//
// It uses mixed-radix representation conversion, so the computation is exact.
type Pow2Cutter struct {
	// rank is the rank of the inputs.
	rank int
	// modIn is the input modulus.
	modIn []*num.Modulus
	// modOut is the output modulus.
	modOut []*num.Modulus
	// isModInOutEq is true if modIn == modOut.
	isModInOutEq bool

	// embOut is embedder for In -> Out.
	emb *Embedder
	// embCut is embedder for In -> Cut.
	embCut *Embedder
	// embCutOut is the embedder for Cut -> Out.
	embCutOut *Embedder

	// cutInv is the inverse of cut modulo modOut.
	cutInv []uint64
	// cutInvS is the Shoup form of cutInv
	cutInvS []uint64

	pool    *sync.Pool
	poolOut *sync.Pool
}

// NewPow2Cutter creates a new [Pow2Cutter].
func NewPow2Cutter(rank int, modOut, modIn []*num.Modulus, logCut int) *Pow2Cutter {
	// if !isCoprime(modIn) || !isCoprime(modOut) {
	// 	panic("modulus must be coprime")
	// }

	if logCut < 1 || logCut > 63 {
		panic("logCut should be in [1, 63]")
	}
	cut := uint64(1) << logCut
	cutMod := num.NewModulus(cut)

	isModInOutEq := slices.EqualFunc(modOut, modIn, func(a, b *num.Modulus) bool {
		return num.CmpModulus(a, b) == 0
	})

	cutInv := make([]uint64, len(modOut))
	cutInvS := make([]uint64, len(modOut))
	for i := 0; i < len(modOut); i++ {
		cutInv[i] = num.Inv(num.Reduce(cut, modOut[i]), modOut[i])
		cutInvS[i] = num.SForm(cutInv[i], modOut[i])
	}

	return &Pow2Cutter{
		rank:         rank,
		modIn:        modIn,
		modOut:       modOut,
		isModInOutEq: isModInOutEq,

		emb:       NewEmbedder(rank, modOut, modIn),
		embCut:    NewEmbedder(rank, []*num.Modulus{cutMod}, modIn),
		embCutOut: NewEmbedder(rank, modOut, []*num.Modulus{cutMod}),

		cutInv:  cutInv,
		cutInvS: cutInvS,

		pool: &sync.Pool{
			New: func() any {
				v := make([]uint64, rank)
				return &v
			},
		},
		poolOut: &sync.Pool{
			New: func() any {
				return NewPoly(rank, len(modOut))
			},
		},
	}
}

// CutTo cuts e.
func (c *Pow2Cutter) CutTo(eOut, e *Element) {
	eCutPtr := c.pool.Get().(*[]uint64)
	eCut := &Element{Coeffs: [][]uint64{*eCutPtr}, IsNTT: false}
	defer c.pool.Put(eCutPtr)

	eCutOut := c.poolOut.Get().(*Element)
	defer c.poolOut.Put(eCutOut)

	c.embCut.EmbedTo(eCut, e)
	c.embCutOut.EmbedTo(eCutOut, eCut)

	if c.isModInOutEq {
		eOut.CopyFrom(e)
	} else {
		c.emb.EmbedTo(eOut, e)
	}

	for i := 0; i < len(c.modOut); i++ {
		vec.SubTo(eOut.Coeffs[i], eOut.Coeffs[i], eCutOut.Coeffs[i], c.modOut[i])
		vec.SMulScalarTo(eOut.Coeffs[i], eOut.Coeffs[i], c.cutInv[i], c.cutInvS[i], c.modOut[i])
	}
}
