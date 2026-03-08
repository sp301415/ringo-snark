package bigpoly

import (
	"math/big"
	"unsafe"

	"github.com/sp301415/ringo-snark/math/bignum"
)

// transformer computes NTT.
type transformer[E bignum.Uint[E]] interface {
	FwdNTTTo(vOut, v []E)
	InvNTTTo(vOut, v []E)
}

// CyclicTransformer computes cyclic NTT.
type CyclicTransformer[E bignum.Uint[E]] struct {
	rank int

	tw      []E
	twInv   []E
	rankInv E
}

// NewCyclicTransformer creates a new [CyclicTransformer].
func NewCyclicTransformer[E bignum.Uint[E]](rank int) *CyclicTransformer[E] {
	if !isPowerOfTwo(rank) {
		panic("rank must be a power of two")
	}

	var z E
	pNegOneE := z.New()
	pNegOneE.SetBigInt(big.NewInt(-1))
	pNegOne := pNegOneE.BigInt(new(big.Int))
	if new(big.Int).Mod(pNegOne, big.NewInt(int64(2*rank))).Sign() != 0 {
		panic("NTT not supported")
	}
	pBig := new(big.Int).Add(pNegOne, big.NewInt(1))

	t1 := new(big.Int).Div(pNegOne, big.NewInt(int64(rank)))
	t2 := big.NewInt(int64(rank >> 1))

	gBig := new(big.Int)
	gPowBig := new(big.Int)
	g := z.New()
	for x := big.NewInt(2); x.Cmp(pBig) < 0; x.Add(x, big.NewInt(1)) {
		gBig.Exp(x, t1, pBig)
		gPowBig.Exp(gBig, t2, pBig)
		if gPowBig.Cmp(big.NewInt(1)) != 0 {
			g.SetBigInt(gBig)
			break
		}
	}
	gInv := z.New().Inverse(g)

	twRef := make([]E, rank/2)
	twInvRef := make([]E, rank/2)
	twRef[0] = z.New().SetUint64(1)
	twInvRef[0] = z.New().SetUint64(1)
	for i := 1; i < rank/2; i++ {
		twRef[i] = z.New().Mul(twRef[i-1], g)
		twInvRef[i] = z.New().Mul(twInvRef[i-1], gInv)
	}
	bitReverseInPlace(twRef)
	bitReverseInPlace(twInvRef)

	tw := make([]E, rank)
	twInv := make([]E, rank)

	t := rank
	for m := 1; m <= rank/2; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			tw[m+i] = twRef[i]
		}
	}

	t = 1
	for m := rank / 2; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			twInv[m+i] = twInvRef[i]
		}
		t <<= 1
	}

	rankInv := z.New().SetUint64(uint64(rank))
	rankInv.Inverse(rankInv)

	return &CyclicTransformer[E]{
		rank:    rank,
		tw:      tw,
		twInv:   twInv,
		rankInv: rankInv,
	}
}

// FwdNTTTo computes vOut = NTT(v).
func (ntt *CyclicTransformer[E]) FwdNTTTo(vOut, v []E) {
	for i := 0; i < len(vOut); i += 8 {
		cOut := (*[8]E)(unsafe.Pointer(&vOut[i]))
		c0 := (*[8]E)(unsafe.Pointer(&v[i]))

		cOut[0].Set(c0[0])
		cOut[1].Set(c0[1])
		cOut[2].Set(c0[2])
		cOut[3].Set(c0[3])

		cOut[4].Set(c0[4])
		cOut[5].Set(c0[5])
		cOut[6].Set(c0[6])
		cOut[7].Set(c0[7])
	}

	nttInPlace(vOut, ntt.tw)
}

// InvNTTTo computes vOut = INTT(v).
func (ntt *CyclicTransformer[E]) InvNTTTo(vOut, v []E) {
	for i := 0; i < len(vOut); i += 8 {
		cOut := (*[8]E)(unsafe.Pointer(&vOut[i]))
		c0 := (*[8]E)(unsafe.Pointer(&v[i]))

		cOut[0].Set(c0[0])
		cOut[1].Set(c0[1])
		cOut[2].Set(c0[2])
		cOut[3].Set(c0[3])

		cOut[4].Set(c0[4])
		cOut[5].Set(c0[5])
		cOut[6].Set(c0[6])
		cOut[7].Set(c0[7])
	}

	inttInPlace(vOut, ntt.twInv)
	scalarMulVecTo(vOut, vOut, ntt.rankInv)
}

// Rank returns the rank of the transformer.
func (ntt CyclicTransformer[E]) Rank() int {
	return ntt.rank
}

// CyclotomicTransformer computes negacyclic NTT.
type CyclotomicTransformer[E bignum.Uint[E]] struct {
	rank int

	tw      []E
	twInv   []E
	rankInv E
}

// NewCyclotomicTransformer creates a new [CyclotomicTransformer].
func NewCyclotomicTransformer[E bignum.Uint[E]](rank int) *CyclotomicTransformer[E] {
	if !isPowerOfTwo(rank) {
		panic("rank must be a power of two")
	}

	var z E
	pNegOneE := z.New()
	pNegOneE.SetBigInt(big.NewInt(-1))
	pNegOne := pNegOneE.BigInt(new(big.Int))
	if new(big.Int).Mod(pNegOne, big.NewInt(int64(2*rank))).Sign() != 0 {
		panic("NTT not supported")
	}
	pBig := new(big.Int).Add(pNegOne, big.NewInt(1))

	t1 := new(big.Int).Div(pNegOne, big.NewInt(int64(2*rank)))
	t2 := big.NewInt(int64(rank))

	gBig := new(big.Int)
	gPowBig := new(big.Int)
	g := z.New()
	for x := big.NewInt(2); x.Cmp(pBig) < 0; x.Add(x, big.NewInt(1)) {
		gBig.Exp(x, t1, pBig)
		gPowBig.Exp(gBig, t2, pBig)
		if gPowBig.Cmp(big.NewInt(1)) != 0 {
			g.SetBigInt(gBig)
			break
		}
	}
	gInv := z.New().Inverse(g)

	tw := make([]E, rank)
	twInv := make([]E, rank)
	tw[0] = z.New().SetUint64(1)
	twInv[0] = z.New().SetUint64(1)
	for i := 1; i < rank; i++ {
		tw[i] = z.New().Mul(tw[i-1], g)
		twInv[i] = z.New().Mul(twInv[i-1], gInv)
	}
	bitReverseInPlace(tw)
	bitReverseInPlace(twInv)

	rankInv := z.New().SetUint64(uint64(rank))
	rankInv.Inverse(rankInv)

	return &CyclotomicTransformer[E]{
		rank:    rank,
		tw:      tw,
		twInv:   twInv,
		rankInv: rankInv,
	}
}

// FwdNTTTo computes vOut = NTT(v).
func (ntt *CyclotomicTransformer[E]) FwdNTTTo(vOut, v []E) {
	for i := 0; i < len(vOut); i += 8 {
		cOut := (*[8]E)(unsafe.Pointer(&vOut[i]))
		c0 := (*[8]E)(unsafe.Pointer(&v[i]))

		cOut[0].Set(c0[0])
		cOut[1].Set(c0[1])
		cOut[2].Set(c0[2])
		cOut[3].Set(c0[3])

		cOut[4].Set(c0[4])
		cOut[5].Set(c0[5])
		cOut[6].Set(c0[6])
		cOut[7].Set(c0[7])
	}

	nttInPlace(vOut, ntt.tw)
}

// InvNTTTo computes vOut = INTT(v).
func (ntt *CyclotomicTransformer[E]) InvNTTTo(vOut, v []E) {
	for i := 0; i < len(vOut); i += 8 {
		cOut := (*[8]E)(unsafe.Pointer(&vOut[i]))
		c0 := (*[8]E)(unsafe.Pointer(&v[i]))

		cOut[0].Set(c0[0])
		cOut[1].Set(c0[1])
		cOut[2].Set(c0[2])
		cOut[3].Set(c0[3])

		cOut[4].Set(c0[4])
		cOut[5].Set(c0[5])
		cOut[6].Set(c0[6])
		cOut[7].Set(c0[7])
	}

	inttInPlace(vOut, ntt.twInv)
	scalarMulVecTo(vOut, vOut, ntt.rankInv)
}

func nttInPlace[E bignum.Uint[E]](p, tw []E) {
	if len(p) < 32 {
		nttInPlaceRef(p, tw)
		return
	}
	nttInPlaceUnroll(p, tw)
}

func butterfly[E bignum.Uint[E]](u, v, w E) {
	v.Mul(v, w)
	u.Add(u, v)
	v.Add(v, v)
	v.Sub(u, v)
}

func nttInPlaceRef[E bignum.Uint[E]](p, tw []E) {
	N := len(p)

	t := N
	for m := 1; m <= N/2; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				butterfly(p[j], p[j+t], tw[m+i])
			}
		}
	}
}

func nttInPlaceUnroll[E bignum.Uint[E]](p, tw []E) {
	N := len(p)

	t := N / 2
	for j := 0; j < N/2; j += 8 {
		c0 := (*[8]E)(unsafe.Pointer(&p[j]))
		c1 := (*[8]E)(unsafe.Pointer(&p[j+t]))

		butterfly(c0[0], c1[0], tw[1])
		butterfly(c0[1], c1[1], tw[1])
		butterfly(c0[2], c1[2], tw[1])
		butterfly(c0[3], c1[3], tw[1])

		butterfly(c0[4], c1[4], tw[1])
		butterfly(c0[5], c1[5], tw[1])
		butterfly(c0[6], c1[6], tw[1])
		butterfly(c0[7], c1[7], tw[1])
	}

	for m := 2; m <= N/16; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t

			for j := j1; j < j2; j += 8 {
				c0 := (*[8]E)(unsafe.Pointer(&p[j]))
				c1 := (*[8]E)(unsafe.Pointer(&p[j+t]))

				butterfly(c0[0], c1[0], tw[m+i])
				butterfly(c0[1], c1[1], tw[m+i])
				butterfly(c0[2], c1[2], tw[m+i])
				butterfly(c0[3], c1[3], tw[m+i])

				butterfly(c0[4], c1[4], tw[m+i])
				butterfly(c0[5], c1[5], tw[m+i])
				butterfly(c0[6], c1[6], tw[m+i])
				butterfly(c0[7], c1[7], tw[m+i])
			}
		}
	}

	// t = 4, m = N / 8
	for i := 0; i < N/8; i++ {
		j := 8 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		butterfly(c[0], c[4], tw[i+N/8])
		butterfly(c[1], c[5], tw[i+N/8])
		butterfly(c[2], c[6], tw[i+N/8])
		butterfly(c[3], c[7], tw[i+N/8])
	}

	// t = 2, m = N / 4
	for i := 0; i < N/4; i += 2 {
		j := 4 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		butterfly(c[0], c[2], tw[i+N/4])
		butterfly(c[1], c[3], tw[i+N/4])

		butterfly(c[4], c[6], tw[i+N/4+1])
		butterfly(c[5], c[7], tw[i+N/4+1])
	}

	// t = 1, m = N / 2
	for i := 0; i < N/2; i += 4 {
		j := 2 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		butterfly(c[0], c[1], tw[i+N/2+0])
		butterfly(c[2], c[3], tw[i+N/2+1])
		butterfly(c[4], c[5], tw[i+N/2+2])
		butterfly(c[6], c[7], tw[i+N/2+3])
	}
}

func inttInPlace[E bignum.Uint[E]](p, twInv []E) {
	if len(p) < 32 {
		inttInPlaceRef(p, twInv)
		return
	}
	inttInPlaceUnroll(p, twInv)
}

func invButterfly[E bignum.Uint[E]](u, v, w E) {
	u.Add(u, v)
	v.Add(v, v)
	v.Sub(u, v)
	v.Mul(v, w)
}

func inttInPlaceRef[E bignum.Uint[E]](p, twInv []E) {
	N := len(p)

	t := 1
	for m := N / 2; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				invButterfly(p[j], p[j+t], twInv[m+i])
			}
		}
		t <<= 1
	}
}

func inttInPlaceUnroll[E bignum.Uint[E]](p, twInv []E) {
	N := len(p)

	// t = 1, m = N / 2
	for i := 0; i < N/2; i += 4 {
		j := 2 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		invButterfly(c[0], c[1], twInv[i+N/2+0])
		invButterfly(c[2], c[3], twInv[i+N/2+1])
		invButterfly(c[4], c[5], twInv[i+N/2+2])
		invButterfly(c[6], c[7], twInv[i+N/2+3])
	}

	// t = 2, m = N / 4
	for i := 0; i < N/4; i += 2 {
		j := 4 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		invButterfly(c[0], c[2], twInv[i+N/4])
		invButterfly(c[1], c[3], twInv[i+N/4])

		invButterfly(c[4], c[6], twInv[i+N/4+1])
		invButterfly(c[5], c[7], twInv[i+N/4+1])
	}

	// t = 4, m = N / 8
	for i := 0; i < N/8; i++ {
		j := 8 * i

		c := (*[8]E)(unsafe.Pointer(&p[j]))

		invButterfly(c[0], c[4], twInv[i+N/8])
		invButterfly(c[1], c[5], twInv[i+N/8])
		invButterfly(c[2], c[6], twInv[i+N/8])
		invButterfly(c[3], c[7], twInv[i+N/8])
	}

	t := 8
	for m := N / 16; m >= 2; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t

			for j := j1; j < j2; j += 8 {
				c0 := (*[8]E)(unsafe.Pointer(&p[j]))
				c1 := (*[8]E)(unsafe.Pointer(&p[j+t]))

				invButterfly(c0[0], c1[0], twInv[m+i])
				invButterfly(c0[1], c1[1], twInv[m+i])
				invButterfly(c0[2], c1[2], twInv[m+i])
				invButterfly(c0[3], c1[3], twInv[m+i])

				invButterfly(c0[4], c1[4], twInv[m+i])
				invButterfly(c0[5], c1[5], twInv[m+i])
				invButterfly(c0[6], c1[6], twInv[m+i])
				invButterfly(c0[7], c1[7], twInv[m+i])
			}
		}
		t <<= 1
	}

	for j := 0; j < N/2; j += 8 {
		c0 := (*[8]E)(unsafe.Pointer(&p[j]))
		c1 := (*[8]E)(unsafe.Pointer(&p[j+t]))

		invButterfly(c0[0], c1[0], twInv[1])
		invButterfly(c0[1], c1[1], twInv[1])
		invButterfly(c0[2], c1[2], twInv[1])
		invButterfly(c0[3], c1[3], twInv[1])

		invButterfly(c0[4], c1[4], twInv[1])
		invButterfly(c0[5], c1[5], twInv[1])
		invButterfly(c0[6], c1[6], twInv[1])
		invButterfly(c0[7], c1[7], twInv[1])
	}
}

// Rank returns the rank of the transformer.
func (ntt CyclotomicTransformer[E]) Rank() int {
	return ntt.rank
}
