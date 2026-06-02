package jindo

import (
	"math/big"
	"slices"
	"sync"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
)

// RNSReconstructor reconstructs ring polynomials to int64.
type RNSReconstructor[E bignum.Uint[E]] struct {
	op *crt.Operator

	qBig   []*big.Int
	qProd  *big.Int
	qProdE E

	// modInSorted is the sorted modIn.
	modInSorted []*num.Modulus
	// modInMap is the mapping between modIn and modInSorted.
	modInMap []int

	// modInHalf is half of modIn.
	modInHalf []uint64

	// modInv is the inverse of modIn.
	modInv [][]uint64
	// modInvS is the Shoup form of modIn.
	modInvS [][]uint64

	// baseBig is the basis of MRS.
	baseBig []*big.Int
	// baseE is the basis of MRS.
	baseE []E

	poolBig *sync.Pool
	poolE   *sync.Pool
	pool    *sync.Pool
	pool64  *sync.Pool
}

// NewRNSReconstructor creates a new [RNSReconstructor].
func NewRNSReconstructor[E bignum.Uint[E]](op *crt.Operator) *RNSReconstructor[E] {
	var z E

	qBig := make([]*big.Int, len(op.Modulus()))
	qProd := big.NewInt(1)
	for i := range op.Modulus() {
		qBig[i] = new(big.Int).SetUint64(op.Modulus()[i].Value())
		qProd.Mul(qProd, qBig[i])
	}

	modInSorted := make([]*num.Modulus, len(op.Modulus()))
	copy(modInSorted, op.Modulus())
	slices.SortFunc(modInSorted, num.CmpModulus)

	modInMap := make([]int, len(modInSorted))
	for i := range modInSorted {
		for j, ql := range op.Modulus() {
			if modInSorted[i].Value() == ql.Value() {
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

	baseBig := make([]*big.Int, len(modInSorted))
	baseBig[0] = big.NewInt(1)
	for i := 1; i < len(modInSorted); i++ {
		baseBig[i] = new(big.Int).SetUint64(modInSorted[i-1].Value())
		baseBig[i].Mul(baseBig[i], baseBig[i-1])
	}

	baseE := make([]E, len(modInSorted))
	for i := 0; i < len(modInSorted); i++ {
		baseE[i] = baseE[i].New().SetBigInt(baseBig[i])
	}

	return &RNSReconstructor[E]{
		op: op,

		qBig:   qBig,
		qProd:  qProd,
		qProdE: z.New().SetBigInt(qProd),

		modInSorted: modInSorted,
		modInMap:    modInMap,

		modInHalf: modInHalf,

		modInv:  modInv,
		modInvS: modInvS,

		baseBig: baseBig,
		baseE:   baseE,

		pool64: &sync.Pool{
			New: func() any {
				v := make([]uint64, op.Rank())
				return &v
			},
		},
		pool: &sync.Pool{
			New: func() any {
				return op.NewPoly()
			},
		},
		poolBig: &sync.Pool{
			New: func() any {
				b := make([]byte, (qProd.BitLen()>>8)+1)
				x := big.NewInt(0).SetBytes(b)
				return x
			},
		},
		poolE: &sync.Pool{
			New: func() any {
				var z E
				return z.New()
			},
		},
	}
}

// ReconstructTo reconstructs a polynomial in RNS form to [*big.Int].
func (r *RNSReconstructor[E]) ReconstructTo(vOut []*big.Int, p *crt.Element) {
	M := (r.op.Rank() >> 3) << 3

	eBuf := r.pool.Get().(*crt.Element)
	defer r.pool.Put(eBuf)

	for i := 0; i < len(r.modInSorted); i++ {
		copy(eBuf.Coeffs[i], p.Coeffs[r.modInMap[i]])
	}

	vBoolPtr := r.pool64.Get().(*[]uint64)
	vBool := *vBoolPtr
	defer r.pool64.Put(vBoolPtr)

	for i := 0; i < len(r.modInSorted); i++ {
		for j := i + 1; j < len(r.modInSorted); j++ {
			vec.SubTo(eBuf.Coeffs[j], eBuf.Coeffs[j], eBuf.Coeffs[i], r.modInSorted[j])
			vec.SMulScalarTo(eBuf.Coeffs[j], eBuf.Coeffs[j], r.modInv[i][j-i-1], r.modInvS[i][j-i-1], r.modInSorted[j])
		}
	}

	clear(vBool)
	for i := 0; i < M; i += 8 {
		vBool[i+0] = isMixedRadixNegative(eBuf.Coeffs, i+0, r.modInHalf)
		vBool[i+1] = isMixedRadixNegative(eBuf.Coeffs, i+1, r.modInHalf)
		vBool[i+2] = isMixedRadixNegative(eBuf.Coeffs, i+2, r.modInHalf)
		vBool[i+3] = isMixedRadixNegative(eBuf.Coeffs, i+3, r.modInHalf)

		vBool[i+4] = isMixedRadixNegative(eBuf.Coeffs, i+4, r.modInHalf)
		vBool[i+5] = isMixedRadixNegative(eBuf.Coeffs, i+5, r.modInHalf)
		vBool[i+6] = isMixedRadixNegative(eBuf.Coeffs, i+6, r.modInHalf)
		vBool[i+7] = isMixedRadixNegative(eBuf.Coeffs, i+7, r.modInHalf)
	}
	for i := M; i < r.op.Rank(); i++ {
		vBool[i] = isMixedRadixNegative(eBuf.Coeffs, i, r.modInHalf)
	}

	coeff := r.poolBig.Get().(*big.Int)
	defer r.poolBig.Put(coeff)

	for j := 0; j < r.op.Rank(); j++ {
		vOut[j].SetUint64(eBuf.Coeffs[0][j])
	}

	for i := 1; i < len(r.modInSorted); i++ {
		for j := 0; j < r.op.Rank(); j++ {
			coeff.SetUint64(eBuf.Coeffs[i][j])
			coeff.Mul(coeff, r.baseBig[i])
			vOut[j].Add(vOut[j], coeff)
		}
	}

	for j := 0; j < r.op.Rank(); j++ {
		if vBool[j] == 1 {
			vOut[j].Sub(vOut[j], r.qProd)
		}
	}
}

// ReconstructToE reconstructs a polynomial in RNS form to E.
// It should be guranteed that E > Q, which in our case, is almost certainly true.
func (r *RNSReconstructor[E]) ReconstructToE(vOut []E, p *crt.Element) {
	M := (r.op.Rank() >> 3) << 3

	eBuf := r.pool.Get().(*crt.Element)
	defer r.pool.Put(eBuf)

	for i := 0; i < len(r.modInSorted); i++ {
		copy(eBuf.Coeffs[i], p.Coeffs[r.modInMap[i]])
	}

	vBoolPtr := r.pool64.Get().(*[]uint64)
	vBool := *vBoolPtr
	defer r.pool64.Put(vBoolPtr)

	for i := 0; i < len(r.modInSorted); i++ {
		for j := i + 1; j < len(r.modInSorted); j++ {
			vec.SubTo(eBuf.Coeffs[j], eBuf.Coeffs[j], eBuf.Coeffs[i], r.modInSorted[j])
			vec.SMulScalarTo(eBuf.Coeffs[j], eBuf.Coeffs[j], r.modInv[i][j-i-1], r.modInvS[i][j-i-1], r.modInSorted[j])
		}
	}

	clear(vBool)
	for i := 0; i < M; i += 8 {
		vBool[i+0] = isMixedRadixNegative(eBuf.Coeffs, i+0, r.modInHalf)
		vBool[i+1] = isMixedRadixNegative(eBuf.Coeffs, i+1, r.modInHalf)
		vBool[i+2] = isMixedRadixNegative(eBuf.Coeffs, i+2, r.modInHalf)
		vBool[i+3] = isMixedRadixNegative(eBuf.Coeffs, i+3, r.modInHalf)

		vBool[i+4] = isMixedRadixNegative(eBuf.Coeffs, i+4, r.modInHalf)
		vBool[i+5] = isMixedRadixNegative(eBuf.Coeffs, i+5, r.modInHalf)
		vBool[i+6] = isMixedRadixNegative(eBuf.Coeffs, i+6, r.modInHalf)
		vBool[i+7] = isMixedRadixNegative(eBuf.Coeffs, i+7, r.modInHalf)
	}
	for i := M; i < r.op.Rank(); i++ {
		vBool[i] = isMixedRadixNegative(eBuf.Coeffs, i, r.modInHalf)
	}

	coeffE := r.poolE.Get().(E)
	defer r.poolE.Put(coeffE)

	for j := 0; j < r.op.Rank(); j++ {
		vOut[j].SetUint64(eBuf.Coeffs[0][j])
	}

	for i := 1; i < len(r.modInSorted); i++ {
		for j := 0; j < r.op.Rank(); j++ {
			coeffE.SetUint64(eBuf.Coeffs[i][j])
			coeffE.Mul(coeffE, r.baseE[i])
			vOut[j].Add(vOut[j], coeffE)
		}
	}

	for j := 0; j < r.op.Rank(); j++ {
		if vBool[j] == 1 {
			vOut[j].Sub(vOut[j], r.qProdE)
		}
	}
}

// SetBigCoeffTo sets the coefficient of pOut as v.
func (r *RNSReconstructor[E]) SetBigCoeffTo(pOut *crt.Element, v []*big.Int) {
	accTmp := r.poolBig.Get().(*big.Int)
	defer r.poolBig.Put(accTmp)

	for i := 0; i < r.op.Rank(); i++ {
		for l := range r.op.Modulus() {
			pOut.Coeffs[l][i] = accTmp.Mod(v[i], r.qBig[l]).Uint64()
		}
	}
}
