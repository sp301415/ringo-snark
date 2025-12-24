package jindo

import (
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

// RNSReconstructor reconstructs ring polynomials to int64.
type RNSReconstructor struct {
	ringQ *ring.Ring
	qHalf *big.Int

	qBig []*big.Int
	gad  []*big.Int

	buf rnsReconstructorBuffer
}

// rnsReconstructorBuffer is a buffer for [RNSReconstructor].
type rnsReconstructorBuffer struct {
	// coeff is a buffer for coeffiecients.
	coeff *big.Int
	// mul is a buffer for coeff * gadget.
	mul *big.Int
	// acc is the accumulator.
	acc *big.Int
	// accTmp is the temporary buffer for the accumulator.
	accTmp *big.Int
}

// NewRNSReconstructor creates a new [RNSReconstructor].
func NewRNSReconstructor(ringQ *ring.Ring) *RNSReconstructor {
	gad := make([]*big.Int, len(ringQ.SubRings))
	qBig := make([]*big.Int, len(ringQ.SubRings))
	for i := range ringQ.SubRings {
		qi := new(big.Int).SetUint64(ringQ.SubRings[i].Modulus)
		qDiv := new(big.Int).Div(ringQ.Modulus(), qi)
		qInv := new(big.Int).ModInverse(qDiv, qi)
		gad[i] = new(big.Int).Mul(qDiv, qInv)
		gad[i].Mod(gad[i], ringQ.Modulus())
		qBig[i] = qi
	}

	return &RNSReconstructor{
		ringQ: ringQ,
		qHalf: new(big.Int).Rsh(ringQ.Modulus(), 1),

		qBig: qBig,
		gad:  gad,

		buf: newRNSReconstructorBuffer(ringQ),
	}
}

// newRNSReconstructorBuffer creates a new [rnsReconstructorBuffer].
func newRNSReconstructorBuffer(ringQ *ring.Ring) rnsReconstructorBuffer {
	limb := len(ringQ.Modulus().Bits())
	return rnsReconstructorBuffer{
		coeff:  big.NewInt(0).SetBits(make([]big.Word, 2*limb)),
		mul:    big.NewInt(0).SetBits(make([]big.Word, 2*limb)),
		acc:    big.NewInt(0).SetBits(make([]big.Word, 2*limb)),
		accTmp: big.NewInt(0).SetBits(make([]big.Word, 2*limb)),
	}
}

// toBalanced returns the balanced form of x.
func toBalanced(x uint64, q uint64) int64 {
	if x > q>>1 {
		return int64(x) - int64(q)
	}
	return int64(x)
}

// ReconstructTo reconstructs a polynomial in RNS form to [*big.Int].
func (r *RNSReconstructor) ReconstructTo(vOut []*big.Int, p ring.Poly) {
	for i := 0; i < r.ringQ.N(); i++ {
		isSmall := true
		cSigned := toBalanced(p.Coeffs[0][i], r.ringQ.SubRings[0].Modulus)
		for j := 1; j < len(r.ringQ.SubRings); j++ {
			if cSigned != toBalanced(p.Coeffs[j][i], r.ringQ.SubRings[j].Modulus) {
				isSmall = false
				break
			}
		}

		if isSmall {
			vOut[i].SetInt64(cSigned)
			continue
		}

		r.buf.acc.SetUint64(0)
		for j := 0; j < len(r.ringQ.SubRings); j++ {
			r.buf.coeff.SetUint64(p.Coeffs[j][i])
			r.buf.mul.Mul(r.buf.coeff, r.gad[j])
			r.buf.acc.Add(r.buf.acc, r.buf.mul)
		}
		r.buf.accTmp.DivMod(r.buf.acc, r.ringQ.Modulus(), r.buf.acc)

		if r.buf.acc.Cmp(r.qHalf) >= 0 {
			r.buf.acc.Sub(r.buf.acc, r.ringQ.Modulus())
		}
		vOut[i].Set(r.buf.acc)
	}
}

// SetBigCoeffTo sets the coefficient of pOut as v.
func (r *RNSReconstructor) SetBigCoeffTo(pOut ring.Poly, v []*big.Int) {
	for i := 0; i < r.ringQ.N(); i++ {
		for l := range r.ringQ.SubRings {
			pOut.Coeffs[l][i] = r.buf.accTmp.Mod(v[i], r.qBig[l]).Uint64()
		}
	}
}

// SafeCopy returns a thread-safe copy.
func (r *RNSReconstructor) SafeCopy() *RNSReconstructor {
	return &RNSReconstructor{
		ringQ: r.ringQ,
		qHalf: r.qHalf,

		gad:  r.gad,
		qBig: r.qBig,

		buf: newRNSReconstructorBuffer(r.ringQ),
	}
}
