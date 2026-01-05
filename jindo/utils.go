package jindo

import (
	"encoding/binary"
	"math/bits"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// divMod64 computes x = x / y and returns x mod y.
func divMod64(x []uint64, y uint64) uint64 {
	var r uint64
	for i := len(x) - 1; i >= 0; i-- {
		x[i], r = bits.Div64(r, x[i], y)
	}
	return r
}

// encodeChallengeTo encodes c to pOut.
func encodeChallengeTo(params Parameters, ringQ *ring.Ring, pOut ring.Poly, chalBytes []byte) {
	pOut.Zero()

	c := []uint64{
		binary.BigEndian.Uint64(chalBytes[:8]),
		binary.BigEndian.Uint64(chalBytes[8:]),
	}

	cInfNm := uint64(params.ChallengeBound())
	for i := 0; i < params.ecd.exp; i++ {
		r := divMod64(c, cInfNm)
		if r > cInfNm/2 {
			r = cInfNm - r
			for k := 0; k <= pOut.Level(); k++ {
				pOut.Coeffs[k][i*params.slots] = ringQ.SubRings[k].Modulus - r
			}
		} else {
			for k := 0; k <= pOut.Level(); k++ {
				pOut.Coeffs[k][i*params.slots] = r
			}
		}
	}

	ringQ.MForm(pOut, pOut)
	ringQ.NTT(pOut, pOut)
}

// setCoeffSigned sets the i-th coefficient of pOut to c.
func setCoeffSigned(ringQ *ring.Ring, pOut ring.Poly, c int64, i int) {
	if c >= 0 {
		for l := 0; l <= ringQ.Level(); l++ {
			pOut.Coeffs[l][i] = uint64(c)
		}
	} else {
		for l := 0; l <= ringQ.Level(); l++ {
			qi := int64(ringQ.SubRings[l].Modulus)
			pOut.Coeffs[l][i] = uint64(c%qi + qi)
		}
	}
}

// leftVec computes the left vector during the evaluation protocol.
func leftVec[E bignum.Uint[E]](params Parameters, x E) []E {
	skip := bignum.Exp(x, uint64(params.cols*params.slots))
	left := make([]E, params.rows)
	left[0] = x.New().SetUint64(1)
	for i := 1; i < params.rows; i++ {
		left[i] = x.New().Mul(left[i-1], skip)
	}
	left[params.rows-1] = x.New().Set(x)
	return left
}

// rightVec computes the right vector during the evaluation protocol.
func rightVec[E bignum.Uint[E]](params Parameters, x E) []E {
	right := make([]E, params.cols*params.slots)
	right[0] = x.New().SetUint64(1)
	for i := 1; i < params.cols*params.slots; i++ {
		right[i] = x.New().Mul(right[i-1], x)
	}
	return right
}
