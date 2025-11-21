package jindo

import (
	"encoding/binary"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// encodeChallengeTo encodes c to pOut.
func encodeChallengeTo(params Parameters, pOut ring.Poly, chalBytes []byte) {
	pOut.Zero()

	c := []uint64{
		binary.BigEndian.Uint64(chalBytes[:8]),
		binary.BigEndian.Uint64(chalBytes[8:]),
	}

	cInfNm := params.ChallengeBound()
	for i := 0; i < params.ecd.exp; i++ {
		r := divMod64(c, cInfNm)
		for k := 0; k <= pOut.Level(); k++ {
			pOut.Coeffs[k][i*params.slots] = r
		}
	}
	params.ringQ.MForm(pOut, pOut)
	params.ringQ.NTT(pOut, pOut)
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
func leftVec[E num.Uint[E]](params Parameters, x E) []E {
	skip := num.ExpE(x, uint64(params.cols*params.slots))
	left := make([]E, params.rows)
	left[0] = x.New().SetUint64(1)
	for i := 1; i < params.rows; i++ {
		left[i] = x.New().Mul(left[i-1], skip)
	}
	left[params.rows-1] = x.New().Set(x)
	return left
}

// rightVec computes the right vector during the evaluation protocol.
func rightVec[E num.Uint[E]](params Parameters, x E) []E {
	right := make([]E, params.cols*params.slots)
	right[0] = x.New().SetUint64(1)
	for i := 1; i < params.cols*params.slots; i++ {
		right[i] = x.New().Mul(right[i-1], x)
	}
	return right
}
