package celpc

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// RNSReconstructor reconstructs a polynomial from its RNS representation.
type RNSReconstructor struct {
	params  Parameters
	reducer *bigring.Reducer

	rnsGadget []*big.Int
	qHalf     *big.Int

	buffer rnsReconstructorBuffer
}

type rnsReconstructorBuffer struct {
	pInv  ring.Poly
	mul   *big.Int
	coeff *big.Int
}

// NewRNSReconstructor creates a new RNSReconstructor.
func NewRNSReconstructor(params Parameters) *RNSReconstructor {
	rnsGadget := make([]*big.Int, params.ringQ.ModuliChainLength())
	qFull := params.ringQ.Modulus()
	for i := 0; i <= params.ringQ.Level(); i++ {
		qi := big.NewInt(0).SetUint64(params.ringQ.SubRings[i].Modulus)
		qDiv := big.NewInt(0).Div(qFull, qi)
		qInv := big.NewInt(0).ModInverse(qDiv, qi)
		rnsGadget[i] = big.NewInt(0).Mul(qDiv, qInv)
	}

	return &RNSReconstructor{
		params:  params,
		reducer: bigring.NewReducer(params.ringQ.Modulus()),

		rnsGadget: rnsGadget,
		qHalf:     big.NewInt(0).Rsh(params.ringQ.Modulus(), 1),

		buffer: newRNSReconstructorBuffer(params),
	}
}

// newRNSReconstructorBuffer creates a new rnsReconstructorBuffer.
func newRNSReconstructorBuffer(params Parameters) rnsReconstructorBuffer {
	return rnsReconstructorBuffer{
		pInv:  params.ringQ.NewPoly(),
		mul:   big.NewInt(0),
		coeff: big.NewInt(0),
	}
}

// ShallowCopy returns a shallow copy of the RNSReconstructor that is thread-safe.
func (r *RNSReconstructor) ShallowCopy() *RNSReconstructor {
	return &RNSReconstructor{
		params:  r.params,
		reducer: r.reducer.ShallowCopy(),

		rnsGadget: r.rnsGadget,
		qHalf:     r.qHalf,

		buffer: newRNSReconstructorBuffer(r.params),
	}
}

func toBalanced(x uint64, q uint64) int64 {
	if x > q>>1 {
		return int64(x) - int64(q)
	}
	return int64(x)
}

// ReconstructAssign converts a polynomial to a big.Int vector.
func (r *RNSReconstructor) ReconstructAssign(p ring.Poly, v []*big.Int) {
	r.params.ringQ.IMForm(p, r.buffer.pInv)
	r.params.ringQ.INTT(r.buffer.pInv, r.buffer.pInv)

	for i := 0; i < r.params.ringQ.N(); i++ {
		isSmall := true
		cInt64 := toBalanced(r.buffer.pInv.Coeffs[0][i], r.params.ringQ.SubRings[0].Modulus)
		for j := 1; j <= r.params.ringQ.Level(); j++ {
			if cInt64 != toBalanced(r.buffer.pInv.Coeffs[j][i], r.params.ringQ.SubRings[j].Modulus) {
				isSmall = false
				break
			}
		}

		if isSmall {
			v[i].SetInt64(cInt64)
			continue
		}

		v[i].SetInt64(0)
		for j := 0; j <= r.params.ringQ.Level(); j++ {
			r.buffer.mul.SetUint64(r.buffer.pInv.Coeffs[j][i])
			r.buffer.coeff.Mul(r.buffer.mul, r.rnsGadget[j])
			v[i].Add(v[i], r.buffer.coeff)
			r.reducer.Reduce(v[i])
		}

		if v[i].Cmp(r.qHalf) >= 0 {
			v[i].Sub(v[i], r.params.ringQ.Modulus())
		}
	}
}
