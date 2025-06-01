package celpc

import (
	"io"
	"math/big"

	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// StreamSampler samples values from uniform distribution using stream cipher.
type StreamSampler struct {
	Parameters Parameters

	*csprng.StreamSampler

	modBuf  []byte
	msbMask byte
}

// NewStreamSampler creates a new StreamSampler.
func NewStreamSampler(params Parameters) *StreamSampler {
	k := (params.modulus.BitLen() + 7) / 8
	b := uint(params.modulus.BitLen() % 8)
	if b == 0 {
		b = 8
	}

	modBuf := make([]byte, k)
	msbMask := byte((1 << b) - 1)

	return &StreamSampler{
		Parameters:    params,
		StreamSampler: csprng.NewStreamSampler(),

		modBuf:  modBuf,
		msbMask: msbMask,
	}
}

// SamplePolyAssign samples a polynomial uniformly from the ring and assigns it to pOut.
func (s *StreamSampler) SamplePolyAssign(pOut ring.Poly) {
	for i := 0; i <= pOut.Level(); i++ {
		for j := 0; j < pOut.N(); j++ {
			pOut.Coeffs[i][j] = s.SampleN(s.Parameters.ringQ.SubRings[i].Modulus)
		}
	}
}

// SampleMod samples a uniformly random value modulo modulus.
func (s *StreamSampler) SampleMod() *big.Int {
	r := big.NewInt(0)
	s.SampleModAssign(r)
	return r
}

// SampleModAssign samples a uniformly random value modulo modulus.
func (s *StreamSampler) SampleModAssign(xOut *big.Int) {
	for {
		_, err := io.ReadFull(s, s.modBuf)
		if err != nil {
			panic(err)
		}

		s.modBuf[0] &= s.msbMask

		xOut.SetBytes(s.modBuf)
		if xOut.Cmp(s.Parameters.modulus) < 0 {
			return
		}
	}
}
