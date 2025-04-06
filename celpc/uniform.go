package celpc

import (
	"crypto/rand"
	"io"
	"math/big"

	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// UniformSampler samples values from uniform distribution.
type UniformSampler struct {
	Parameters Parameters

	*csprng.UniformSampler

	modBuf  []byte
	msbMask byte
}

// NewUniformSampler creates a new UniformSampler.
func NewUniformSampler(params Parameters) *UniformSampler {
	seed := make([]byte, 16)
	if _, err := rand.Read(seed); err != nil {
		panic(err)
	}
	return NewUniformSamplerWithSeed(params, seed)
}

// NewUniformSamplerWithSeed creates a new UniformSampler with seed.
func NewUniformSamplerWithSeed(params Parameters, seed []byte) *UniformSampler {
	k := (params.modulus.BitLen() + 7) / 8
	b := uint(params.modulus.BitLen() % 8)
	if b == 0 {
		b = 8
	}

	modBuf := make([]byte, k)
	msbMask := byte((1 << b) - 1)

	return &UniformSampler{
		Parameters:     params,
		UniformSampler: csprng.NewUniformSamplerWithSeed(seed),

		modBuf:  modBuf,
		msbMask: msbMask,
	}
}

// SamplePolyAssign samples a polynomial uniformly from the ring and assigns it to pOut.
func (s *UniformSampler) SamplePolyAssign(pOut ring.Poly) {
	for i := 0; i <= pOut.Level(); i++ {
		for j := 0; j < pOut.N(); j++ {
			pOut.Coeffs[i][j] = s.SampleN(s.Parameters.ringQ.ModuliChain()[i])
		}
	}
}

// SampleMod samples a uniformly random value modulo modulus.
func (s *UniformSampler) SampleMod() *big.Int {
	r := big.NewInt(0)
	s.SampleModAssign(r)
	return r
}

// SampleModAssign samples a uniformly random value modulo modulus.
func (s *UniformSampler) SampleModAssign(xOut *big.Int) {
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
