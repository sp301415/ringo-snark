package celpc

import (
	"github.com/sp301415/rlwe-piop/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// GaussianSampler samples from Discrete Gaussian Distribution.
type GaussianSampler struct {
	Parameters Parameters

	*csprng.GaussianSampler
}

// NewGaussianSampler creates a new GaussianSampler.
func NewGaussianSampler(params Parameters) *GaussianSampler {
	return &GaussianSampler{
		Parameters:      params,
		GaussianSampler: csprng.NewGaussianSampler(),
	}
}

// SamplePoly samples a polynomial from the Discrete Gaussian Distribution.
func (s *GaussianSampler) SamplePoly(center, stdDev float64) ring.Poly {
	pOut := s.Parameters.ringQ.NewPoly()
	s.SamplePolyAssign(center, stdDev, pOut)
	return pOut
}

// SamplePolyAssign samples a polynomial from the Discrete Gaussian Distribution and assigns it to pOut.
func (s *GaussianSampler) SamplePolyAssign(center, stdDev float64, pOut ring.Poly) {
	for i := 0; i < s.Parameters.ringQ.N(); i++ {
		c := s.Sample(center, stdDev)
		if c >= 0 {
			for j := 0; j <= s.Parameters.ringQ.Level(); j++ {
				pOut.Coeffs[j][i] = uint64(c)
			}
		} else {
			for j := 0; j <= s.Parameters.ringQ.Level(); j++ {
				pOut.Coeffs[j][i] = uint64(c + int64(s.Parameters.ringQ.SubRings[j].Modulus))
			}
		}
	}

	s.Parameters.ringQ.NTT(pOut, pOut)
	s.Parameters.ringQ.MForm(pOut, pOut)
}
