package celpc

import (
	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// COSACSampler samples from Discrete Gaussian Distribution
// with varying center and stdDev.
type COSACSampler struct {
	Parameters Parameters

	*csprng.COSACSampler
}

// NewCOSACSampler creates a new COSACSampler.
//
// Panics when read from crypto/rand or blake2b initialization fails.
func NewCOSACSampler(params Parameters) *COSACSampler {
	return &COSACSampler{
		Parameters:   params,
		COSACSampler: csprng.NewCOSACSampler(),
	}
}

// SamplePoly samples a polynomial from the Discrete Gaussian Distribution.
func (s *COSACSampler) SamplePoly(center, stdDev float64) ring.Poly {
	pOut := s.Parameters.ringQ.NewPoly()
	s.SamplePolyAssign(center, stdDev, pOut)
	return pOut
}

// SamplePolyAssign samples a polynomial from the Discrete Gaussian Distribution and assigns it to pOut.
func (s *COSACSampler) SamplePolyAssign(center, stdDev float64, pOut ring.Poly) {
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

// TwinCDTSampler samples from Discrete Gaussian Distribution
// with varying center and fixed, small stdDev.
type TwinCDTSampler struct {
	Parameters Parameters

	*csprng.TwinCDTSampler
}

// NewTwinCDTSampler creates a new TwinCDTSampler.
//
// Panics when read from crypto/rand or blake2b initialization fails.
func NewTwinCDTSampler(params Parameters, stdDev float64) *TwinCDTSampler {
	return &TwinCDTSampler{
		Parameters:     params,
		TwinCDTSampler: csprng.NewTwinCDTSampler(stdDev),
	}
}

// ShallowCopy creates a copy of Sampler that is thread-safe.
func (s *TwinCDTSampler) ShallowCopy() *TwinCDTSampler {
	return &TwinCDTSampler{
		Parameters:     s.Parameters,
		TwinCDTSampler: s.TwinCDTSampler.ShallowCopy(),
	}
}

// SamplePoly samples a polynomial from the Discrete Gaussian Distribution.
func (s *TwinCDTSampler) SamplePoly(center float64) ring.Poly {
	pOut := s.Parameters.ringQ.NewPoly()
	s.SamplePolyAssign(center, pOut)
	return pOut
}

// SamplePolyAssign samples a polynomial from the Discrete Gaussian Distribution and assigns it to pOut.
func (s *TwinCDTSampler) SamplePolyAssign(center float64, pOut ring.Poly) {
	for i := 0; i < s.Parameters.ringQ.N(); i++ {
		c := s.Sample(center)
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
