package csprng

import "math"

// COSACSampler samples from Discrete Gaussian Distribution
// with varying center and stdDev.
type COSACSampler struct {
	baseSampler    *UniformSampler
	roundedSampler *RoundedGaussianSampler
}

// NewCOSACSampler creates a new [COSACSampler].
//
// Panics when read from crypto/rand or AES initialization fails.
func NewCOSACSampler() *COSACSampler {
	return &COSACSampler{
		baseSampler:    NewUniformSampler(),
		roundedSampler: NewRoundedGaussianSampler(),
	}
}

// sampleRound samples a rounded Gaussian distribution.
func (s *COSACSampler) sampleRound(cFrac, stdDev float64) int64 {
	for {
		y := stdDev * s.roundedSampler.normFloat()
		b := s.baseSampler.Sample() & 1

		var yRound float64
		var cmp bool
		if b == 0 {
			yRound = math.Round(y) - 1
			cmp = yRound <= 0.5
		} else {
			yRound = math.Round(y) + 1
			cmp = yRound >= -0.5
		}

		if cmp {
			r := s.baseSampler.SampleFloat()
			if r < math.Exp(-((yRound+cFrac)*(yRound+cFrac)-y*y)/(2*stdDev*stdDev)) {
				return int64(yRound)
			}
		}
	}
}

// Sample samples from Discrete Gaussian distribution.
func (s *COSACSampler) Sample(center, stdDev float64) int64 {
	cInt := math.Round(center)
	cFrac := cInt - center

	r := s.baseSampler.SampleFloat()
	if r < math.Exp(-(cFrac*cFrac)/(2*stdDev*stdDev))/(math.Sqrt(2*math.Pi)*stdDev) {
		return int64(cInt)
	}
	return s.sampleRound(cFrac, stdDev) + int64(cInt)
}
