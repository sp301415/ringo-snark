package csprng

import (
	"math"
	"slices"
)

const (
	tailCut = 9
)

// computeCDT computes the Cumulative Distribution Table for a given center and sigma.
func computeCDT(center, sigma float64) []uint64 {
	tailHi := int64(math.Ceil(tailCut * sigma))
	tailLo := -tailHi
	tableSize := int(tailHi - tailLo + 1)

	table := make([]uint64, tableSize)
	cdf := 0.0
	norm := math.Sqrt(2*math.Pi) * sigma
	for i, x := 0, tailLo; x <= tailHi; i, x = i+1, x+1 {
		xf := float64(x)
		rho := math.Exp(-(xf-center)*(xf-center)/(2*sigma*sigma)) / norm
		cdf += rho
		if cdf > 1 {
			table[i] = math.MaxUint64
		} else {
			table[i] = uint64(math.Round(cdf * math.Exp2(64)))
		}
	}

	return table
}

// TwinCDTGaussianSampler samples values from Discrete Gaussian Distribution
// using the Twin-CDT method.
// This allows for variable center, fixed standard deviation sampling.
type TwinCDTGaussianSampler struct {
	baseSampler *UniformSampler

	stdDev float64
	tables [blockSize][]uint64

	tailLo int64
	tailHi int64
}

// NewTwinCDTGaussianSampler creates a new [TwinCDTGaussianSampler].
//
// Panics when read from crypto/rand or AES initialization fails.
func NewTwinCDTGaussianSampler(stdDev float64) *TwinCDTGaussianSampler {
	tables := [blockSize][]uint64{}
	for i := range blockSize {
		tables[i] = computeCDT(float64(i)/blockSize, stdDev)
	}

	tailHi := int64(math.Ceil(tailCut * stdDev))
	tailLo := -tailHi

	return &TwinCDTGaussianSampler{
		baseSampler: NewUniformSampler(),

		stdDev: stdDev,
		tables: tables,

		tailLo: tailLo,
		tailHi: tailHi,
	}
}

// StdDev returns the standard deviation of the sampler.
func (s *TwinCDTGaussianSampler) StdDev() float64 {
	return s.stdDev
}

// Sample samples from Discrete Gaussian Distribution.
func (s *TwinCDTGaussianSampler) Sample(center float64) int64 {
	cFloor := math.Floor(center)
	cFrac := center - cFloor

	c0 := int64(math.Floor(blockSize*cFrac)) % blockSize
	c1 := int64(math.Ceil(blockSize*cFrac)) % blockSize

	u := s.baseSampler.Sample()

	v0, ok := slices.BinarySearch(s.tables[c0], u)
	if ok {
		v0 -= 1
	}
	v1, ok := slices.BinarySearch(s.tables[c1], u)
	if ok {
		v1 -= 1
	}

	if v0 == v1 {
		return int64(v0) + int64(cFloor) + s.tailLo
	}

	cdf := 0.0
	norm := math.Sqrt(2*math.Pi) * s.stdDev
	for x := s.tailLo; x <= int64(v0); x++ {
		xf := float64(x)
		cdf += math.Exp(-(xf-cFrac)*(xf-cFrac)/(2*s.stdDev*s.stdDev)) / norm
	}

	p := float64(u) / math.Exp2(64)
	if p < cdf {
		return int64(v0) + int64(s.tailLo) + int64(cFloor)
	}
	return int64(v1) + int64(s.tailLo) + int64(cFloor)
}

// SampleCoset samples from Discrete Gaussian distribution over a coset.
func (s *TwinCDTGaussianSampler) SampleCoset(center float64) float64 {
	return center + float64(s.Sample(-center))
}

// SafeCopy returns a thread-safe copy.
func (s *TwinCDTGaussianSampler) SafeCopy() *TwinCDTGaussianSampler {
	return &TwinCDTGaussianSampler{
		baseSampler: NewUniformSampler(),

		stdDev: s.stdDev,
		tables: s.tables,

		tailLo: s.tailLo,
		tailHi: s.tailHi,
	}
}
