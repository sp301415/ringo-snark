package csprng

import (
	"math"
	"slices"
)

const (
	cdtBase = 128
	tailCut = 9
)

// TwinCDTSampler samples from Discrete Gaussian Distribution
// with varying center and fixed, small stdDev.
type TwinCDTSampler struct {
	baseSampler *UniformSampler

	stdDev float64
	tables [cdtBase][]uint64

	tailLo int64
	tailHi int64
}

// NewTwinCDTSampler creates a new TwinCDTSampler.
//
// Panics when read from crypto/rand or blake2b initialization fails.
func NewTwinCDTSampler(stdDev float64) *TwinCDTSampler {
	tables := [cdtBase][]uint64{}
	for i := 0; i < cdtBase; i++ {
		tables[i] = computeCDT(float64(i)/cdtBase, stdDev)
	}

	tailHi := int64(math.Ceil(tailCut * stdDev))
	tailLo := -tailHi

	return &TwinCDTSampler{
		baseSampler: NewUniformSampler(),

		stdDev: stdDev,
		tables: tables,

		tailLo: tailLo,
		tailHi: tailHi,
	}
}

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

// ShallowCopy creates a copy of Sampler that is thread-safe.
func (s *TwinCDTSampler) ShallowCopy() *TwinCDTSampler {
	return &TwinCDTSampler{
		baseSampler: NewUniformSampler(),

		stdDev: s.stdDev,
		tables: s.tables,

		tailLo: s.tailLo,
		tailHi: s.tailHi,
	}
}

// StdDev returns the standard deviation of the sampler.
func (s *TwinCDTSampler) StdDev() float64 {
	return s.stdDev
}

// Sample samples from Discrete Gaussian Distribution.
func (s *TwinCDTSampler) Sample(center float64) int64 {
	cFloor := math.Floor(center)
	cFrac := center - cFloor

	c0 := int64(math.Floor(cdtBase*cFrac)) % cdtBase
	c1 := int64(math.Ceil(cdtBase*cFrac)) % cdtBase

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
func (s *TwinCDTSampler) SampleCoset(center float64) float64 {
	return center + float64(s.Sample(-center))
}
