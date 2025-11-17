package csprng

import (
	"math"
)

const (
	blockSize = 128
	floatPrec = 52

	// From "The Ziggurat Method for Generating Random Variables"
	// by Marsaglia and Tsang (2000)
	rn = 3.442619855899
)

var (
	kn [blockSize]uint64
	wn [blockSize]float64
	fn [blockSize]float64
)

func init() {
	v := rn*normal(rn) + normalIntegral(rn)

	var xn [blockSize]float64
	xn[blockSize-1] = rn
	for i := blockSize - 2; i >= 1; i-- {
		xn[i] = normalInv(v/xn[i+1] + normal(xn[i+1]))
	}

	const scale = 1 << floatPrec
	for i := 1; i < blockSize; i++ {
		kn[i] = uint64((xn[i-1] / xn[i]) * scale)
		wn[i] = xn[i] / scale
		fn[i] = normal(xn[i])
	}
	kn[0] = uint64((rn * normal(rn) / v) * scale)
	wn[0] = (v / normal(rn)) / scale
}

func normal(x float64) float64 {
	return math.Exp(-0.5 * x * x)
}

func normalIntegral(x float64) float64 {
	return math.Sqrt(math.Pi/2) * math.Erfc(x/math.Sqrt(2))
}

func normalInv(x float64) float64 {
	return math.Sqrt(-2 * math.Log(x))
}

// RoundedGaussianSampler samples from Rounded Gaussian Distribution, centered around zero.
type RoundedGaussianSampler struct {
	baseSampler *UniformSampler
}

// NewRoundedGaussianSampler creates a new [RoundedGaussianSampler].
//
// Panics when read from crypto/rand or AES initialization fails.
func NewRoundedGaussianSampler() *RoundedGaussianSampler {
	return &RoundedGaussianSampler{
		baseSampler: NewUniformSampler(),
	}
}

// NewRoundedGaussianSamplerWithSeed creates a new [RoundedGaussianSampler], with user supplied seed.
//
// Panics when AES initialization fails.
func NewRoundedGaussianSamplerWithSeed(seed []byte) *RoundedGaussianSampler {
	return &RoundedGaussianSampler{
		baseSampler: NewUniformSamplerWithSeed(seed),
	}
}

// normFloat samples float64 from normal distribution.
func (s *RoundedGaussianSampler) normFloat() float64 {
	for {
		r := s.baseSampler.Sample()

		b := r >> 63
		i := r % (1 << 7)
		j := (r >> 7) % (1 << floatPrec)

		x := float64(int64((j^-b)+b)) * wn[i]

		if j < kn[i] {
			return x
		}

		if i == 0 {
			var u, v float64
			for {
				u = -math.Log(s.baseSampler.SampleFloat()) * (1.0 / rn)
				v = -math.Log(s.baseSampler.SampleFloat())
				if v+v >= u*u {
					break
				}
			}
			u += rn

			if b == 1 {
				return -u
			}
			return u
		}

		f0, f1 := fn[i-1], fn[i]
		if s.baseSampler.SampleFloat()*(f0-f1) < math.Exp(-0.5*x*x)-f1 {
			return x
		}
	}
}

// Sample returns a number sampled from rounded gaussian distribution
// with standard deviation stdDev.
//
// Panics when stdDev <= 0.
func (s *RoundedGaussianSampler) Sample(center, stdDev float64) int64 {
	if stdDev <= 0 {
		panic("standard deviation not positive")
	}

	return int64(math.Round(center + s.normFloat()*stdDev))
}
