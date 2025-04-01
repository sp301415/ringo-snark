package csprng

import (
	"crypto/rand"
	"math"

	"golang.org/x/crypto/blake2b"
)

// bufSize is the default buffer size of UniformSampler.
const bufSize = 8192

// UniformSampler samples values from uniform distribution.
// This uses blake2b as a underlying prng.
type UniformSampler struct {
	prngWriter blake2b.XOF
	prngReader blake2b.XOF

	buf [bufSize]byte
	ptr int
}

// NewUniformSampler creates a new UniformSampler.
//
// Panics when read from crypto/rand or blake2b initialization fails.
func NewUniformSampler() *UniformSampler {
	seed := make([]byte, 16)
	if _, err := rand.Read(seed); err != nil {
		panic(err)
	}
	return NewUniformSamplerWithSeed(seed)
}

// NewUniformSamplerWithSeed creates a new UniformSampler, with user supplied seed.
//
// Panics when blake2b initialization fails.
func NewUniformSamplerWithSeed(seed []byte) *UniformSampler {
	prng, err := blake2b.NewXOF(blake2b.OutputLengthUnknown, nil)
	if err != nil {
		panic(err)
	}

	if _, err = prng.Write(seed); err != nil {
		panic(err)
	}

	return &UniformSampler{
		prngWriter: prng,
		prngReader: prng.Clone(),

		buf: [bufSize]byte{},
		ptr: bufSize,
	}
}

// Read implements the [io.Reader] interface.
func (s *UniformSampler) Read(p []byte) (n int, err error) {
	return s.prngReader.Read(p)
}

// Write implements the [io.Writer] interface.
func (s *UniformSampler) Write(p []byte) (n int, err error) {
	return s.prngWriter.Write(p)
}

// Reset resets the UniformSampler.
func (s *UniformSampler) Reset() {
	s.prngWriter.Reset()
	s.prngReader.Reset()
	s.ptr = bufSize
}

// Finalize finalizes the UniformSampler,
// So that it can read again.
func (s *UniformSampler) Finalize() {
	s.prngReader = s.prngWriter.Clone()
	s.ptr = bufSize
}

// Sample uniformly samples a random integer of type T.
func (s *UniformSampler) Sample() uint64 {
	if s.ptr == bufSize {
		if _, err := s.prngReader.Read(s.buf[:]); err != nil {
			panic(err)
		}
		s.ptr = 0
	}

	var res uint64
	res |= uint64(s.buf[s.ptr+0])
	res |= uint64(s.buf[s.ptr+1]) << 8
	res |= uint64(s.buf[s.ptr+2]) << 16
	res |= uint64(s.buf[s.ptr+3]) << 24
	res |= uint64(s.buf[s.ptr+4]) << 32
	res |= uint64(s.buf[s.ptr+5]) << 40
	res |= uint64(s.buf[s.ptr+6]) << 48
	res |= uint64(s.buf[s.ptr+7]) << 56
	s.ptr += 8

	return res
}

// SampleN uniformly samples a random integer in [0, N).
func (s *UniformSampler) SampleN(N uint64) uint64 {
	bound := math.MaxUint64 - (math.MaxUint64 % N)
	for {
		res := s.Sample()
		if res < bound {
			return res % N
		}
	}
}
