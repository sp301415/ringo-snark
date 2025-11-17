package csprng

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"crypto/sha512"
	"math"
)

// bufSize is the default buffer size of [UniformSampler].
const bufSize = 8192

// UniformSampler samples values from uniform distribution.
// This uses AES-CTR as a underlying prng.
type UniformSampler struct {
	prng cipher.Stream

	buf [bufSize]byte
	ptr uint64
}

// NewUniformSampler creates a new [UniformSampler].
//
// Panics when read from crypto/rand or AES initialization fails.
func NewUniformSampler() *UniformSampler {
	var seed [32]byte
	if _, err := rand.Read(seed[:]); err != nil {
		panic(err)
	}

	return NewUniformSamplerWithSeed(seed[:])
}

// NewUniformSamplerWithSeed creates a new [UniformSampler], with user supplied seed.
//
// Panics when AES initialization fails.
func NewUniformSamplerWithSeed(seed []byte) *UniformSampler {
	r := sha512.Sum384(seed)

	block, err := aes.NewCipher(r[:32])
	if err != nil {
		panic(err)
	}

	prng := cipher.NewCTR(block, r[32:])

	return &UniformSampler{
		prng: prng,

		buf: [bufSize]byte{},
		ptr: bufSize,
	}
}

// Read implements the [io.Reader] interface.
// It always succeeds, with n == len(p) and err == nil.
func (s *UniformSampler) Read(p []byte) (n int, err error) {
	s.prng.XORKeyStream(p, p)
	return len(p), nil
}

// Sample uniformly samples a random uint64 value.
func (s *UniformSampler) Sample() uint64 {
	if s.ptr == bufSize {
		s.prng.XORKeyStream(s.buf[:], s.buf[:])
		s.ptr = 0
	}

	var r uint64
	r |= uint64(s.buf[s.ptr+0])
	r |= uint64(s.buf[s.ptr+1]) << 8
	r |= uint64(s.buf[s.ptr+2]) << 16
	r |= uint64(s.buf[s.ptr+3]) << 24
	r |= uint64(s.buf[s.ptr+4]) << 32
	r |= uint64(s.buf[s.ptr+5]) << 40
	r |= uint64(s.buf[s.ptr+6]) << 48
	r |= uint64(s.buf[s.ptr+7]) << 56
	s.ptr += 8

	return r
}

// SampleN uniformly samples a random uint64 value in [0, n).
func (s *UniformSampler) SampleN(n uint64) uint64 {
	bound := math.MaxUint64 - math.MaxUint64%n
	for {
		r := s.Sample()
		if r < bound {
			return r % n
		}
	}
}

// SampleFloat samples a random float64 value in [0, 1).
func (s *UniformSampler) SampleFloat() float64 {
	r := s.Sample() % (1 << floatPrec)
	rf := math.Float64frombits(r | ((1023 + floatPrec) << floatPrec))
	return (rf / (1 << floatPrec)) - 1
}
