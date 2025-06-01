package csprng

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/rand"
	"math"
)

// StreamSampler sample values from uniform distribution.
// This uses AES-256 as a underlying prng.
type StreamSampler struct {
	prng cipher.Stream

	buf [bufSize]byte
	ptr int
}

// NewStreamSampler creates a new StreamSampler.
//
// Panics when read from crypto/rand or AES initialization fails.
func NewStreamSampler() *StreamSampler {
	key := make([]byte, 32)
	if _, err := rand.Read(key); err != nil {
		panic(err)
	}

	block, err := aes.NewCipher(key)
	if err != nil {
		panic(err)
	}

	iv := make([]byte, block.BlockSize())
	if _, err := rand.Read(iv); err != nil {
		panic(err)
	}

	prng := cipher.NewCTR(block, iv)

	return &StreamSampler{
		prng: prng,
	}
}

// Read implements the [io.Reader] interface.
func (s *StreamSampler) Read(p []byte) (n int, err error) {
	s.prng.XORKeyStream(p, p)
	return len(p), nil
}

// Sample uniformly samples a random uint64.
func (s *StreamSampler) Sample() uint64 {
	if s.ptr == bufSize {
		s.prng.XORKeyStream(s.buf[:], s.buf[:])
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
func (s *StreamSampler) SampleN(N uint64) uint64 {
	bound := math.MaxUint64 - (math.MaxUint64 % N)
	for {
		res := s.Sample()
		if res < bound {
			return res % N
		}
	}
}
