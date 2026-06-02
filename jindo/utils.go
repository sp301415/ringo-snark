package jindo

import (
	"bytes"
	"encoding/binary"
	"io"
	"math"
	"math/bits"
	"unsafe"

	"github.com/sp301415/ringo-snark/math/bignum"
)

// divMod64 computes x = x / y and returns x mod y.
func divMod64(x []uint64, y uint64) uint64 {
	n := len(x) - 1
	for n > 0 && x[n] == 0 {
		n--
	}

	var r uint64
	for i := n; i >= 0; i-- {
		x[i], r = bits.Div64(r, x[i], y)
	}
	return r
}

// sampleN samples uniformly random value from oracle.
func sampleN(oracle io.Reader, N uint64) uint64 {
	var buf [8]byte
	bound := math.MaxUint64 - math.MaxUint64%N
	for {
		oracle.Read(buf[:])
		x := binary.BigEndian.Uint64(buf[:])
		if x < bound {
			return x % N
		}
	}
}

// writeE writes x to buf.
func writeE[E bignum.Uint[E]](buf *bytes.Buffer, buf64 []uint64, x []E) {
	var buf8 [8]byte

	for i := range x {
		x[i].Slice(buf64)
		for j := range buf64 {
			binary.BigEndian.PutUint64(buf8[:], buf64[j])
			buf.Write(buf8[:])
		}
	}
}

// write64 writes x to buf.
func write64(buf *bytes.Buffer, x []uint64) {
	M := (len(x) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	var buf64 [64]byte

	r := unsafe.Pointer(unsafe.SliceData(x))

	for i := 0; i < M; i += 8 {
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		binary.BigEndian.PutUint64(buf64[0*8:1*8], w[0])
		binary.BigEndian.PutUint64(buf64[1*8:2*8], w[1])
		binary.BigEndian.PutUint64(buf64[2*8:3*8], w[2])
		binary.BigEndian.PutUint64(buf64[3*8:4*8], w[3])

		binary.BigEndian.PutUint64(buf64[4*8:5*8], w[4])
		binary.BigEndian.PutUint64(buf64[5*8:6*8], w[5])
		binary.BigEndian.PutUint64(buf64[6*8:7*8], w[6])
		binary.BigEndian.PutUint64(buf64[7*8:8*8], w[7])

		buf.Write(buf64[:])
	}

	for i := M; i < len(x); i++ {
		binary.BigEndian.PutUint64(buf64[0:8], x[i])
		buf.Write(buf64[0:8])
	}
}

// encodeChalRawTo encodes challenge to pOut as int64 vector.
func encodeChalRawTo(pOut []uint64, oracle io.Reader) {
	clear(pOut)

	var signByte [1]byte
	var idxByte [8]byte
	for i := len(pOut) - chalWeight; i < len(pOut); i++ {
		oracle.Read(signByte[:])
		jBound := math.MaxUint64 - math.MaxUint64%uint64(i)
		var j uint64
		for {
			oracle.Read(idxByte[:])
			j = binary.BigEndian.Uint64(idxByte[:])
			if j < jBound {
				j %= uint64(i)
				break
			}
		}

		pOut[i] = pOut[j]
		if signByte[0]&1 == 0 {
			pOut[j] = 1
		} else {
			pOut[j] = math.MaxUint64
		}
	}
}

// isMixedRadixNegative checks if i-th index of v is negative in signed mixed radix representation.
func isMixedRadixNegative(v [][]uint64, i int, modInHalf []uint64) uint64 {
	for j := len(v) - 1; j >= 0; j-- {
		x := v[j][i]
		qHalf := modInHalf[j]

		if x > qHalf {
			return 1
		}
		if x < qHalf {
			return 0
		}
	}
	return 0
}
