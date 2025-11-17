package bigpoly

import (
	"unsafe"

	"github.com/sp301415/ringo-snark/math/num"
)

func addVecTo[E num.Uint[E]](xOut, x0, x1 []E) {
	M := (len(xOut) >> 3) << 3
	for i := 0; i < M; i += 8 {
		wOut := (*[8]E)(unsafe.Pointer(&xOut[i]))
		w0 := (*[8]E)(unsafe.Pointer(&x0[i]))
		w1 := (*[8]E)(unsafe.Pointer(&x1[i]))

		wOut[0].Add(w0[0], w1[0])
		wOut[1].Add(w0[1], w1[1])
		wOut[2].Add(w0[2], w1[2])
		wOut[3].Add(w0[3], w1[3])

		wOut[4].Add(w0[4], w1[4])
		wOut[5].Add(w0[5], w1[5])
		wOut[6].Add(w0[6], w1[6])
		wOut[7].Add(w0[7], w1[7])
	}

	for i := M; i < len(xOut); i++ {
		xOut[i].Add(x0[i], x1[i])
	}
}

func subVecTo[E num.Uint[E]](xOut, x0, x1 []E) {
	M := (len(xOut) >> 3) << 3
	for i := 0; i < M; i += 8 {
		wOut := (*[8]E)(unsafe.Pointer(&xOut[i]))
		w0 := (*[8]E)(unsafe.Pointer(&x0[i]))
		w1 := (*[8]E)(unsafe.Pointer(&x1[i]))

		wOut[0].Sub(w0[0], w1[0])
		wOut[1].Sub(w0[1], w1[1])
		wOut[2].Sub(w0[2], w1[2])
		wOut[3].Sub(w0[3], w1[3])

		wOut[4].Sub(w0[4], w1[4])
		wOut[5].Sub(w0[5], w1[5])
		wOut[6].Sub(w0[6], w1[6])
		wOut[7].Sub(w0[7], w1[7])
	}

	for i := M; i < len(xOut); i++ {
		xOut[i].Sub(x0[i], x1[i])
	}
}

func negVecTo[E num.Uint[E]](xOut, x0 []E) {
	M := (len(xOut) >> 3) << 3
	for i := 0; i < M; i += 8 {
		wOut := (*[8]E)(unsafe.Pointer(&xOut[i]))
		w0 := (*[8]E)(unsafe.Pointer(&x0[i]))

		wOut[0].Neg(w0[0])
		wOut[1].Neg(w0[1])
		wOut[2].Neg(w0[2])
		wOut[3].Neg(w0[3])

		wOut[4].Neg(w0[4])
		wOut[5].Neg(w0[5])
		wOut[6].Neg(w0[6])
		wOut[7].Neg(w0[7])
	}

	for i := M; i < len(xOut); i++ {
		xOut[i].Neg(x0[i])
	}
}

func scalarMulVecTo[E num.Uint[E]](xOut, x0 []E, c E) {
	M := (len(xOut) >> 3) << 3
	for i := 0; i < M; i += 8 {
		wOut := (*[8]E)(unsafe.Pointer(&xOut[i]))
		w0 := (*[8]E)(unsafe.Pointer(&x0[i]))

		wOut[0].Mul(w0[0], c)
		wOut[1].Mul(w0[1], c)
		wOut[2].Mul(w0[2], c)
		wOut[3].Mul(w0[3], c)

		wOut[4].Mul(w0[4], c)
		wOut[5].Mul(w0[5], c)
		wOut[6].Mul(w0[6], c)
		wOut[7].Mul(w0[7], c)
	}

	for i := M; i < len(xOut); i++ {
		xOut[i].Mul(x0[i], c)
	}
}

func mulVecTo[E num.Uint[E]](xOut, x0, x1 []E) {
	M := (len(xOut) >> 3) << 3
	for i := 0; i < M; i += 8 {
		wOut := (*[8]E)(unsafe.Pointer(&xOut[i]))
		w0 := (*[8]E)(unsafe.Pointer(&x0[i]))
		w1 := (*[8]E)(unsafe.Pointer(&x1[i]))

		wOut[0].Mul(w0[0], w1[0])
		wOut[1].Mul(w0[1], w1[1])
		wOut[2].Mul(w0[2], w1[2])
		wOut[3].Mul(w0[3], w1[3])

		wOut[4].Mul(w0[4], w1[4])
		wOut[5].Mul(w0[5], w1[5])
		wOut[6].Mul(w0[6], w1[6])
		wOut[7].Mul(w0[7], w1[7])
	}

	for i := M; i < len(xOut); i++ {
		xOut[i].Mul(x0[i], x1[i])
	}
}
