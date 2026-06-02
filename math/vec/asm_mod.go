//go:build !(amd64 && !purego)

package vec

import (
	"unsafe"

	"github.com/sp301415/ringo-snark/math/internal/modops"
	"github.com/sp301415/ringo-snark/math/num"
)

// AddTo computes vOut = v0 + v1 mod q.
// x0 and x1 must be in [0, q).
// If q is nil, then it returns x0 + x1.
func AddTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	if q != nil {
		addTo(vOut, v0, v1, q)
		return
	}
	addWordTo(vOut, v0, v1)
}

// addTo computes vOut = v0 + v1 mod q.
func addTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = modops.Add(w0[0], w1[0], qv)
		wOut[1] = modops.Add(w0[1], w1[1], qv)
		wOut[2] = modops.Add(w0[2], w1[2], qv)
		wOut[3] = modops.Add(w0[3], w1[3], qv)

		wOut[4] = modops.Add(w0[4], w1[4], qv)
		wOut[5] = modops.Add(w0[5], w1[5], qv)
		wOut[6] = modops.Add(w0[6], w1[6], qv)
		wOut[7] = modops.Add(w0[7], w1[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Add(v0[i], v1[i], qv)
	}
}

// addWordTo computes vOut = v0 + v1.
func addWordTo(vOut, v0, v1 []uint64) {
	checkLength(len(vOut), len(v0), len(v1))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = w0[0] + w1[0]
		wOut[1] = w0[1] + w1[1]
		wOut[2] = w0[2] + w1[2]
		wOut[3] = w0[3] + w1[3]

		wOut[4] = w0[4] + w1[4]
		wOut[5] = w0[5] + w1[5]
		wOut[6] = w0[6] + w1[6]
		wOut[7] = w0[7] + w1[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = v0[i] + v1[i]
	}
}

// AddScalarTo computes vOut = v + c mod q.
// v and c must be in [0, q).
// If q is nil, then it returns v + c.
func AddScalarTo(vOut, v []uint64, c uint64, q *num.Modulus) {
	if q != nil {
		addScalarTo(vOut, v, c, q)
		return
	}
	addScalarWordTo(vOut, v, c)
}

// addScalarTo computes vOut = v + c mod q.
func addScalarTo(vOut, v []uint64, c uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.Add(w[0], c, qv)
		wOut[1] = modops.Add(w[1], c, qv)
		wOut[2] = modops.Add(w[2], c, qv)
		wOut[3] = modops.Add(w[3], c, qv)

		wOut[4] = modops.Add(w[4], c, qv)
		wOut[5] = modops.Add(w[5], c, qv)
		wOut[6] = modops.Add(w[6], c, qv)
		wOut[7] = modops.Add(w[7], c, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Add(v[i], c, qv)
	}
}

// addScalarWordTo computes vOut = v + c.
func addScalarWordTo(vOut []uint64, v []uint64, c uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = w[0] + c
		wOut[1] = w[1] + c
		wOut[2] = w[2] + c
		wOut[3] = w[3] + c

		wOut[4] = w[4] + c
		wOut[5] = w[5] + c
		wOut[6] = w[6] + c
		wOut[7] = w[7] + c
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = c + v[i]
	}
}

// Sub returns v0 - v1 mod q.
// v0 and v1 must be in [0, q).
// If q is nil, then it returns v0 - v1.
func SubTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	if q != nil {
		subTo(vOut, v0, v1, q)
		return
	}
	subWordTo(vOut, v0, v1)
}

// subTo computes vOut = v0 - v1 mod q.
func subTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = modops.Sub(w0[0], w1[0], qv)
		wOut[1] = modops.Sub(w0[1], w1[1], qv)
		wOut[2] = modops.Sub(w0[2], w1[2], qv)
		wOut[3] = modops.Sub(w0[3], w1[3], qv)

		wOut[4] = modops.Sub(w0[4], w1[4], qv)
		wOut[5] = modops.Sub(w0[5], w1[5], qv)
		wOut[6] = modops.Sub(w0[6], w1[6], qv)
		wOut[7] = modops.Sub(w0[7], w1[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Sub(v0[i], v1[i], qv)
	}
}

// subWordTo computes vOut = v0 - v1.
func subWordTo(vOut, v0, v1 []uint64) {
	checkLength(len(vOut), len(v0), len(v1))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = w0[0] - w1[0]
		wOut[1] = w0[1] - w1[1]
		wOut[2] = w0[2] - w1[2]
		wOut[3] = w0[3] - w1[3]

		wOut[4] = w0[4] - w1[4]
		wOut[5] = w0[5] - w1[5]
		wOut[6] = w0[6] - w1[6]
		wOut[7] = w0[7] - w1[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = v0[i] - v1[i]
	}
}

// SubScalar returns v - c mod q.
// v and c must be in [0, q).
// If q is nil, then it returns v - c.
func SubScalarTo(vOut, v []uint64, c uint64, q *num.Modulus) {
	if q != nil {
		subScalarTo(vOut, v, c, q)
		return
	}
	subScalarWordTo(vOut, v, c)
}

// subScalarTo computes vOut = v - c mod q.
func subScalarTo(vOut, v []uint64, c uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.Sub(w[0], c, qv)
		wOut[1] = modops.Sub(w[1], c, qv)
		wOut[2] = modops.Sub(w[2], c, qv)
		wOut[3] = modops.Sub(w[3], c, qv)

		wOut[4] = modops.Sub(w[4], c, qv)
		wOut[5] = modops.Sub(w[5], c, qv)
		wOut[6] = modops.Sub(w[6], c, qv)
		wOut[7] = modops.Sub(w[7], c, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Sub(v[i], c, qv)
	}
}

// subScalarWordTo computes vOut = v - c.
func subScalarWordTo(vOut, v []uint64, c uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = w[0] - c
		wOut[1] = w[1] - c
		wOut[2] = w[2] - c
		wOut[3] = w[3] - c

		wOut[4] = w[4] - c
		wOut[5] = w[5] - c
		wOut[6] = w[6] - c
		wOut[7] = w[7] - c
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = v[i] - c
	}
}

// negTo computes vOut = -v mod q.
func negTo(vOut, v []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.Neg(w[0], qv)
		wOut[1] = modops.Neg(w[1], qv)
		wOut[2] = modops.Neg(w[2], qv)
		wOut[3] = modops.Neg(w[3], qv)

		wOut[4] = modops.Neg(w[4], qv)
		wOut[5] = modops.Neg(w[5], qv)
		wOut[6] = modops.Neg(w[6], qv)
		wOut[7] = modops.Neg(w[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Neg(v[i], qv)
	}
}

// negWordTo computes vOut = -v.
func negWordTo(vOut, v []uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = -w[0]
		wOut[1] = -w[1]
		wOut[2] = -w[2]
		wOut[3] = -w[3]

		wOut[4] = -w[4]
		wOut[5] = -w[5]
		wOut[6] = -w[6]
		wOut[7] = -w[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = -v[i]
	}
}

// mulScalarWordTo computes vOut = v * c.
func mulScalarWordTo(vOut, v []uint64, c uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = w[0] * c
		wOut[1] = w[1] * c
		wOut[2] = w[2] * c
		wOut[3] = w[3] * c

		wOut[4] = w[4] * c
		wOut[5] = w[5] * c
		wOut[6] = w[6] * c
		wOut[7] = w[7] * c
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = v[i] * c
	}
}

// mulAddScalarWordTo computes vOut += v * c.
func mulAddScalarWordTo(vOut, v []uint64, c uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))
		wOut[0] += w[0] * c
		wOut[1] += w[1] * c
		wOut[2] += w[2] * c
		wOut[3] += w[3] * c

		wOut[4] += w[4] * c
		wOut[5] += w[5] * c
		wOut[6] += w[6] * c
		wOut[7] += w[7] * c
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += v[i] * c
	}
}

// mulSubScalarWordTo computes vOut -= v * c.
func mulSubScalarWordTo(vOut, v []uint64, c uint64) {
	checkLength(len(vOut), len(v))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] -= w[0] * c
		wOut[1] -= w[1] * c
		wOut[2] -= w[2] * c
		wOut[3] -= w[3] * c

		wOut[4] -= w[4] * c
		wOut[5] -= w[5] * c
		wOut[6] -= w[6] * c
		wOut[7] -= w[7] * c
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] -= v[i] * c
	}
}

// SMulScalarTo computes vOut = v * c mod q using Shoup multiplication.
func SMulScalarTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.SMul(w[0], c, cS, qv)
		wOut[1] = modops.SMul(w[1], c, cS, qv)
		wOut[2] = modops.SMul(w[2], c, cS, qv)
		wOut[3] = modops.SMul(w[3], c, cS, qv)

		wOut[4] = modops.SMul(w[4], c, cS, qv)
		wOut[5] = modops.SMul(w[5], c, cS, qv)
		wOut[6] = modops.SMul(w[6], c, cS, qv)
		wOut[7] = modops.SMul(w[7], c, cS, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.SMul(v[i], c, cS, qv)
	}
}

// SMulAddScalarTo computes vOut += v * c mod q using Shoup multiplication.
func SMulAddScalarTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.Add(wOut[0], modops.SMul(w[0], c, cS, qv), qv)
		wOut[1] = modops.Add(wOut[1], modops.SMul(w[1], c, cS, qv), qv)
		wOut[2] = modops.Add(wOut[2], modops.SMul(w[2], c, cS, qv), qv)
		wOut[3] = modops.Add(wOut[3], modops.SMul(w[3], c, cS, qv), qv)

		wOut[4] = modops.Add(wOut[4], modops.SMul(w[4], c, cS, qv), qv)
		wOut[5] = modops.Add(wOut[5], modops.SMul(w[5], c, cS, qv), qv)
		wOut[6] = modops.Add(wOut[6], modops.SMul(w[6], c, cS, qv), qv)
		wOut[7] = modops.Add(wOut[7], modops.SMul(w[7], c, cS, qv), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Add(vOut[i], modops.SMul(v[i], c, cS, qv), qv)
	}
}

// SMulSubScalarTo computes vOut -= v * c mod q using Shoup multiplication.
func SMulSubScalarTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.Sub(wOut[0], modops.SMul(w[0], c, cS, qv), qv)
		wOut[1] = modops.Sub(wOut[1], modops.SMul(w[1], c, cS, qv), qv)
		wOut[2] = modops.Sub(wOut[2], modops.SMul(w[2], c, cS, qv), qv)
		wOut[3] = modops.Sub(wOut[3], modops.SMul(w[3], c, cS, qv), qv)

		wOut[4] = modops.Sub(wOut[4], modops.SMul(w[4], c, cS, qv), qv)
		wOut[5] = modops.Sub(wOut[5], modops.SMul(w[5], c, cS, qv), qv)
		wOut[6] = modops.Sub(wOut[6], modops.SMul(w[6], c, cS, qv), qv)
		wOut[7] = modops.Sub(wOut[7], modops.SMul(w[7], c, cS, qv), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Sub(vOut[i], modops.SMul(v[i], c, cS, qv), qv)
	}
}

// SMulScalarLazyTo computes vOut = v * c mod q using Shoup multiplication,
// but the result is in [0, 2q).
//
// Panics if q is nil.
func SMulScalarLazyTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] = modops.SMulLazy(w[0], c, cS, qv)
		wOut[1] = modops.SMulLazy(w[1], c, cS, qv)
		wOut[2] = modops.SMulLazy(w[2], c, cS, qv)
		wOut[3] = modops.SMulLazy(w[3], c, cS, qv)

		wOut[4] = modops.SMulLazy(w[4], c, cS, qv)
		wOut[5] = modops.SMulLazy(w[5], c, cS, qv)
		wOut[6] = modops.SMulLazy(w[6], c, cS, qv)
		wOut[7] = modops.SMulLazy(w[7], c, cS, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.SMulLazy(v[i], c, cS, qv)
	}
}

// SMulAddScalarLazyTo computes vOut += v * c mod q using Shoup multiplication,
// but the result is in [0, 3q).
//
// Panics if q is nil.
func SMulAddScalarLazyTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] += modops.SMulLazy(w[0], c, cS, qv)
		wOut[1] += modops.SMulLazy(w[1], c, cS, qv)
		wOut[2] += modops.SMulLazy(w[2], c, cS, qv)
		wOut[3] += modops.SMulLazy(w[3], c, cS, qv)

		wOut[4] += modops.SMulLazy(w[4], c, cS, qv)
		wOut[5] += modops.SMulLazy(w[5], c, cS, qv)
		wOut[6] += modops.SMulLazy(w[6], c, cS, qv)
		wOut[7] += modops.SMulLazy(w[7], c, cS, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += modops.SMulLazy(v[i], c, cS, qv)
	}
}

// SMulSubScalarLazyTo computes vOut -= v * c mod q using Shoup multiplication,
// but the result is in [0, 3q).
//
// Panics if q is nil.
func SMulSubScalarLazyTo(vOut, v []uint64, c, cS uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v))

	qv := q.Value()

	cNeg := modops.Neg(c, qv)
	var cNegS uint64
	if qv&1 == 1 {
		cNegS = -cS - 1
	} else {
		cNegS = modops.SForm(cNeg, qv)
	}

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r := unsafe.Pointer(unsafe.SliceData(v))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w := (*[8]uint64)(unsafe.Add(r, uintptr(i)*L))

		wOut[0] += modops.SMulLazy(w[0], cNeg, cNegS, qv)
		wOut[1] += modops.SMulLazy(w[1], cNeg, cNegS, qv)
		wOut[2] += modops.SMulLazy(w[2], cNeg, cNegS, qv)
		wOut[3] += modops.SMulLazy(w[3], cNeg, cNegS, qv)

		wOut[4] += modops.SMulLazy(w[4], cNeg, cNegS, qv)
		wOut[5] += modops.SMulLazy(w[5], cNeg, cNegS, qv)
		wOut[6] += modops.SMulLazy(w[6], cNeg, cNegS, qv)
		wOut[7] += modops.SMulLazy(w[7], cNeg, cNegS, qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += modops.SMulLazy(v[i], cNeg, cNegS, qv)
	}
}

// mulWordTo computes vOut = v0 * v1.
func mulWordTo(vOut, v0, v1 []uint64) {
	checkLength(len(vOut), len(v0), len(v1))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = w0[0] * w1[0]
		wOut[1] = w0[1] * w1[1]
		wOut[2] = w0[2] * w1[2]
		wOut[3] = w0[3] * w1[3]

		wOut[4] = w0[4] * w1[4]
		wOut[5] = w0[5] * w1[5]
		wOut[6] = w0[6] * w1[6]
		wOut[7] = w0[7] * w1[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = v0[i] * v1[i]
	}
}

// mulAddWordTo computes vOut += v0 * v1.
func mulAddWordTo(vOut, v0, v1 []uint64) {
	checkLength(len(vOut), len(v0), len(v1))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] += w0[0] * w1[0]
		wOut[1] += w0[1] * w1[1]
		wOut[2] += w0[2] * w1[2]
		wOut[3] += w0[3] * w1[3]

		wOut[4] += w0[4] * w1[4]
		wOut[5] += w0[5] * w1[5]
		wOut[6] += w0[6] * w1[6]
		wOut[7] += w0[7] * w1[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += v0[i] * v1[i]
	}
}

// mulSubWordTo computes vOut -= v0 * v1.
func mulSubWordTo(vOut, v0, v1 []uint64) {
	checkLength(len(vOut), len(v0), len(v1))

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] -= w0[0] * w1[0]
		wOut[1] -= w0[1] * w1[1]
		wOut[2] -= w0[2] * w1[2]
		wOut[3] -= w0[3] * w1[3]

		wOut[4] -= w0[4] * w1[4]
		wOut[5] -= w0[5] * w1[5]
		wOut[6] -= w0[6] * w1[6]
		wOut[7] -= w0[7] * w1[7]
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] -= v0[i] * v1[i]
	}
}

// mulTo computes vOut = v0 * v1 mod q using Barrett reduction.
func mulTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1))

	qv := q.Value()
	divHi, divLo := q.Div()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = modops.FMul(w0[0], w1[0], qv)
		wOut[1] = modops.FMul(w0[1], w1[1], qv)
		wOut[2] = modops.FMul(w0[2], w1[2], qv)
		wOut[3] = modops.FMul(w0[3], w1[3], qv)

		wOut[4] = modops.FMul(w0[4], w1[4], qv)
		wOut[5] = modops.FMul(w0[5], w1[5], qv)
		wOut[6] = modops.FMul(w0[6], w1[6], qv)
		wOut[7] = modops.FMul(w0[7], w1[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.BMul(v0[i], v1[i], qv, divHi, divLo)
	}
}

// mulAddTo computes vOut += v0 * v1 mod q using Barrett reduction.
func mulAddTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1))

	qv := q.Value()
	divHi, divLo := q.Div()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = modops.Add(wOut[0], modops.BMul(w0[0], w1[0], qv, divHi, divLo), qv)
		wOut[1] = modops.Add(wOut[1], modops.BMul(w0[1], w1[1], qv, divHi, divLo), qv)
		wOut[2] = modops.Add(wOut[2], modops.BMul(w0[2], w1[2], qv, divHi, divLo), qv)
		wOut[3] = modops.Add(wOut[3], modops.BMul(w0[3], w1[3], qv, divHi, divLo), qv)

		wOut[4] = modops.Add(wOut[4], modops.BMul(w0[4], w1[4], qv, divHi, divLo), qv)
		wOut[5] = modops.Add(wOut[5], modops.BMul(w0[5], w1[5], qv, divHi, divLo), qv)
		wOut[6] = modops.Add(wOut[6], modops.BMul(w0[6], w1[6], qv, divHi, divLo), qv)
		wOut[7] = modops.Add(wOut[7], modops.BMul(w0[7], w1[7], qv, divHi, divLo), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Add(vOut[i], modops.BMul(v0[i], v1[i], qv, divHi, divLo), qv)
	}
}

// mulSubTo computes vOut -= v0 * v1 mod q using Barrett reduction.
func mulSubTo(vOut, v0, v1 []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1))

	qv := q.Value()
	divHi, divLo := q.Div()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))

		wOut[0] = modops.Sub(wOut[0], modops.BMul(w0[0], w1[0], qv, divHi, divLo), qv)
		wOut[1] = modops.Sub(wOut[1], modops.BMul(w0[1], w1[1], qv, divHi, divLo), qv)
		wOut[2] = modops.Sub(wOut[2], modops.BMul(w0[2], w1[2], qv, divHi, divLo), qv)
		wOut[3] = modops.Sub(wOut[3], modops.BMul(w0[3], w1[3], qv, divHi, divLo), qv)

		wOut[4] = modops.Sub(wOut[4], modops.BMul(w0[4], w1[4], qv, divHi, divLo), qv)
		wOut[5] = modops.Sub(wOut[5], modops.BMul(w0[5], w1[5], qv, divHi, divLo), qv)
		wOut[6] = modops.Sub(wOut[6], modops.BMul(w0[6], w1[6], qv, divHi, divLo), qv)
		wOut[7] = modops.Sub(wOut[7], modops.BMul(w0[7], w1[7], qv, divHi, divLo), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Sub(vOut[i], modops.BMul(v0[i], v1[i], qv, divHi, divLo), qv)
	}
}

// SMulTo computes vOut = v0 * v1 mod q using Shoup multiplication.
//
// Panics if q is nil.
func SMulTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] = modops.SMul(w0[0], w1[0], w1S[0], qv)
		wOut[1] = modops.SMul(w0[1], w1[1], w1S[1], qv)
		wOut[2] = modops.SMul(w0[2], w1[2], w1S[2], qv)
		wOut[3] = modops.SMul(w0[3], w1[3], w1S[3], qv)

		wOut[4] = modops.SMul(w0[4], w1[4], w1S[4], qv)
		wOut[5] = modops.SMul(w0[5], w1[5], w1S[5], qv)
		wOut[6] = modops.SMul(w0[6], w1[6], w1S[6], qv)
		wOut[7] = modops.SMul(w0[7], w1[7], w1S[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.SMul(v0[i], v1[i], v1S[i], qv)
	}
}

// SMulAddTo computes vOut += v0 * v1 mod q using Shoup multiplication.
//
// Panics if q is nil.
func SMulAddTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] = modops.Add(wOut[0], modops.SMul(w0[0], w1[0], w1S[0], qv), qv)
		wOut[1] = modops.Add(wOut[1], modops.SMul(w0[1], w1[1], w1S[1], qv), qv)
		wOut[2] = modops.Add(wOut[2], modops.SMul(w0[2], w1[2], w1S[2], qv), qv)
		wOut[3] = modops.Add(wOut[3], modops.SMul(w0[3], w1[3], w1S[3], qv), qv)

		wOut[4] = modops.Add(wOut[4], modops.SMul(w0[4], w1[4], w1S[4], qv), qv)
		wOut[5] = modops.Add(wOut[5], modops.SMul(w0[5], w1[5], w1S[5], qv), qv)
		wOut[6] = modops.Add(wOut[6], modops.SMul(w0[6], w1[6], w1S[6], qv), qv)
		wOut[7] = modops.Add(wOut[7], modops.SMul(w0[7], w1[7], w1S[7], qv), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Add(vOut[i], modops.SMul(v0[i], v1[i], v1S[i], qv), qv)
	}
}

// SMulSubTo computes vOut -= v0 * v1 mod q using Shoup multiplication.
//
// Panics if q is nil.
func SMulSubTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] = modops.Sub(wOut[0], modops.SMul(w0[0], w1[0], w1S[0], qv), qv)
		wOut[1] = modops.Sub(wOut[1], modops.SMul(w0[1], w1[1], w1S[1], qv), qv)
		wOut[2] = modops.Sub(wOut[2], modops.SMul(w0[2], w1[2], w1S[2], qv), qv)
		wOut[3] = modops.Sub(wOut[3], modops.SMul(w0[3], w1[3], w1S[3], qv), qv)

		wOut[4] = modops.Sub(wOut[4], modops.SMul(w0[4], w1[4], w1S[4], qv), qv)
		wOut[5] = modops.Sub(wOut[5], modops.SMul(w0[5], w1[5], w1S[5], qv), qv)
		wOut[6] = modops.Sub(wOut[6], modops.SMul(w0[6], w1[6], w1S[6], qv), qv)
		wOut[7] = modops.Sub(wOut[7], modops.SMul(w0[7], w1[7], w1S[7], qv), qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.Sub(vOut[i], modops.SMul(v0[i], v1[i], v1S[i], qv), qv)
	}
}

// SMulLazyTo computes vOut = v0 * v1 mod q using Shoup multiplication,
// but the result is in [0, 2q).
//
// Panics if q is nil.
func SMulLazyTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] = modops.SMulLazy(w0[0], w1[0], w1S[0], qv)
		wOut[1] = modops.SMulLazy(w0[1], w1[1], w1S[1], qv)
		wOut[2] = modops.SMulLazy(w0[2], w1[2], w1S[2], qv)
		wOut[3] = modops.SMulLazy(w0[3], w1[3], w1S[3], qv)

		wOut[4] = modops.SMulLazy(w0[4], w1[4], w1S[4], qv)
		wOut[5] = modops.SMulLazy(w0[5], w1[5], w1S[5], qv)
		wOut[6] = modops.SMulLazy(w0[6], w1[6], w1S[6], qv)
		wOut[7] = modops.SMulLazy(w0[7], w1[7], w1S[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] = modops.SMulLazy(v0[i], v1[i], v1S[i], qv)
	}
}

// SMulAddLazyTo computes vOut += v0 * v1 mod q using Shoup multiplication,
// but the result is in [0, 3q).
//
// Panics if q is nil.
func SMulAddLazyTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] += modops.SMulLazy(w0[0], w1[0], w1S[0], qv)
		wOut[1] += modops.SMulLazy(w0[1], w1[1], w1S[1], qv)
		wOut[2] += modops.SMulLazy(w0[2], w1[2], w1S[2], qv)
		wOut[3] += modops.SMulLazy(w0[3], w1[3], w1S[3], qv)

		wOut[4] += modops.SMulLazy(w0[4], w1[4], w1S[4], qv)
		wOut[5] += modops.SMulLazy(w0[5], w1[5], w1S[5], qv)
		wOut[6] += modops.SMulLazy(w0[6], w1[6], w1S[6], qv)
		wOut[7] += modops.SMulLazy(w0[7], w1[7], w1S[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += modops.SMulLazy(v0[i], v1[i], v1S[i], qv)
	}
}

// SMulSubLazyTo computes vOut -= v0 * v1 mod q using Shoup multiplication,
// but the result is in [0, 3q).
//
// Panics if q is nil.
func SMulSubLazyTo(vOut, v0, v1, v1S []uint64, q *num.Modulus) {
	checkLength(len(vOut), len(v0), len(v1), len(v1S))

	qv := q.Value()

	M := (len(vOut) >> 3) << 3
	L := unsafe.Sizeof(uint64(0))

	rOut := unsafe.Pointer(unsafe.SliceData(vOut))
	r0 := unsafe.Pointer(unsafe.SliceData(v0))
	r1 := unsafe.Pointer(unsafe.SliceData(v1))
	r1S := unsafe.Pointer(unsafe.SliceData(v1S))

	for i := 0; i < M; i += 8 {
		wOut := (*[8]uint64)(unsafe.Add(rOut, uintptr(i)*L))
		w0 := (*[8]uint64)(unsafe.Add(r0, uintptr(i)*L))
		w1 := (*[8]uint64)(unsafe.Add(r1, uintptr(i)*L))
		w1S := (*[8]uint64)(unsafe.Add(r1S, uintptr(i)*L))

		wOut[0] += modops.SMulLazy(qv-w0[0], w1[0], w1S[0], qv)
		wOut[1] += modops.SMulLazy(qv-w0[1], w1[1], w1S[1], qv)
		wOut[2] += modops.SMulLazy(qv-w0[2], w1[2], w1S[2], qv)
		wOut[3] += modops.SMulLazy(qv-w0[3], w1[3], w1S[3], qv)

		wOut[4] += modops.SMulLazy(qv-w0[4], w1[4], w1S[4], qv)
		wOut[5] += modops.SMulLazy(qv-w0[5], w1[5], w1S[5], qv)
		wOut[6] += modops.SMulLazy(qv-w0[6], w1[6], w1S[6], qv)
		wOut[7] += modops.SMulLazy(qv-w0[7], w1[7], w1S[7], qv)
	}

	for i := M; i < len(vOut); i++ {
		vOut[i] += modops.SMulLazy(qv-v0[i], v1[i], v1S[i], qv)
	}
}
