package crt

import "math/bits"

const (
	nttUnrollBound = 32
)

// fwdNTTInPlacePow2 computes the NTT transform in-place for power-of-two length coefficients.
func fwdNTTInPlacePow2(coeffs, tw, twS []uint64, q uint64) {
	if len(coeffs) < nttUnrollBound {
		fwdNTTInPlacePow2Ref(coeffs, tw, twS, q)
		return
	}
	fwdNTTInPlacePow2Unroll(coeffs, tw, twS, q)
}

// fwdButterflyPow2 returns the Harvey butterfly.
func fwdButterflyPow2(u, v, w, wS, q, twoQ uint64) (uint64, uint64) {
	quo, _ := bits.Mul64(v, wS)
	t := v*w - quo*q
	if u >= twoQ {
		u -= twoQ
	}
	return u + t, u - t + twoQ
}

// fwdButterflyPow2Reduce returns the Harvey butterfly with reduction.
func fwdButterflyPow2Reduce(u, v, w, wS, q, twoQ uint64) (uint64, uint64) {
	quo, _ := bits.Mul64(v, wS)
	t := v*w - quo*q
	if u >= twoQ {
		u -= twoQ
	}

	u, v = u+t, u-t+twoQ

	if u >= twoQ {
		u -= twoQ
	}
	if u >= q {
		u -= q
	}

	if v >= twoQ {
		v -= twoQ
	}
	if v >= q {
		v -= q
	}

	return u, v
}

// fwdNTTInPlacePow2Ref computes the NTT transform in-place for power-of-two length coefficients.
func fwdNTTInPlacePow2Ref(coeffs, tw, twS []uint64, q uint64) {
	N := len(coeffs)
	twoQ := q << 1

	t := N
	for m := 1; m <= N/2; m <<= 1 {
		t >>= 1
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t
			w, wS := tw[m+i], twS[m+i]
			for j := j1; j < j2; j++ {
				coeffs[j], coeffs[j+t] = fwdButterflyPow2(coeffs[j], coeffs[j+t], w, wS, q, twoQ)
			}
		}
	}
}

// invNTTInPlacePow2 computes the inverse NTT transform in-place for power-of-two length coefficients.
func invNTTInPlacePow2(coeffs, twInv, twInvS []uint64, q uint64) {
	if len(coeffs) < nttUnrollBound {
		invNTTInPlacePow2Ref(coeffs, twInv, twInvS, q)
		return
	}
	invNTTInPlacePow2Unroll(coeffs, twInv, twInvS, q)
}

// invButterflyPow2 returns the inverse Harvey butterfly.
func invButterflyPow2(u, v, w, wS, q, twoQ uint64) (uint64, uint64) {
	u, v = u+v, u-v+twoQ
	if u >= twoQ {
		u -= twoQ
	}
	quo, _ := bits.Mul64(v, wS)
	return u, v*w - quo*q
}

// invNTTInPlacePow2Ref computes the inverse NTT transform in-place for power-of-two length coefficients.
func invNTTInPlacePow2Ref(coeffs, twInv, twInvS []uint64, q uint64) {
	N := len(coeffs)
	twoQ := q << 1

	t := 1
	for m := N / 2; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := i * t << 1
			j2 := j1 + t
			w, wS := twInv[m+i], twInvS[m+i]
			for j := j1; j < j2; j++ {
				coeffs[j], coeffs[j+t] = invButterflyPow2(coeffs[j], coeffs[j+t], w, wS, q, twoQ)
			}
		}
		t <<= 1
	}
}
