package num

import (
	"errors"
	"math/bits"
	"math/rand"
	"slices"
)

var (
	smallPrimes = []uint64{
		2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
	}
)

// IsPrime checks of x is prime.
// Any x <= 1 are not considered prime.
func IsPrime[T Integer](x T) bool {
	return (x > 1) && isPrimeUint64(uint64(Abs((x))))
}

// isPrime checks of x is prime.
// 0 and 1 are not considered prime.
func isPrimeUint64(x uint64) bool {
	xq := NewModulus(x)

	for _, p := range smallPrimes {
		if x == p {
			return true
		} else if x%p == 0 {
			return false
		}
	}

	s := bits.TrailingZeros64(x - 1)
	d := (x - 1) >> s

	tests := []uint64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}
	for _, a := range tests {
		n := Exp(a, d, xq)
		var y uint64
		for i := 0; i < s; i++ {
			y = Mul(n, n, xq)
			if y == 1 && n != 1 && n != x-1 {
				return false
			}
			n = y
		}
		if y != 1 {
			return false
		}
	}

	return true
}

// MustPrevPrime returns the previous prime number of x with skip.
// It panics if an error occurs.
func MustPrevPrime[T Integer](x T, skip T) T {
	prime, err := PrevPrime(x, skip)
	if err != nil {
		panic(err)
	}
	return prime
}

// PrevPrime returns the previous prime number of x with skip.
// If skip <= 0, or there is no prime number meets the condition, it returns an error.
func PrevPrime[T Integer](x T, skip T) (T, error) {
	if skip <= 0 {
		return 0, errors.New("PrevPrime: skip must be positive")
	}

	for t := x - skip; ; t -= skip {
		if uint64(t) > MaxModulus || t <= 1 {
			return 0, errors.New("PrevPrime: underflow")
		}

		if IsPrime(t) {
			return t, nil
		}
	}
}

// MustNextPrime returns the next prime number of x with skip.
// It panics if an error occurs.
func MustNextPrime[T Integer](x T, skip T) T {
	prime, err := NextPrime(x, skip)
	if err != nil {
		panic(err)
	}
	return prime
}

// NextPrime returns the next prime number of x with skip.
// If skip <= 0, or there is no prime number meets the condition, it returns an error.
func NextPrime[T Integer](x T, skip T) (T, error) {
	if skip <= 0 {
		panic("skip must be positive")
	}

	for t := x + skip; ; t += skip {
		if uint64(t) > MaxModulus {
			return 0, errors.New("overflow")
		}

		if IsPrime(t) {
			return t, nil
		}
	}
}

// IsProdPowerOf checks if x can be expressed as a product of the powers of given factors.
func IsProdPowerOf[T Integer](x T, factors []T) bool {
	for _, f := range factors {
		if f == 0 {
			continue
		}
		for x%f == 0 {
			x /= f
		}
	}
	return x == 1
}

// NextProdPower returns the next number of x that can be expressed as
// a product of the powers of given factors.
func NextProdPower[T Integer](x T, factors []T) T {
	xNext := x + 1
	for !IsProdPowerOf(xNext, factors) {
		xNext++
	}
	return xNext
}

// Factor factors x. The resulting primes are sorted in ascending order.
//
// Panics when x < 0.
func Factor[T Integer](x T) (primes []T, exps []T) {
	if x < 0 {
		panic("x must be non-negative")
	}

	factors := make(map[uint64]uint64)
	factorRecurse(uint64(x), factors)

	primes = make([]T, 0, len(factors))
	for p := range factors {
		primes = append(primes, T(p))
	}
	slices.Sort(primes)

	exps = make([]T, len(primes))
	for i, p := range primes {
		exps[i] = T(factors[uint64(p)])
	}

	return primes, exps
}

// factorRecurse finds a non-trivial factor of x and adds it to factors.
// It uses Brent-Pollard's rho algorithm without trivial checks.
func factorRecurse(x uint64, factors map[uint64]uint64) {
	for _, p := range smallPrimes {
		for {
			if x%p != 0 {
				break
			}
			factors[p] += 1
			x /= p
		}
	}

	switch {
	case x == 0:
		return
	case x == 1:
		if len(factors) == 0 {
			factors[1] = 1
		}
		return
	case IsPrime(x):
		factors[x] += 1
		return
	}

	n := NewModulus(x)
	y, c, m := randUint64n(x), 1+randUint64n(x-3), randUint64n(x)
	g, r, q := uint64(1), uint64(1), uint64(1)

	var t, ys uint64

	for g == 1 {
		t = y
		for i := uint64(0); i < r; i++ {
			y = Add(Mul(y, y, n), c, n)
		}
		var k uint64
		for k < r && g == 1 {
			ys = y
			for i := uint64(0); i < min(m, r-k); i++ {
				y = Add(Mul(y, y, n), c, n)
				q = Mul(q, subAbs(y, t), n)
			}
			g = GCD(q, x)
			k += m
		}
		r <<= 1
	}

	if g == x {
		for {
			ys = Add(Mul(ys, ys, n), c, n)
			g = GCD(subAbs(ys, t), x)

			if g > 1 {
				break
			}
		}
	}

	factorRecurse(g, factors)
	factorRecurse(x/g, factors)
}

// subAbs returns |x - y|.
func subAbs(x, y uint64) uint64 {
	if x > y {
		return x - y
	}
	return y - x
}

// randUint64n returns random uint64 in [0, n).
func randUint64n(n uint64) uint64 {
	return uint64(rand.Int63n(int64(n)))
}

// Order returns the multiplicative order of x modulo q.
func Order(x uint64, q *Modulus) uint64 {
	ord := uint64(1)
	acc := Reduce(x, q)
	for acc != 1 {
		acc = Mul(acc, x, q)
		ord += 1
	}
	return ord
}

// Totient returns the Euler-Phi function of x.
//
// Panics when x < 0.
func Totient[T Integer](x T) T {
	primes, exps := Factor(x)
	return TotientWithFactors(x, primes, exps)
}

// TotientWithFactors returns the Euler-Phi function of x, given its factorization.
//
// Panics when x < 0.
func TotientWithFactors[T Integer](x T, primes, exps []T) T {
	if x < 0 {
		panic("x must be non-negative")
	} else if x == 0 || x == 1 {
		return x
	}

	phi := x
	for _, p := range primes {
		phi -= phi / p
	}
	return phi
}

// Generators returns the generators of the subgroup of multiplicative group modulo q.
func Generators(q *Modulus) []uint64 {
	primes, exps := Factor(q.Value())
	return GeneratorsWithFactors(q, primes, exps)
}

// GeneratorsWithFactors returns the generators of the subgroup of multiplicative group modulo q,
// given its factorization.
func GeneratorsWithFactors(q *Modulus, primes, exps []uint64) []uint64 {
	primePows := make([]uint64, len(primes))
	for i := range primePows {
		primePows[i] = Exp(primes[i], exps[i], nil)
	}

	subGens := make([]uint64, len(primes))
	crt := make([]uint64, len(primes))
	for i := range subGens {
		primePowMod := NewModulus(primePows[i])
		subGens[i] = primitiveRoot(primes[i], primePows[i])
		crt[i] = Mul(q.Value()/primePows[i], Inv(q.Value()/primePows[i], primePowMod), q)
	}

	gens := make([]uint64, len(subGens))
	for i := range gens {
		for j := range crt {
			if j == i {
				gens[i] = Add(gens[i], Mul(subGens[j], crt[j], q), q)
			} else {
				gens[i] = Add(gens[i], crt[j], q)
			}
		}
	}

	if primePows[0]%8 == 0 {
		gens = append([]uint64{0}, gens...)
		gens[0] = Mul(5, crt[0], q)
		for i := 1; i < len(crt); i++ {
			gens[0] = Add(gens[0], crt[i], q)
		}
	} else if gens[0] == 1 {
		gens = gens[1:]
	}

	return gens
}

// primitiveRoot returns a generator modulo p^e.
// Returns p^e - 1 if p is 2.
func primitiveRoot(p, pExp uint64) uint64 {
	if p == 2 {
		return pExp - 1
	}

	phi := pExp - pExp/p
	primes, _ := Factor(phi)
	testPows := make([]uint64, 0, len(primes))
	for _, p := range primes {
		testPows = append(testPows, phi/p)
	}

	pExpMod := NewModulus(pExp)
	g := uint64(2)
	for {
		ok := true
		for _, t := range testPows {
			if Exp(g, t, pExpMod) == 1 {
				ok = false
				break
			}
		}
		if ok && Exp(g, phi, pExpMod) == 1 {
			return g
		}
		g++
	}
}

// NthRoot returns the N-th root of unity modulo q, given the generators.
func NthRoot(n int, g []uint64, q *Modulus) uint64 {
	primes, exps := Factor(q.Value())
	return NthRootWithFactors(n, g, q, primes, exps)
}

// NthRootWithFactors returns the N-th root of unity modulo q, given the generators and the factorization of q.
func NthRootWithFactors(n int, g []uint64, q *Modulus, primes, exps []uint64) uint64 {
	primePows := make([]uint64, len(primes))
	for i := range primePows {
		primePows[i] = Exp(primes[i], exps[i], nil)
		if (primePows[i]-primePows[i]/primes[i])%uint64(n) != 0 {
			panic("there is no N-th root of unity")
		}
	}

	if primes[0] == 2 {
		switch n {
		case 1:
			return 1
		case 2:
			return q.Value() - 1
		}
	}

	r := uint64(0)
	for i := range primes {
		primePowMod := NewModulus(primePows[i])
		h := Exp(g[i], (primePows[i]-primePows[i]/primes[i])/uint64(n), primePowMod)
		t := Mul(q.Value()/primePows[i], Inv(q.Value()/primePows[i], primePowMod), q)
		r = Add(r, Mul(h, t, q), q)
	}
	return r
}
