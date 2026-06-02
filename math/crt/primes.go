package crt

import (
	"errors"
	"math"
	"slices"

	"github.com/sp301415/ringo-snark/math/num"
)

// FindNearestNTTPrimes finds a list of prime moduli that are NTT-friendly with respect to the given ring parameters.
// Specifically, it outputs the first cnt NTT-friendly primes nearest to 2^bits.
// Output moduli are alternating in size.
// It panics if an error occurs.
func MustFindNearestNTTPrimes(rank int, bits float64, cnt int) []*num.Modulus {
	primes, err := FindNearestNTTPrimes(rank, bits, cnt)
	if err != nil {
		panic(err)
	}
	return primes
}

// FindNearestNTTPrimes finds a list of prime moduli that are NTT-friendly with respect to the given ring parameters.
// Specifically, it outputs the first cnt NTT-friendly primes nearest to 2^bits.
// Output moduli are alternating in size.
func FindNearestNTTPrimes(rank int, bits float64, cnt int) ([]*num.Modulus, error) {
	gap := uint64(rank) << 1

	start := (uint64(math.Floor(math.Exp2(bits))/float64(gap)))*gap + 1
	nextCnt := cnt >> 1
	prevCnt := cnt - nextCnt

	nextStart := start
	nextPrimes := make([]*num.Modulus, 0, nextCnt)
	for i := 0; i < nextCnt; i++ {
		prime, err := num.NextPrime(nextStart, gap)
		if err != nil {
			break
		}
		nextPrimes = append(nextPrimes, num.NewModulus(prime))
		nextStart = prime
	}

	prevStart := start
	prevPrimes := make([]*num.Modulus, 0, prevCnt)
	for i := 0; i < prevCnt; i++ {
		prime, err := num.PrevPrime(prevStart, gap)
		if err != nil {
			break
		}
		prevPrimes = append(prevPrimes, num.NewModulus(prime))
		prevStart = prime
	}

	if len(nextPrimes) < nextCnt && len(prevPrimes) < prevCnt {
		return nil, errors.New("not enough primes found")
	} else if len(nextPrimes) < nextCnt {
		prevStart := prevPrimes[prevCnt-1].Value()
		for i := 0; i < cnt-(len(nextPrimes)+len(prevPrimes)); i++ {
			prime, err := num.PrevPrime(prevStart, gap)
			if err != nil {
				return nil, err
			}
			prevPrimes = append(prevPrimes, num.NewModulus(prime))
			prevStart = prime
		}
	} else if len(prevPrimes) < prevCnt {
		nextStart := nextPrimes[nextCnt-1].Value()
		for i := 0; i < cnt-(len(nextPrimes)+len(prevPrimes)); i++ {
			prime, err := num.NextPrime(nextStart, gap)
			if err != nil {
				return nil, err
			}
			nextPrimes = append(nextPrimes, num.NewModulus(prime))
			nextStart = prime
		}
	}

	primes := append(append(make([]*num.Modulus, 0, cnt), prevPrimes...), nextPrimes...)
	slices.SortFunc(primes, num.CmpModulus)

	return primes, nil
}
