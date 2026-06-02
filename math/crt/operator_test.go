package crt_test

import (
	"fmt"
	"testing"

	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
	"github.com/stretchr/testify/assert"
)

var (
	rSrc      = csprng.NewUniformSamplerWithSeed(nil)
	benchLogN = []int{12, 13, 14, 15, 16, 17}
)

func randPoly(rank int, q []*num.Modulus) *crt.Element {
	p := crt.NewPoly(rank, len(q))
	for i := 0; i < rank; i++ {
		for j := range q {
			p.Coeffs[j][i] = rSrc.SampleN(q[j].Value())
		}
	}

	return p
}

func mulReduce(p0, p1, pMod [][]uint64, q []*num.Modulus) [][]uint64 {
	pOut := make([][]uint64, len(q))
	for i := range q {
		pOut[i] = reduce(mul(p0[i], p1[i], q[i]), pMod[i], q[i])
	}
	return pOut
}

func mul(p0, p1 []uint64, q *num.Modulus) []uint64 {
	pOut := make([]uint64, len(p0)+len(p1)-1)
	for i := range p0 {
		for j := range p1 {
			pOut[i+j] = num.Add(pOut[i+j], num.Mul(p0[i], p1[j], q), q)
		}
	}

	return pOut
}

func reduce(p0, p1 []uint64, q *num.Modulus) []uint64 {
	quo := make([]uint64, len(p0)-len(p1)+1)
	rem := make([]uint64, len(p0))
	copy(rem, p0)

	lcInv := num.Inv(p1[len(p1)-1], q)
	for i := 0; i <= len(p0)-len(p1); i++ {
		if rem[len(rem)-i-1] != 0 {
			quo[len(quo)-i-1] = num.Mul(rem[len(rem)-i-1], lcInv, q)
			vec.MulSubScalarTo(rem[len(rem)-i-len(p1):len(rem)-i], p1, quo[len(quo)-i-1], q)
		}
	}

	return rem[:len(p1)-1]
}

func TestOperator(t *testing.T) {
	N := 1 << 10
	q := crt.MustFindNearestNTTPrimes(N, 40, 3)
	op := crt.NewOperator(N, q)

	p0 := randPoly(N, q)
	p1 := randPoly(N, q)

	cycloPoly := make([]int64, N+1)
	cycloPoly[N] = 1
	cycloPoly[0] = 1

	pMod := make([][]uint64, len(q))
	for i := range q {
		pMod[i] = vec.Reduce(cycloPoly, q[i])
	}

	p0NTT := op.FwdNTT(p0)
	p1NTT := op.FwdNTT(p1)
	p1NTTS := crt.GenShoupElement(p1NTT, op.Modulus())

	t.Run("Mul", func(t *testing.T) {
		pOutNTT := op.Mul(p0NTT, p1NTT)
		pOut := op.InvNTT(pOutNTT)

		assert.Equal(t, mulReduce(p0.Coeffs, p1.Coeffs, pMod, q), pOut.Coeffs)
	})

	t.Run("MulAdd", func(t *testing.T) {
		pOutNTT := randPoly(N, q)
		pOutNTT.IsNTT = true
		pOutNTTRef := pOutNTT.Copy()

		op.MulAddTo(pOutNTT, p0NTT, p1NTT)
		op.AddTo(pOutNTTRef, pOutNTTRef, op.Mul(p0NTT, p1NTT))

		assert.Equal(t, pOutNTTRef.Coeffs, pOutNTT.Coeffs)
	})

	t.Run("MulSub", func(t *testing.T) {
		pOutNTT := randPoly(N, q)
		pOutNTT.IsNTT = true
		pOutNTTRef := pOutNTT.Copy()

		op.MulSubTo(pOutNTT, p0NTT, p1NTT)
		op.SubTo(pOutNTTRef, pOutNTTRef, op.Mul(p0NTT, p1NTT))

		assert.Equal(t, pOutNTTRef.Coeffs, pOutNTT.Coeffs)
	})

	t.Run("SMul", func(t *testing.T) {
		pOutNTT := op.SMul(p0NTT, p1NTT, p1NTTS)
		pOut := op.InvNTT(pOutNTT)

		assert.Equal(t, mulReduce(p0.Coeffs, p1.Coeffs, pMod, q), pOut.Coeffs)
	})

	t.Run("SMulAdd", func(t *testing.T) {
		pOutNTT := randPoly(N, q)
		pOutNTT.IsNTT = true
		pOutNTTRef := pOutNTT.Copy()

		op.SMulAddTo(pOutNTT, p0NTT, p1NTT, p1NTTS)
		op.AddTo(pOutNTTRef, pOutNTTRef, op.Mul(p0NTT, p1NTT))

		assert.Equal(t, pOutNTTRef.Coeffs, pOutNTT.Coeffs)
	})

	t.Run("SMulSub", func(t *testing.T) {
		pOutNTT := randPoly(N, q)
		pOutNTT.IsNTT = true
		pOutNTTRef := pOutNTT.Copy()

		op.SMulSubTo(pOutNTT, p0NTT, p1NTT, p1NTTS)
		op.SubTo(pOutNTTRef, pOutNTTRef, op.Mul(p0NTT, p1NTT))

		assert.Equal(t, pOutNTTRef.Coeffs, pOutNTT.Coeffs)
	})

	t.Run("Aut", func(t *testing.T) {
		cycloOrd := uint64(N) << 1
		var idx uint64
		for {
			idx = rSrc.SampleN(cycloOrd)
			if op.CanAut(int(idx)) {
				break
			}
		}
		idxInv := num.Inv(idx, num.NewModulus(cycloOrd))

		pOut := op.Aut(p0, int(idx))
		op.FwdNTTTo(pOut, pOut)
		op.AutTo(pOut, pOut, int(idxInv))
		op.InvNTTTo(pOut, pOut)

		assert.Equal(t, p0.Coeffs, pOut.Coeffs)
	})
}

func benchmarkOperator(b *testing.B, N int) {
	q := crt.MustFindNearestNTTPrimes(N, 40, 1)
	op := crt.NewOperator(N, q)

	p0 := randPoly(N, q)
	p1 := randPoly(N, q)
	pOut := randPoly(N, q)

	p0NTT := op.FwdNTT(p0)
	p1NTT := op.FwdNTT(p1)
	p1NTTS := crt.GenShoupElement(p1NTT, op.Modulus())
	pOutNTT := op.FwdNTT(pOut)

	b.Run("Add", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.AddTo(pOut, p0, p1)
		}
	})

	b.Run("Sub", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.SubTo(pOut, p0, p1)
		}
	})

	b.Run("Neg", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.NegTo(pOut, p0)
		}
	})

	b.Run("FwdNTT", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.FwdNTTTo(p0NTT, p0)
		}
	})

	b.Run("InvNTT", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.InvNTTTo(p0, p0NTT)
		}
	})

	b.Run("Mul", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.MulTo(pOutNTT, p0NTT, p1NTT)
		}
	})

	b.Run("MulAdd", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.MulAddTo(pOutNTT, p0NTT, p1NTT)
		}
	})

	b.Run("MulSub", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.MulSubTo(pOutNTT, p0NTT, p1NTT)
		}
	})

	b.Run("SMul", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.SMulTo(pOutNTT, p0NTT, p1NTT, p1NTTS)
		}
	})

	b.Run("SMulAdd", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.SMulAddTo(pOutNTT, p0NTT, p1NTT, p1NTTS)
		}
	})

	b.Run("SMulSub", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.SMulSubTo(pOutNTT, p0NTT, p1NTT, p1NTTS)
		}
	})

	var idx uint64
	for {
		idx = rSrc.SampleN(uint64(N << 1))
		if op.CanAut(int(idx)) {
			break
		}
	}

	b.Run("Aut", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.AutTo(pOut, p0, int(idx))
		}
	})

	b.Run("AutNTT", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			op.AutTo(pOutNTT, p0NTT, int(idx))
		}
	})
}

func BenchmarkCyclotomicOperator(b *testing.B) {
	for _, logN := range benchLogN {
		N := 1 << logN
		b.Run(fmt.Sprintf("LogN=%v", logN), func(b *testing.B) {
			benchmarkOperator(b, N)
		})
	}
}
