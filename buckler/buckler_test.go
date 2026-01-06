package buckler_test

import (
	"math/rand"
	"testing"

	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/buckler/internal/zp110"
	"github.com/sp301415/ringo-snark/buckler/internal/zp220"
	"github.com/sp301415/ringo-snark/buckler/internal/zp440"
	"github.com/sp301415/ringo-snark/buckler/internal/zp880"
	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/stretchr/testify/assert"
)

type PublicKeyCircuit[E bignum.Uint[E]] struct {
	NTT buckler.LinearTransformer[E]

	Sk    buckler.Witness[E]
	SkNTT buckler.Witness[E]

	PkNTT [2]buckler.PublicWitness[E]

	Noise    buckler.Witness[E]
	NoiseNTT buckler.Witness[E]
}

func (c *PublicKeyCircuit[E]) Define(ctx *buckler.Context[E]) {
	var z E

	ctx.AddLinearConstraint(c.SkNTT, c.Sk, c.NTT)
	ctx.AddLinearConstraint(c.NoiseNTT, c.Noise, c.NTT)

	// pk[1] - pk[0] * sk - noise = 0
	var pkCircuit buckler.ArithmeticConstraint[E]
	pkCircuit.AddTerm(z.New().SetInt64(1), c.PkNTT[1])
	pkCircuit.AddTerm(z.New().SetInt64(-1), c.PkNTT[0], c.SkNTT)
	pkCircuit.AddTerm(z.New().SetInt64(-1), nil, c.NoiseNTT)
	ctx.AddArithmeticConstraint(pkCircuit)

	ctx.AddInfNormConstraint(c.Sk, 1)
	ctx.AddInfNormConstraint(c.Noise, 1)
}

func newPkCircuit[E bignum.Uint[E]](rank int) *PublicKeyCircuit[E] {
	polyEval := bigpoly.NewCyclotomicEvaluator[E](rank)

	sk := polyEval.NewPoly(false)
	for i := range rank {
		sk.Coeffs[i].SetInt64(rand.Int63()%3 - 1)
	}
	skNTT := polyEval.NTT(sk)

	noise := polyEval.NewPoly(false)
	for i := range rank {
		noise.Coeffs[i].SetInt64(rand.Int63()%3 - 1)
	}
	noiseNTT := polyEval.NTT(noise)

	pkNTT := [2]*bigpoly.Poly[E]{polyEval.NewPoly(true), polyEval.NewPoly(true)}
	for i := range rank {
		pkNTT[0].Coeffs[i].MustSetRandom()
	}
	polyEval.MulTo(pkNTT[1], pkNTT[0], skNTT)
	polyEval.AddTo(pkNTT[1], pkNTT[1], noiseNTT)

	return &PublicKeyCircuit[E]{
		Sk:    sk.Coeffs,
		SkNTT: skNTT.Coeffs,

		PkNTT: [2]buckler.PublicWitness[E]{
			pkNTT[0].Coeffs,
			pkNTT[1].Coeffs,
		},

		Noise:    noise.Coeffs,
		NoiseNTT: noiseNTT.Coeffs,
	}
}

func BenchmarkPK(b *testing.B) {
	crs := []byte("Buckler!")
	b.Run("LogN=12/LogQ=110", func(b *testing.B) {
		N := 1 << 12
		type E = *zp110.Uint

		var pf *buckler.Proof[E]
		c := PublicKeyCircuit[E]{
			NTT: buckler.NewNTTTransformer[E](N),
		}

		prv, vrf, err := buckler.Compile(N, &c, crs)
		if err != nil {
			b.Fatal(err)
		}

		pk := newPkCircuit[E](N)
		b.Run("Prove", func(b *testing.B) {
			for b.Loop() {
				pf, _ = prv.Prove(pk)
			}
		})

		var ok bool
		b.Run("Verify", func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(pk, pf)
			}
		})
		assert.True(b, ok)
	})

	b.Run("LogN=13/LogQ=220", func(b *testing.B) {
		N := 1 << 13
		type E = *zp220.Uint

		var pf *buckler.Proof[E]
		c := PublicKeyCircuit[E]{
			NTT: buckler.NewNTTTransformer[E](N),
		}

		prv, vrf, err := buckler.Compile(N, &c, crs)
		if err != nil {
			b.Fatal(err)
		}

		pk := newPkCircuit[E](N)
		b.Run("Prove", func(b *testing.B) {
			for b.Loop() {
				pf, _ = prv.Prove(pk)
			}
		})

		var ok bool
		b.Run("Verify", func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(pk, pf)
			}
		})
		assert.True(b, ok)
	})

	b.Run("LogN=14/LogQ=440", func(b *testing.B) {
		N := 1 << 14
		type E = *zp440.Uint

		var pf *buckler.Proof[E]
		c := PublicKeyCircuit[E]{
			NTT: buckler.NewNTTTransformer[E](N),
		}

		prv, vrf, err := buckler.Compile(N, &c, crs)
		if err != nil {
			b.Fatal(err)
		}

		pk := newPkCircuit[E](N)
		b.Run("Prove", func(b *testing.B) {
			for b.Loop() {
				pf, _ = prv.Prove(pk)
			}
		})

		var ok bool
		b.Run("Verify", func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(pk, pf)
			}
		})
		assert.True(b, ok)
	})

	b.Run("LogN=15/LogQ=880", func(b *testing.B) {
		N := 1 << 15
		type E = *zp880.Uint

		var pf *buckler.Proof[E]
		c := PublicKeyCircuit[E]{
			NTT: buckler.NewNTTTransformer[E](N),
		}

		prv, vrf, err := buckler.Compile(N, &c, crs)
		if err != nil {
			b.Fatal(err)
		}

		pk := newPkCircuit[E](N)
		b.Run("Prove", func(b *testing.B) {
			for b.Loop() {
				pf, _ = prv.Prove(pk)
			}
		})

		var ok bool
		b.Run("Verify", func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(pk, pf)
			}
		})
		assert.True(b, ok)
	})
}
