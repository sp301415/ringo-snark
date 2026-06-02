package jindo_test

import (
	"fmt"
	"math"
	"testing"

	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/jindo/internal/zp"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/stretchr/testify/assert"
)

var (
	crs = []byte("Jindo!")
)

func TestJindo(t *testing.T) {
	t.Run("Single", func(t *testing.T) {
		testJindo(t, 1)
	})

	t.Run("Batch", func(t *testing.T) {
		testJindo(t, 8)
	})
}

func testJindo(t *testing.T, batch int) {
	N := 1 << 10
	params := jindo.NewParameters[*zp.Uint](N, batch)
	v := make([][]*zp.Uint, batch)
	for i := range batch {
		v[i] = make([]*zp.Uint, N)
		for j := range N {
			v[i][j] = new(zp.Uint).New().MustSetRandom()
		}
	}

	prv := jindo.NewProver(params, crs)
	vrf := jindo.NewVerifier(params, crs)

	com := make([]*jindo.Commitment, batch)
	open := make([]*jindo.Opening[*zp.Uint], batch)

	for i := range batch {
		com[i], open[i] = prv.Commit(v[i])
	}

	x := new(zp.Uint).New().MustSetRandom()

	y := make([]*zp.Uint, batch)
	for i := range batch {
		y[i] = (&bigpoly.Poly[*zp.Uint]{Coeffs: v[i]}).Evaluate(x)
	}

	pf := prv.Evaluate(x, y, com, open)

	ok := vrf.Verify(x, y, com, pf)
	assert.True(t, ok)
}

func BenchmarkSingle(b *testing.B) {
	crs := []byte("Jindo!")
	for _, logN := range []int{14, 16, 18, 20} {
		N := 1 << logN
		params := jindo.NewParameters[*zp.Uint](N, 1)
		fmt.Printf("%+v\n", params)
		fmt.Println("Size:", params.Size()/math.Exp2(23))

		v := [][]*zp.Uint{make([]*zp.Uint, N)}
		for i := range v[0] {
			v[0][i] = new(zp.Uint).New().MustSetRandom()
		}
		x := new(zp.Uint).New().MustSetRandom()
		y := []*zp.Uint{(&bigpoly.Poly[*zp.Uint]{Coeffs: v[0]}).Evaluate(x)}

		prv := jindo.NewProver(params, crs)
		vrf := jindo.NewVerifier(params, crs)

		com := make([]*jindo.Commitment, params.Batch())
		open := make([]*jindo.Opening[*zp.Uint], params.Batch())
		for i := range params.Batch() {
			com[i] = jindo.NewCommitment(params)
			open[i] = jindo.NewOpening(params)
		}

		prv.CommitTo(com[0], open[0], v[0])

		b.Run(fmt.Sprintf("LogN=%v/Com", logN), func(b *testing.B) {
			for b.Loop() {
				prv.CommitTo(com[0], open[0], v[0])
			}
		})

		pf := jindo.NewProof(params)
		prv.EvaluateTo(pf, x, y, com, open)

		b.Run(fmt.Sprintf("LogN=%v/Eval", logN), func(b *testing.B) {
			for b.Loop() {
				prv.EvaluateTo(pf, x, y, com, open)
			}
		})

		var ok bool
		b.Run(fmt.Sprintf("LogN=%v/Verify", logN), func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(x, y, com, pf)
			}
			assert.True(b, ok)
		})
	}
}

func BenchmarkBatch(b *testing.B) {
	N := 1 << 19
	crs := []byte("Jindo!")
	for _, t := range []int{8, 16, 32} {
		params := jindo.NewParameters[*zp.Uint](N, t)
		v := make([][]*zp.Uint, t)
		for i := range t {
			v[i] = make([]*zp.Uint, N)
			for j := range N {
				v[i][j] = new(zp.Uint).New().MustSetRandom()
			}
		}

		x := new(zp.Uint).New().MustSetRandom()

		y := make([]*zp.Uint, t)
		for i := range t {
			y[i] = (&bigpoly.Poly[*zp.Uint]{Coeffs: v[i]}).Evaluate(x)
		}

		prv := jindo.NewProver(params, crs)
		vrf := jindo.NewVerifier(params, crs)

		com := make([]*jindo.Commitment, t)
		open := make([]*jindo.Opening[*zp.Uint], t)

		b.Run(fmt.Sprintf("Batch=%v/Com", t), func(b *testing.B) {
			for b.Loop() {
				for i := range t {
					com[i], open[i] = prv.Commit(v[i])
				}
			}
		})

		var pf *jindo.Proof[*zp.Uint]
		b.Run(fmt.Sprintf("Batch=%v/Eval", t), func(b *testing.B) {
			for b.Loop() {
				pf = prv.Evaluate(x, y, com, open)
			}
		})

		var ok bool
		b.Run(fmt.Sprintf("Batch=%v/Verify", t), func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(x, y, com, pf)
			}
		})

		assert.True(b, ok)
	}
}
