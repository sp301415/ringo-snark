package jindo_test

import (
	"fmt"
	"testing"

	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/jindo/internal/zp"
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

	prv := jindo.NewProver[*zp.Uint](params, crs)
	vrf := jindo.NewVerifier[*zp.Uint](params, crs)

	com := make([]*jindo.Commitment, batch)
	open := make([]*jindo.Opening, batch)

	for i := range batch {
		com[i], open[i] = prv.Commit(v[i])
	}

	x := new(zp.Uint).New().MustSetRandom()
	y, pf := prv.Evaluate(x, v, com, open)

	ok := vrf.Verify(x, com, y, pf)
	assert.True(t, ok)
}

func BenchmarkSingle(b *testing.B) {
	crs := []byte("Jindo!")
	for _, logN := range []int{13, 15, 17, 19} {
		N := 1 << logN
		params := jindo.NewParameters[*zp.Uint](N, 1)
		v := [][]*zp.Uint{make([]*zp.Uint, N)}
		for i := range v[0] {
			v[0][i] = new(zp.Uint).New().MustSetRandom()
		}
		x := new(zp.Uint).New().MustSetRandom()

		prv := jindo.NewProver[*zp.Uint](params, crs)
		vrf := jindo.NewVerifier[*zp.Uint](params, crs)

		com := make([]*jindo.Commitment, 1)
		open := make([]*jindo.Opening, 1)

		b.Run(fmt.Sprintf("LogN=%v/Com", logN), func(b *testing.B) {
			for b.Loop() {
				com[0], open[0] = prv.Commit(v[0])
			}
		})

		var pf *jindo.Proof
		var y []*zp.Uint
		b.Run(fmt.Sprintf("LogN=%v/Eval", logN), func(b *testing.B) {
			for b.Loop() {
				y, pf = prv.Evaluate(x, v, com, open)
			}
		})

		var ok bool
		b.Run(fmt.Sprintf("LogN=%v/Verify", logN), func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(x, com, y, pf)
			}
		})

		assert.True(b, ok)
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

		prv := jindo.NewProver[*zp.Uint](params, crs)
		vrf := jindo.NewVerifier[*zp.Uint](params, crs)

		com := make([]*jindo.Commitment, t)
		open := make([]*jindo.Opening, t)

		b.Run(fmt.Sprintf("Batch=%v/Com", t), func(b *testing.B) {
			for b.Loop() {
				for i := range t {
					com[i], open[i] = prv.Commit(v[i])
				}
			}
		})

		var pf *jindo.Proof
		var y []*zp.Uint
		b.Run(fmt.Sprintf("Batch=%v/Eval", t), func(b *testing.B) {
			for b.Loop() {
				y, pf = prv.Evaluate(x, v, com, open)
			}
		})

		var ok bool
		b.Run(fmt.Sprintf("Batch=%v/Verify", t), func(b *testing.B) {
			for b.Loop() {
				ok = vrf.Verify(x, com, y, pf)
			}
		})

		assert.True(b, ok)
	}
}
