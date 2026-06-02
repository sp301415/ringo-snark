package jindo_test

import (
	"math/big"
	"testing"

	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/jindo/internal/zp"
)

func TestEncoder(t *testing.T) {
	params := jindo.NewParameters[*zp.Uint](1<<16, 1)
	ecd := jindo.NewEncoder(params.Operator(), params.EncodeParameters())

	v := make([]*zp.Uint, params.Slots())
	vOut := make([]*zp.Uint, params.Slots())
	for i := range v {
		v[i] = v[i].New().MustSetRandom()
		vOut[i] = vOut[i].New().MustSetRandom()
	}

	p := params.Operator().NewPoly()

	ecd.EncodeTo(p, v)
	params.Operator().InvNTTTo(p, p)
	ecd.DecodeTo(vOut, p)

	for i := 0; i < params.Slots(); i++ {
		if !v[i].Equal(vOut[i]) {
			t.FailNow()
		}
	}
}

func TestEncoderBoundary(t *testing.T) {
	params := jindo.NewParameters[*zp.Uint](1<<16, 1)
	ecd := jindo.NewEncoder(params.Operator(), params.EncodeParameters())

	v := make([]*zp.Uint, params.Slots())
	vOut := make([]*zp.Uint, params.Slots())
	for i := range v {
		v[i] = v[i].New().SetBigInt(big.NewInt(-1))
		vOut[i] = vOut[i].New()
	}

	p := params.Operator().NewPoly()

	ecd.EncodeTo(p, v)
	params.Operator().InvNTTTo(p, p)
	ecd.DecodeTo(vOut, p)

	for i := 0; i < params.Slots(); i++ {
		if !v[i].Equal(vOut[i]) {
			t.FailNow()
		}
	}
}

func BenchmarkEncoder(b *testing.B) {
	params := jindo.NewParameters[*zp.Uint](1<<19, 1)
	ecd := jindo.NewEncoder(params.Operator(), params.EncodeParameters())

	v := make([]*zp.Uint, params.Slots())
	for i := range v {
		v[i] = v[i].New().MustSetRandom()
	}

	p := params.Operator().NewPoly()

	b.Run("Encode", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			ecd.EncodeTo(p, v)
			p.IsNTT = false
		}
	})

	b.Run("Decode", func(b *testing.B) {
		for i := 0; i < b.N; i++ {
			p.IsNTT = false
			ecd.DecodeTo(v, p)
		}
	})
}
