package buckler

import (
	"fmt"
	"math/bits"
	"reflect"

	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
)

var (
	errReadOnly     = fmt.Errorf("cannot set value")
	errRankMismatch = fmt.Errorf("witness rank mismatch")
)

func idToWitness[E bignum.Uint[E], W Witness[E] | PublicWitness[E]](id uint64) W {
	var z E
	var w W

	switch any(w).(type) {
	case Witness[E]:
		sw := Witness[E]{z.New().SetUint64((id + 1) << 1)}
		return any(sw).(W)
	case PublicWitness[E]:
		pw := PublicWitness[E]{z.New().SetUint64(((id + 1) << 1) + 1)}
		return any(pw).(W)
	}

	return nil
}

func witnessToID[E bignum.Uint[E], W Witness[E] | PublicWitness[E]](w W) uint64 {
	var z E

	digits := make([]uint64, z.Limb())
	w[0].Slice(digits)
	return (digits[0] >> 1) - 1
}

type walker[E bignum.Uint[E]] struct {
	pwCnt       uint64
	wCnt        uint64
	circuitType reflect.Type
}

// firstWalk is called in the compile phase.
func (w *walker[E]) firstWalk(v reflect.Value) error {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness[E]{}):
		if !v.CanSet() {
			return errReadOnly
		}
		v.Set(reflect.ValueOf(idToWitness[E, PublicWitness[E]](w.pwCnt)))
		w.pwCnt++
		return nil

	case reflect.TypeOf(Witness[E]{}):
		if !v.CanSet() {
			return errReadOnly
		}
		v.Set(reflect.ValueOf(idToWitness[E, Witness[E]](w.wCnt)))
		w.wCnt++
		return nil
	}

	switch v.Kind() {
	case reflect.Pointer, reflect.Interface:
		if !v.IsNil() {
			w.firstWalk(v.Elem())
		}
	case reflect.Struct:
		for i := range v.NumField() {
			w.firstWalk(v.Field(i))
		}
	case reflect.Slice, reflect.Array:
		for i := range v.Len() {
			w.firstWalk(v.Index(i))
		}
	case reflect.Invalid:
		return fmt.Errorf("walk: invalid kind")
	}

	return nil
}

// prvWalk is called in the prove phase.
func (w *walker[E]) prvWalk(prv *Prover[E], v reflect.Value, pw []PublicWitness[E], sw []Witness[E]) error {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness[E]{}):
		pw[w.pwCnt] = v.Interface().(PublicWitness[E])
		if len(pw[w.pwCnt]) != prv.ctx.rank {
			return errRankMismatch
		}
		w.pwCnt++
		return nil

	case reflect.TypeOf(Witness[E]{}):
		sw[w.wCnt] = v.Interface().(Witness[E])
		if len(sw[w.wCnt]) != prv.ctx.rank {
			return errRankMismatch
		}
		w.wCnt++
		return nil
	}

	switch v.Kind() {
	case reflect.Pointer, reflect.Interface:
		if !v.IsNil() {
			w.prvWalk(prv, v.Elem(), pw, sw)
		}
	case reflect.Struct:
		for i := range v.NumField() {
			w.prvWalk(prv, v.Field(i), pw, sw)
		}
	case reflect.Slice, reflect.Array:
		for i := range v.Len() {
			w.prvWalk(prv, v.Index(i), pw, sw)
		}
	case reflect.Invalid:
		return fmt.Errorf("walk: invalid kind")
	}

	return nil
}

// vrfWalk is called in the prove phase.
func (w *walker[E]) vrfWalk(vrf *Verifier[E], v reflect.Value, pw []PublicWitness[E]) error {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness[E]{}):
		pw[w.pwCnt] = v.Interface().(PublicWitness[E])
		if len(pw[w.pwCnt]) != vrf.ctx.rank {
			return errRankMismatch
		}
		w.pwCnt++
		return nil
	}

	switch v.Kind() {
	case reflect.Pointer, reflect.Interface:
		if !v.IsNil() {
			w.vrfWalk(vrf, v.Elem(), pw)
		}
	case reflect.Struct:
		for i := range v.NumField() {
			w.vrfWalk(vrf, v.Field(i), pw)
		}
	case reflect.Slice, reflect.Array:
		for i := range v.Len() {
			w.vrfWalk(vrf, v.Index(i), pw)
		}
	case reflect.Invalid:
		return fmt.Errorf("walk: invalid kind")
	}

	return nil
}

// Compile compiles the circuit and returns the prover, verifier pair.
//
// For correct compilation, the [PublicWitness] and [Witness] field must be empty.
// Moreover, all other fields must be set correctly.
func Compile[E bignum.Uint[E]](witnessRank int, c Circuit[E], crs []byte) (*Prover[E], *Verifier[E], error) {
	if reflect.TypeOf(c).Kind() != reflect.Pointer {
		return nil, nil, fmt.Errorf("circuit must be defined with a pointer receiver")
	}

	w := &walker[E]{circuitType: reflect.TypeOf(c).Elem()}
	if err := w.firstWalk(reflect.ValueOf(c)); err != nil {
		return nil, nil, err
	}

	ctx := newContext(witnessRank, w)
	ctx.pwCnt = w.pwCnt
	ctx.wCnt = w.wCnt

	c.Define(ctx)

	jindoParams := jindo.NewParameters[E](ctx.commitRank(), ctx.batch())

	embRank := 1 << bits.Len(uint(max(ctx.arithCheckMaxRank, ctx.sumCheckMaxRank)-1))

	prv := &Prover[E]{
		JindoParams: jindoParams,

		polyEval: bigpoly.NewCyclicEvaluator[E](embRank),

		ecd: newEncoder[E](witnessRank, embRank),

		polyProver: jindo.NewProver[E](jindoParams, crs),

		ctx: ctx,
	}

	vrf := &Verifier[E]{
		JindoParams: jindoParams,

		polyEval: bigpoly.NewCyclicEvaluator[E](embRank),

		ecd: newEncoder[E](witnessRank, embRank),

		polyVerifier: jindo.NewVerifier[E](jindoParams, crs),

		ctx: ctx,
	}

	return prv, vrf, nil
}
