package buckler

import (
	"fmt"
	"reflect"

	"github.com/sp301415/ringo-snark/math/num"
)

type walker[E num.Uint[E]] struct {
	pwCnt       uint64
	wCnt        uint64
	circuitType reflect.Type
}

// firstWalk is called in the compile phase.
func (w *walker[E]) firstWalk(v reflect.Value) error {
	var z E
	switch v.Type() {
	case reflect.TypeOf(PublicWitness[E]{}):
		if !v.CanSet() {
			return fmt.Errorf("walk: cannot set value")
		}
		v.Set(reflect.ValueOf([]E{z.New().SetUint64((uint64(w.pwCnt+1)<<1 + 1))}))
		w.pwCnt++
		return nil

	case reflect.TypeOf(Witness[E]{}):
		if !v.CanSet() {
			return fmt.Errorf("walk: cannot set value")
		}
		v.Set(reflect.ValueOf([]E{z.New().SetUint64((uint64(w.wCnt+1) << 1))}))
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

// Compile compiles the circuit and returns the prover, verifier pair.
//
// For correct compilation, the [PublicWitness] and [Witness] field must be empty.
// Moreover, all other fields must be set correctly.
func Compile[E num.Uint[E]](witnessRank int, c Circuit[E]) error {
	if reflect.TypeOf(c).Kind() != reflect.Pointer {
		return fmt.Errorf("circuit must be defined with a pointer receiver")
	}

	w := &walker[E]{circuitType: reflect.TypeOf(c).Elem()}
	if err := w.firstWalk(reflect.ValueOf(c)); err != nil {
		return err
	}

	ctx := newContext(witnessRank, w)
	ctx.pwCnt = w.pwCnt
	ctx.wCnt = w.wCnt

	c.Define(ctx)

	fmt.Println(ctx)

	fmt.Println(witnessRank, ctx.maxRank)

	return nil
}
