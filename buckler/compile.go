package buckler

import (
	"fmt"
	"math/big"
	"reflect"

	"github.com/sp301415/rlwe-piop/celpc"
)

type walker struct {
	publicWitnessCount int64
	witnessCount       int64
}

func (w *walker) walkForCompile(v reflect.Value) {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness{}):
		v.Set(reflect.ValueOf([]*big.Int{big.NewInt(w.publicWitnessCount)}))
		w.publicWitnessCount++
	case reflect.TypeOf(Witness{}):
		v.Set(reflect.ValueOf([]*big.Int{big.NewInt(w.witnessCount)}))
		w.witnessCount++
	}

	switch v.Kind() {
	case reflect.Ptr, reflect.Interface:
		w.walkForCompile(v.Elem())
	case reflect.Invalid:
		panic("invalid type")
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			w.walkForCompile(v.Field(i))
		}
	case reflect.Slice, reflect.Array:
		for i := 0; i < v.Len(); i++ {
			w.walkForCompile(v.Index(i))
		}
	}
}

// Compile compiles the circuit returns the prover, verifier pair.
func Compile(params celpc.Parameters, c Circuit) (*Prover, *Verifier, error) {
	if reflect.TypeOf(c).Kind() != reflect.Ptr {
		return nil, nil, fmt.Errorf("circuit must be defined with a pointer receiver")
	}
	w := &walker{}
	w.walkForCompile(reflect.ValueOf(c))

	ctx := newContext(params, w)
	if err := c.Define(ctx); err != nil {
		return nil, nil, err
	}

	return newProver(params, ctx), newVerifier(params, ctx), nil
}
