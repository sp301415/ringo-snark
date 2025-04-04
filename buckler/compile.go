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
		return
	case reflect.TypeOf(Witness{}):
		v.Set(reflect.ValueOf([]*big.Int{big.NewInt(w.witnessCount)}))
		w.witnessCount++
		return
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
	c.Define(ctx)

	prover := newProver(params, ctx)
	verifier := &Verifier{
		Parameters: params,

		ringQ:     prover.ringQ,
		baseRingQ: prover.baseRingQ,

		encoder:      prover.encoder.ShallowCopy(),
		polyVerifier: celpc.NewVerifier(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,
	}

	return prover, verifier, nil
}
