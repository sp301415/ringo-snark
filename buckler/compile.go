package buckler

import (
	"fmt"
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
)

type walker struct {
	publicWitnessCount int64
	witnessCount       int64
	circuitType        reflect.Type
}

func (w *walker) walkForCompile(v reflect.Value) error {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness{}):
		if !v.CanSet() {
			return fmt.Errorf("cannot set value")
		}
		v.Set(reflect.ValueOf([]*big.Int{big.NewInt(w.publicWitnessCount)}))
		w.publicWitnessCount++
		return nil
	case reflect.TypeOf(Witness{}):
		if !v.CanSet() {
			return fmt.Errorf("cannot set value")
		}
		v.Set(reflect.ValueOf([]*big.Int{big.NewInt(w.witnessCount)}))
		w.witnessCount++
		return nil
	}

	switch v.Kind() {
	case reflect.Ptr, reflect.Interface:
		if !v.IsNil() {
			w.walkForCompile(v.Elem())
		}
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

	return nil
}

// Compile compiles the circuit and returns the prover, verifier pair.
//
// For correct compilation, the [PublicWitness] and [Witness] field must be empty.
// Moreover, all other fields must be set correctly.
func Compile(params celpc.Parameters, c Circuit) (*Prover, *Verifier, error) {
	if reflect.TypeOf(c).Kind() != reflect.Ptr {
		return nil, nil, fmt.Errorf("circuit must be defined with a pointer receiver")
	}

	w := &walker{circuitType: reflect.TypeOf(c).Elem()}
	if err := w.walkForCompile(reflect.ValueOf(c)); err != nil {
		return nil, nil, err
	}

	ctx := newContext(params, w)
	ctx.prePublicWitnessCount = w.publicWitnessCount
	ctx.preWitnessCount = w.witnessCount

	c.Define(ctx)

	logEmbedDegree := int(math.Ceil(math.Log2(float64(ctx.maxDegree))))
	embedDegree := 1 << logEmbedDegree

	ringQ := bigring.NewCyclicRing(embedDegree, params.Modulus())
	encoder := NewEncoder(params, embedDegree)

	embedFactor := embedDegree / params.Degree()
	rootEmbed := ringQ.NthRoot()
	root2N := big.NewInt(0).Exp(rootEmbed, big.NewInt(int64(embedFactor/2)), nil)
	linCheckRingQ := bigring.NewCyclicRingFromRoot(params.Degree()<<1, params.Modulus(), root2N)

	linCheckEncoder := encoder.ShallowCopy()
	linCheckEncoder.EmbedDegree = 2 * params.Degree()

	prover := &Prover{
		Parameters: params,

		reducer: bigring.NewReducer(params.Modulus()),

		ringQ:         ringQ.ShallowCopy(),
		linCheckRingQ: linCheckRingQ.ShallowCopy(),

		encoder:         encoder.ShallowCopy(),
		linCheckEncoder: linCheckEncoder.ShallowCopy(),

		polyProver: celpc.NewProver(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,

		buffer:         newProverBuffer(params, ringQ, ctx),
		rowCheckBuffer: newRowCheckBuffer(params, ringQ, ctx),
		linCheckBuffer: newLinCheckBuffer(params, linCheckRingQ, ctx),
		sumCheckBuffer: newSumCheckBuffer(params, ringQ, ctx),
	}

	verifier := &Verifier{
		Parameters: params,

		reducer: bigring.NewReducer(params.Modulus()),

		ringQ: ringQ.ShallowCopy(),

		encoder:      encoder.ShallowCopy(),
		polyVerifier: celpc.NewVerifier(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,

		buffer: newVerifierBuffer(params, ringQ, ctx),
	}

	return prover, verifier, nil
}
