package celpc_test

import (
	"fmt"
	"math"
	"math/big"
	"testing"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/stretchr/testify/assert"
)

var (
	params            = celpc.ParamsLogN19LogP256.Compile()
	paramsLiteralList = []celpc.ParametersLiteral{
		celpc.ParamsLogN19LogP256,
		celpc.ParamsLogN21LogP256,
		celpc.ParamsLogN23LogP256,
		celpc.ParamsLogN25LogP256,
	}
)

func TestParameters(t *testing.T) {
	for _, paramsLiteral := range paramsLiteralList {
		logN := int(math.Log2(float64(paramsLiteral.Degree)))
		t.Run(fmt.Sprintf("Compile/LogN=%v", logN), func(t *testing.T) {
			assert.NotPanics(t, func() { paramsLiteral.Compile() })
		})
	}
}

func TestEncoder(t *testing.T) {
	ecd := celpc.NewEncoder(params)
	oracle := celpc.NewRandomOracle(params)

	v := make([]*big.Int, 2*params.Slots())
	for i := 0; i < len(v); i++ {
		v[i] = big.NewInt(0)
		oracle.SampleModAssign(v[i])
	}

	t.Run("Encode", func(t *testing.T) {
		pOut := ecd.EncodeChunk(v)
		vOut := ecd.DecodeChunk(pOut)
		assert.Equal(t, v, vOut)
	})

	t.Run("RandomEncode", func(t *testing.T) {
		pOut := ecd.RandomEncodeChunk(v, params.BlindRandStdDev())
		vOut := ecd.DecodeChunk(pOut)
		assert.Equal(t, v, vOut)
	})
}

func TestCommitment(t *testing.T) {
	ck := celpc.GenAjtaiCommitKey(params)
	prover := celpc.NewProver(params, ck)
	verifier := celpc.NewVerifier(params, ck)
	oracle := celpc.NewRandomOracle(params)

	v := bigring.BigPoly{Coeffs: make([]*big.Int, params.BigIntCommitSize())}
	for i := 0; i < v.Degree(); i++ {
		v.Coeffs[i] = big.NewInt(0)
		oracle.SampleModAssign(v.Coeffs[i])
	}

	t.Run("Commit", func(t *testing.T) {
		com, open := prover.Commit(v)
		openPf := prover.ProveOpening([]celpc.Commitment{com}, []celpc.Opening{open})

		assert.True(t, verifier.VerifyOpeningProof([]celpc.Commitment{com}, openPf))
	})

	t.Run("CommitParallel", func(t *testing.T) {
		com, open := prover.CommitParallel(v)
		openPf := prover.ProveOpeningParallel([]celpc.Commitment{com}, []celpc.Opening{open})

		assert.True(t, verifier.VerifyOpeningProof([]celpc.Commitment{com}, openPf))
	})

	t.Run("Evaluate", func(t *testing.T) {
		x := big.NewInt(0)
		oracle.SampleModAssign(x)

		com, open := prover.Commit(v)
		evalPf := prover.Evaluate(x, open)

		assert.True(t, verifier.VerifyEvaluation(x, com, evalPf))

		valueReal := big.NewInt(0)
		for i := v.Degree() - 1; i >= 0; i-- {
			valueReal.Mul(valueReal, x)
			valueReal.Add(valueReal, v.Coeffs[i])
			valueReal.Mod(valueReal, params.Modulus())
		}

		assert.Equal(t, valueReal, evalPf.Value)
	})

	t.Run("EvaluateParallel", func(t *testing.T) {
		x := big.NewInt(0)
		oracle.SampleModAssign(x)

		com, open := prover.Commit(v)
		evalPf := prover.EvaluateParallel(x, open)

		if !verifier.VerifyEvaluation(x, com, evalPf) {
			t.Errorf("Evaluation verification failed")
		}

		valueReal := big.NewInt(0)
		for i := v.Degree() - 1; i >= 0; i-- {
			valueReal.Mul(valueReal, x)
			valueReal.Add(valueReal, v.Coeffs[i])
			valueReal.Mod(valueReal, params.Modulus())
		}

		assert.Equal(t, valueReal, evalPf.Value)
	})
}

func BenchmarkCommitment(b *testing.B) {
	for _, paramsLiteral := range paramsLiteralList {
		params := paramsLiteral.Compile()
		logN := int(math.Log2(float64(params.Degree())))

		ck := celpc.GenAjtaiCommitKey(params)
		prover := celpc.NewProver(params, ck)
		verifier := celpc.NewVerifier(params, ck)
		oracle := celpc.NewRandomOracle(params)

		v := bigring.BigPoly{Coeffs: make([]*big.Int, params.Degree())}
		for i := 0; i < v.Degree(); i++ {
			v.Coeffs[i] = big.NewInt(0)
			oracle.SampleModAssign(v.Coeffs[i])
		}

		com := celpc.NewCommitment(params, params.Degree())
		open := celpc.NewOpening(params, params.Degree())
		openPf := celpc.NewOpeningProof(params)
		evalPf := celpc.NewEvaluationProof(params)

		b.Run(fmt.Sprintf("Commit/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.CommitAssign(v, com, open)
			}
		})

		b.Run(fmt.Sprintf("CommitParallel/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.CommitParallelAssign(v, com, open)
			}
		})

		b.Run(fmt.Sprintf("ProveOpening/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.ProveOpeningAssign([]celpc.Commitment{com}, []celpc.Opening{open}, openPf)
			}
		})

		b.Run(fmt.Sprintf("ProveOpeningParallel/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.ProveOpeningParallelAssign([]celpc.Commitment{com}, []celpc.Opening{open}, openPf)
			}
		})

		x := big.NewInt(0)
		oracle.SampleModAssign(x)

		b.Run(fmt.Sprintf("Evaluate/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.EvaluateAssign(x, open, evalPf)
			}
		})

		b.Run(fmt.Sprintf("EvaluateParallel/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				prover.EvaluateParallelAssign(x, open, evalPf)
			}
		})

		b.Run(fmt.Sprintf("VerifyOpeningProof/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				verifier.VerifyOpeningProof([]celpc.Commitment{com}, openPf)
			}
		})

		b.Run(fmt.Sprintf("VerifyEvaluation/LogN=%v", logN), func(b *testing.B) {
			for i := 0; i < b.N; i++ {
				verifier.VerifyEvaluation(x, com, evalPf)
			}
		})
	}
}

func BenchmarkProfile(b *testing.B) {
	params := celpc.ParamsLogN19LogP256.Compile()

	ck := celpc.GenAjtaiCommitKey(params)
	prover := celpc.NewProver(params, ck)
	oracle := celpc.NewRandomOracle(params)

	v := bigring.BigPoly{Coeffs: make([]*big.Int, params.Degree())}
	for i := 0; i < v.Degree(); i++ {
		v.Coeffs[i] = big.NewInt(0)
		oracle.SampleModAssign(v.Coeffs[i])
	}

	// com := celpc.NewCommitment(params, params.Degree())
	// open := celpc.NewOpening(params, params.Degree())
	_, open := prover.Commit(v)
	// openPf := prover.ProveOpening([]celpc.Commitment{com}, []celpc.Opening{open})
	evalPf := celpc.NewEvaluationProof(params)
	x := oracle.SampleMod()

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		prover.EvaluateAssign(x, open, evalPf)
	}
}
