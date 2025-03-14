package celpc_test

import (
	"math/big"
	"testing"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
	"github.com/stretchr/testify/assert"
)

var (
	params = celpc.ParamsLogN19LogP256.Compile()
)

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
