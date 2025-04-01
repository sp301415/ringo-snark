package buckler

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/celpc"
)

// Context is the context for proving or verifing the relation.
type Context[W Witness] interface {
	NewArithmeticCircuit() ArithmeticCircuit[W]
	AddArithmeticCircuit(c ArithmeticCircuit[W])
	AddNormCheck(w W, logBound int)
}

type proverContext struct {
	Parameters celpc.Parameters

	aritmeticCircuits []ArithmeticCircuit[ProverWitness]

	decomposedWitness map[**big.Int][][]*big.Int
}

func newProverContext(params celpc.Parameters) *proverContext {
	return &proverContext{
		Parameters: params,

		aritmeticCircuits: make([]ArithmeticCircuit[ProverWitness], 0),

		decomposedWitness: make(map[**big.Int][][]*big.Int, 0),
	}
}

func (ctx *proverContext) NewArithmeticCircuit() ArithmeticCircuit[ProverWitness] {
	return &arithmeticCircuitProve{}
}

func (ctx *proverContext) AddArithmeticCircuit(c ArithmeticCircuit[ProverWitness]) {
	ctx.aritmeticCircuits = append(ctx.aritmeticCircuits, c)
}

func (ctx *proverContext) AddNormCheck(w ProverWitness, logBound int) {
	if logBound == 0 {
		ternaryCheck := ctx.NewArithmeticCircuit()
		ternaryCheck.AddTerm(1, w, w, w)
		ternaryCheck.AddTerm(-1, w)
		ctx.AddArithmeticCircuit(ternaryCheck)
		return
	}

	wDecomposed := make([][]*big.Int, logBound+1)
	for i := 0; i < logBound+1; i++ {
		wDecomposed[i] = make([]*big.Int, ctx.Parameters.Degree())
	}

	for i := 0; i < ctx.Parameters.Degree(); i++ {
		dcmp := bigSignedDecompose(w[i], ctx.Parameters.Modulus(), logBound)
		for j := 0; j < logBound+1; j++ {
			wDecomposed[j][i] = dcmp[j]
		}
	}

	ctx.decomposedWitness[&w[:1][0]] = wDecomposed

	for i := 0; i < logBound+1; i++ {
		ternaryCheck := ctx.NewArithmeticCircuit()
		ternaryCheck.AddTerm(1, wDecomposed[i], wDecomposed[i], wDecomposed[i])
		ternaryCheck.AddTerm(-1, wDecomposed[i])
		ctx.AddArithmeticCircuit(ternaryCheck)
	}

	decompCheck := ctx.NewArithmeticCircuit()
	decompCheck.AddTerm(1, w)
	decompCheck.AddTerm(-1, wDecomposed[0])
	for i := 1; i < logBound+1; i++ {
		decompCheck.AddTerm(-(1 << (i - 1)), wDecomposed[i])
	}
	ctx.AddArithmeticCircuit(decompCheck)
}

type verifierContext struct {
	Parameters celpc.Parameters
	hash       *celpc.RandomOracle

	decomposedCommitments map[uint64][]celpc.Commitment

	aritmeticCircuits []ArithmeticCircuit[VerifierWitness]
}

func newVerifierContext(params celpc.Parameters, pf Proof) *verifierContext {
	return &verifierContext{
		Parameters: params,
		hash:       celpc.NewRandomOracle(params),

		decomposedCommitments: pf.DecomposedWitness,

		aritmeticCircuits: make([]ArithmeticCircuit[VerifierWitness], 0),
	}
}

func (ctx *verifierContext) NewArithmeticCircuit() ArithmeticCircuit[VerifierWitness] {
	return &arithmeticCircuitVerify{}
}

func (ctx *verifierContext) AddArithmeticCircuit(c ArithmeticCircuit[VerifierWitness]) {
	ctx.aritmeticCircuits = append(ctx.aritmeticCircuits, c)
}

func (ctx *verifierContext) AddNormCheck(w VerifierWitness, logBound int) {
	if logBound == 0 {
		ternaryCheck := ctx.NewArithmeticCircuit()
		ternaryCheck.AddTerm(1, w, w, w)
		ternaryCheck.AddTerm(-1, w)
		ctx.AddArithmeticCircuit(ternaryCheck)
		return
	}

	wHash := hashCommitment(w, ctx.hash)
	wDecomposed := ctx.decomposedCommitments[wHash]

	for i := 0; i < logBound+1; i++ {
		ternaryCheck := ctx.NewArithmeticCircuit()
		ternaryCheck.AddTerm(1, wDecomposed[i], wDecomposed[i], wDecomposed[i])
		ternaryCheck.AddTerm(-1, wDecomposed[i])
		ctx.AddArithmeticCircuit(ternaryCheck)
	}

	decompCheck := ctx.NewArithmeticCircuit()
	decompCheck.AddTerm(1, w)
	decompCheck.AddTerm(-1, wDecomposed[0])
	for i := 1; i < logBound+1; i++ {
		decompCheck.AddTerm(-(1 << (i - 1)), wDecomposed[i])
	}
	ctx.AddArithmeticCircuit(decompCheck)
}
