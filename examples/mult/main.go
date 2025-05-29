package main

import (
	"fmt"
	"math"
	"math/big"
	"math/rand"
	"time"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/celpc"
)

// In this example, we show how to prove the follwing relations:
//
// 	X * Y = Z
//  |X| <= 5
//
// Where X, Z are secret and Y is public.

// The core idea of buckler is to transform the arithmetic relation
// over the ring R_q to linear relations over Z_q^N.
// For instance, our relation can be transformed to:
//
//  XNTT = NTT(X)
//  ZNTT = NTT(Z)
//  XNTT * YNTT - ZNTT = 0
//  |X| <= 5
//
// Where * and - are element-wise vector operations.

// Just like gnark, we define a circuit type.
type MultCircuit struct {
	NTTTransformer buckler.TransposeTransformer

	YNTT buckler.PublicWitness

	XCoeffs buckler.Witness
	ZCoeffs buckler.Witness

	XNTT buckler.Witness
	ZNTT buckler.Witness
}

// Again, just like gnark, we define a special method to constraint the circuit.
func (c *MultCircuit) Define(ctx *buckler.Context) {
	// XNTT = NTT(X)
	ctx.AddLinearConstraint(c.NTTTransformer, c.XCoeffs, c.XNTT)
	// ZNTT = NTT(Z)
	ctx.AddLinearConstraint(c.NTTTransformer, c.ZCoeffs, c.ZNTT)

	// XNTT * YNTT - ZNTT = 0
	var multConstraint buckler.ArithmeticConstraint
	multConstraint.AddTerm(big.NewInt(1), c.YNTT, c.XNTT) // YNTT * XNTT
	multConstraint.AddTerm(big.NewInt(-1), nil, c.ZNTT)   // - ZNTT
	ctx.AddArithmeticConstraint(multConstraint)

	// |X| <= 5
	ctx.AddInfNormConstraint(c.XCoeffs, 5)
}

func main() {
	// First, we should define the Polynomial Commitment Parameters.
	paramsLogN13LogQ212 := celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 13,
		BigIntCommitSize: 1 << 11,

		ModulusBase: 9694,
		Digits:      16,

		RingDegree:     1 << 11,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10,
		OpeningProofStdDev: 32,
		BlindStdDev:        math.Exp2(19),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 64,
		BlindRandStdDev:        math.Exp2(20),

		OpenProofBound: math.Exp2(32.754070623437386),
		EvalProofBound: math.Exp2(48.75847312606874),
	}.Compile()

	// Now, generate the witness.
	ringQ := bigring.NewBigRing(paramsLogN13LogQ212.Degree(), paramsLogN13LogQ212.Modulus())
	X := ringQ.NewPoly()
	Y := ringQ.NewPoly()
	for i := 0; i < paramsLogN13LogQ212.Degree(); i++ {
		X.Coeffs[i].SetInt64(rand.Int63() % 6) // Less or equal to 5
		Y.Coeffs[i].SetInt64(rand.Int63())
	}

	XNTT := ringQ.ToNTTPoly(X)
	YNTT := ringQ.ToNTTPoly(Y)
	ZNTT := ringQ.MulNTT(XNTT, YNTT)
	Z := ringQ.ToPoly(ZNTT)

	// Generate the CRS.
	ck := celpc.GenAjtaiCommitKey(paramsLogN13LogQ212)

	// We compile an empty circuit, and get prover and verifier.
	// Ideally, this should be done by the prover and verifier, respectively.
	c := MultCircuit{
		NTTTransformer: buckler.NewNTTTransformer(ringQ),
	}
	prover, verifier, err := buckler.Compile(paramsLogN13LogQ212, &c)
	if err != nil {
		panic(err)
	}

	// Using the generated prover, we can generate a proof.
	// Assign the public and secret witness to the circuit.
	assignment := MultCircuit{
		YNTT: YNTT.Coeffs,

		XCoeffs: X.Coeffs,
		ZCoeffs: Z.Coeffs,

		XNTT: XNTT.Coeffs,
		ZNTT: ZNTT.Coeffs,
	}
	now := time.Now()
	proof, err := prover.ProveParallel(ck, &assignment)
	fmt.Println("Prover time:", time.Since(now))
	if err != nil {
		panic(err)
	}

	// Verify the proof.
	now = time.Now()
	vf := verifier.Verify(ck, proof)
	fmt.Println("Verifier time:", time.Since(now))
	fmt.Println("Verification result:", vf)
}
