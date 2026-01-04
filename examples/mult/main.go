package main

import (
	crand "crypto/rand"
	"fmt"
	"math/rand"
	"time"

	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/scratchpad/zp"
)

// In this example, we show how to prove the follwing relations:
//
//  X * Y = Z
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
type MultCircuit[E num.Uint[E]] struct {
	NTTTransformer buckler.LinearTransformer[E]

	YNTT buckler.PublicWitness[E]

	XCoeffs buckler.Witness[E]
	ZCoeffs buckler.Witness[E]

	XNTT buckler.Witness[E]
	ZNTT buckler.Witness[E]
}

// Again, just like gnark, we define a special method to constraint the circuit.
func (c *MultCircuit[E]) Define(ctx *buckler.Context[E]) {
	// "Empty" element for initialization
	var z E

	// XNTT = NTT(X)
	ctx.AddLinearConstraint(c.XNTT, c.XCoeffs, c.NTTTransformer)
	// // ZNTT = NTT(Z)
	ctx.AddLinearConstraint(c.ZNTT, c.ZCoeffs, c.NTTTransformer)

	// XNTT * YNTT - ZNTT = 0
	var multConstraint buckler.ArithmeticConstraint[E]
	multConstraint.AddTerm(z.New().SetInt64(1), c.YNTT, c.XNTT) // YNTT * XNTT
	multConstraint.AddTerm(z.New().SetInt64(-1), nil, c.ZNTT)   // - ZNTT
	ctx.AddArithmeticConstraint(multConstraint)

	// |X| <= 5
	ctx.AddInfNormConstraint(c.XCoeffs, 5)
}

func main() {
	// First, we should define the rank (aka the ring degree).
	rank := 1 << 13

	// Now, generate the witness.
	ringQ := bigpoly.NewCyclotomicEvaluator[*zp.Uint](rank)
	X := ringQ.NewPoly(false)
	Y := ringQ.NewPoly(false)
	for i := 0; i < ringQ.Rank(); i++ {
		X.Coeffs[i].SetInt64(rand.Int63() % 6) // Less or equal to 5
		Y.Coeffs[i].SetInt64(rand.Int63())
	}

	XNTT := ringQ.NTT(X)
	YNTT := ringQ.NTT(Y)
	ZNTT := ringQ.Mul(XNTT, YNTT)
	Z := ringQ.InvNTT(ZNTT)

	// Generate the CRS.
	crs := make([]byte, 16)
	crand.Read(crs)

	// We compile an empty circuit, and get prover and verifier.
	// Ideally, this should be done by the prover and verifier, respectively.
	c := MultCircuit[*zp.Uint]{
		NTTTransformer: buckler.NewNTTTransformer[*zp.Uint](rank),
	}
	prover, verifier, err := buckler.Compile(rank, &c, crs)
	if err != nil {
		panic(err)
	}

	// Using the generated prover, we can generate a proof.
	// Assign the public and secret witness to the circuit.
	assignment := MultCircuit[*zp.Uint]{
		YNTT: YNTT.Coeffs,

		XCoeffs: X.Coeffs,
		ZCoeffs: Z.Coeffs,

		XNTT: XNTT.Coeffs,
		ZNTT: ZNTT.Coeffs,
	}
	now := time.Now()
	proof, err := prover.Prove(&assignment)
	fmt.Println("Prover time:", time.Since(now))
	if err != nil {
		panic(err)
	}

	// Verifier should assign the public witness as well.
	publicAssignment := MultCircuit[*zp.Uint]{
		YNTT: YNTT.Coeffs,
	}

	// Verify the proof.
	now = time.Now()
	vf := verifier.Verify(&publicAssignment, proof)
	fmt.Println("Verifier time:", time.Since(now))
	fmt.Println("Verification result:", vf)
}
