<h1 align="center">Ringo-SNARK</h1>
<p align="center">A Zero-Knowledge PIOP Toolkit for Ring-LWE Relations</p>
<p align="center"><img src="LOGO.png" width="300"/></p>

> [!IMPORTANT]
> This library is under construction!

**Ringo-SNARK** is a Go library that offers efficient and simple API for proving relationships commonly used in lattice-based cryptosystems.

This library consists of two parts:

1. **CELPC** [[HSS24](https://eprint.iacr.org/2024/306)], a lattice-based PCS (Polynomial Commitment Scheme) with post-quantum security and transparent setup. More importantly, CELPC naturally supports polynomials over very large prime fields, making it a suitable candidate for proving relations over typical FHE parameters.
2. **Buckler** [[HLSS24](https://eprint.iacr.org/2024/1879)], a zero-knowledge PIOP (Polynomial Interactive Oracle Proof) toolkit for relationships over power-of-two cyclotomic rings, which is commonly used in lattice-based cryptography.

## Examples

For more examples, see `examples/` folder.

```go
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
		/* Excluded for brevity */
	}.Compile()

	// Now, generate the witness.
	ringQ := bigring.NewCyclotomicRing(paramsLogN13LogQ212.Degree(), paramsLogN13LogQ212.Modulus())
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
		// All non-witness fields should be set for correct compilation.
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
	proof, err := prover.Prove(ck, &assignment)
	if err != nil {
		panic(err)
	}

	// Verify the proof.
	vf := verifier.Verify(ck, proof)
	fmt.Println("Verification result:", vf)
}
```

## TODO
- [x] Arithmetic Constraints
- [x] Infinite-Norm Contraints
- [x] NTT Contraints
- [x] Automorphism Constraints
- [x] Arbitrary Linear Constraints
- [x] Sumcheck
- [x] Two-Norm Constraints
- [ ] Approximate Infinite-Norm Constraints (via Modular J-L)
- [ ] Approximate Two-Norm Constraints (via Modular J-L)
- [ ] Strong Fiat-Shamir Transform
- [ ] Automatic Parameter Selection

## Citing
To cite Ringo-SNARK, please use the following BibTeX entry:
```tex
@misc{Ringo-SNARK,
  title={{Ringo-SNARK}},
  author={Intak Hwang, Seonhong Min},
  year={2025},
  howpublished = {Online: \url{https://github.com/sp301415/ringo-snark}},
}
```

## References
- Concretely Efficient Lattice-based Polynomial Commitment from Standard Assumptions (https://eprint.iacr.org/2024/306)
- Practical Zero-Knowledge PIOP for Public Key and Ciphertext Generation in (Multi-Group) Homomorphic Encryption (https://eprint.iacr.org/2024/1879)
- On the Security and Privacy of CKKS-based Homomorphic Evaluation Protocols (https://eprint.iacr.org/2025/382)
