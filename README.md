<h1 align="center">Ringo-SNARK</h1>
<p align="center">A Zero-Knowledge PIOP Toolkit for Ring-LWE Relations</p>
<p align="center"><img src="LOGO.png" width="300"/></p>

> [!IMPORTANT]
> This library is under construction!

**Ringo-SNARK** is a Go library that offers efficient and simple API for proving relationships commonly used in lattice-based cryptosystems.

This library consists of two parts:

1. **Jindo** [[HLSS25](https://eprint.iacr.org/2026/044)], a lattice-based PCS (Polynomial Commitment Scheme) with post-quantum security and transparent setup. More importantly, Jindo naturally supports polynomials over very large prime fields, making it a suitable candidate for proving relations over typical FHE parameters.
2. **Buckler** [[HLSS24](https://eprint.iacr.org/2024/1879)], a zero-knowledge PIOP (Polynomial Interactive Oracle Proof) toolkit for relationships over cyclotomic rings, which is commonly used in lattice-based cryptography.

## Usage

First, run `jindo-modulus` binary to generate optimized code for input modulus.
```
$ go install github.com/sp301415/ringo-snark/jindo-modulus@latest
$ jindo-modulus -n <target bits> -o <target-directory>
```
This creates a package called `zp` in the target directory. You may need to install `asmfmt` as follows.
```
$ go install github.com/klauspost/asmfmt/cmd/asmfmt@latest
```

Then, define a circuit that holds the witnesses.
```go
// Just like gnark, we define a circuit type.
type MultCircuit[E bignum.Uint[E]] struct {
	NTTChecker buckler.LinearChecker[E]

	YNTT buckler.PublicWitness[E]

	XCoeffs buckler.Witness[E]
	ZCoeffs buckler.Witness[E]

	XNTT buckler.Witness[E]
	ZNTT buckler.Witness[E]
}
```

Now, add constraints to the circuit by defining the `Define` method.
```go 
func (c *MultCircuit[E]) Define(ctx *buckler.Context[E]) {
	// "Empty" element for initialization
	var z E

	// XNTT = NTT(X)
	ctx.AddLinearConstraint(c.XNTT, c.XCoeffs, c.NTTChecker)
	// // ZNTT = NTT(Z)
	ctx.AddLinearConstraint(c.ZNTT, c.ZCoeffs, c.NTTChecker)

	// XNTT * YNTT - ZNTT = 0
	var multConstraint buckler.ArithmeticConstraint[E]
	multConstraint.AddTermWithConst(z.New().SetInt64(1), c.YNTT, c.XNTT) // YNTT * XNTT
	multConstraint.AddTermWithConst(z.New().SetInt64(-1), nil, c.ZNTT)   // - ZNTT
	ctx.AddArithmeticConstraint(multConstraint)

	// |X| <= 5
	ctx.AddInfNormConstraint(c.XCoeffs, 5)
}
```

Finally, you can create an "empty" circuit to generate the prover or the verifier.
Then, assign the witness to generate the proof.
```go
// Generate the CRS.
crs := make([]byte, 16)
crand.Read(crs)

// We compile an empty circuit, and get prover and verifier.
// Ideally, this should be done by the prover and verifier, respectively.
c := MultCircuit[*zp.Uint]{
	NTTChecker: buckler.NewNTTChecker[*zp.Uint](rank),
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

fmt.Println("Estimated Proof Size:", prover.JindoParams.Size()/math.Exp2(23), "MB")
```

## TODO
- [x] Arithmetic Constraints
- [x] Infinite-Norm Contraints
- [x] NTT Contraints
- [x] Automorphism Constraints
- [x] Arbitrary Linear Constraints
- [x] Sumcheck
- [x] Two-Norm Constraints
- [x] Approximate Infinite-Norm Constraints (via Modular J-L)
- [ ] Approximate Two-Norm Constraints (via Modular J-L)
- [x] Strong Fiat-Shamir Transform
- [x] Automatic Parameter Selection

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
- Practical TFHE Ciphertext Sanitization for Oblivious Circuit Evaluation (https://eprint.iacr.org/2025/216)
- Jindo: Practical Lattice-Based Polynomial Commitment for Zero-Knowledge Arguments (https://eprint.iacr.org/2026/044)
