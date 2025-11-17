<h1 align="center">Ringo-SNARK</h1>
<p align="center">A Zero-Knowledge PIOP Toolkit for Ring-LWE Relations</p>
<p align="center"><img src="LOGO.png" width="300"/></p>

> [!IMPORTANT]
> This library is under construction!

**Ringo-SNARK** is a Go library that offers efficient and simple API for proving relationships commonly used in lattice-based cryptosystems.

This library consists of two parts:

1. **Jindo**, a lattice-based PCS (Polynomial Commitment Scheme) with post-quantum security and transparent setup. More importantly, CELPC naturally supports polynomials over very large prime fields, making it a suitable candidate for proving relations over typical FHE parameters.
2. **Buckler** [[HLSS24](https://eprint.iacr.org/2024/1879)], a zero-knowledge PIOP (Polynomial Interactive Oracle Proof) toolkit for relationships over power-of-two cyclotomic rings, which is commonly used in lattice-based cryptography.

## Usage

First, you must run `jindo-modulus` binary to generate optimized code for input modulus.
```
$ go run ./jindo-modulus -n <target bits> -o <target-directory>
```
This creates a package called `zp` in the target directory. You may need to install `asmfmt` as follows.
```
$ go install github.com/klauspost/asmfmt/cmd/asmfmt@latest
```

TODO: Fill the rest


## TODO
- [ ] Arithmetic Constraints
- [ ] Infinite-Norm Contraints
- [ ] NTT Contraints
- [ ] Automorphism Constraints
- [ ] Arbitrary Linear Constraints
- [ ] Sumcheck
- [ ] Two-Norm Constraints
- [ ] Approximate Infinite-Norm Constraints (via Modular J-L)
- [ ] Approximate Two-Norm Constraints (via Modular J-L)
- [ ] Strong Fiat-Shamir Transform
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
