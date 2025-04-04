<h1 align="center">Cyclone</h1>
<p align="center">A Zero-Knowledge PIOP Toolkit for Ring-LWE Relations</p>

> [!IMPORTANT]
> This library is under construction!

**Cyclone** is a Go library that offers efficient and simple API for proving relationships commonly used in lattice-based cryptosystems.

This library consists of two parts:

1. **CELPC** [[HSS24](https://eprint.iacr.org/2024/306)], a lattice-based PCS (Polynomial Commitment Scheme) with post-quantum security and transparent setup. More importantly, CELPC naturally supports polynomials over very large prime fields, making it a suitable candidate for proving relations over typical FHE parameters.
2. **Buckler** [[HLSS24](https://eprint.iacr.org/2024/1879)], a zero-knowledge PIOP (Polynomial Interactive Oracle Proof) toolkit for relationships over power-of-two cyclotomic rings, which is commonly used in lattice-based cryptography.

## References
- Concretely Efficient Lattice-based Polynomial Commitment from Standard Assumptions (https://eprint.iacr.org/2024/306)
- Practical Zero-Knowledge PIOP for Public Key and Ciphertext Generation in (Multi-Group) Homomorphic Encryption (https://eprint.iacr.org/2024/1879)
- On the Security and Privacy of CKKS-based Homomorphic Evaluation Protocols (https://eprint.iacr.org/2025/382)
