<h1 align="center">RLWE-PIOP</h1>
<p align="center">A PIOP Toolkit for Ring-LWE Relations</p>

> [!IMPORTANT]
> This library is under construction!

**rlwe-piop** is a Go library that offers efficient and simple API for proving relationships commonly used in lattice-based cryptosystems that rely on Ring-LWE problem.

This library consists of two parts:

1. **CELPC** [[HSS24](https://eprint.iacr.org/2024/306)], a lattice-based PCS (Polynomial Commitment Scheme) with post-quantum security and transparent setup. More importantly, CELPC naturally supports polynomials over very large prime fields, making it a suitable candidate for proving relations over typical FHE parameters.
2. **Buckler** [[HLSS24](https://eprint.iacr.org/2024/1879)], a zero-knowledge PIOP (Polynomial Interactive Oracle Proof) toolkit for relationships over power-of-two cyclotomic rings, which is commonly used in lattice-based cryptography.
