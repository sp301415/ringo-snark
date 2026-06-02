// Package crt implements the Chinese Remainder Theorem (CRT) for polynomial and vector arithmetic.
package crt

// Operator evaluates ring operations over [Poly].
//
// Operations usually take two forms: for example,
//   - Add(p0, p1) adds p0, p1, allocates a new vector to store the result and returns it.
//   - AddTo(pOut, p0, p1) adds p0, p1 and writes the result to pre-allocated pOut without returning.
//
// Moreover, operations panics when inputs are not consistent with the
// Operator's parameters, or operations itself are not valid.
