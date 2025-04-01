package buckler

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/celpc"
)

// ArithmeticCircuit is a arithmetic constraint.
type ArithmeticCircuit[W Witness] interface {
	// AddTerm adds a term to the circuit.
	AddTerm(coeff int64, x ...W)
	// AddBigIntTerm adds a term to the circuit.
	AddBigIntTerm(coeff *big.Int, x ...W)
	// AddPublicWitnessTerm adds a term to the circuit.
	AddPublicWitnessTerm(coeff int64, pw PublicWitness, x ...W)
}

type arithmeticCircuitProve struct {
	coeffInt64         []int64
	coeffBigInt        []*big.Int
	coeffPublicWitness [][]*big.Int
	monomials          [][][]*big.Int
}

func (c *arithmeticCircuitProve) AddTerm(coeff int64, x ...ProverWitness) {
	c.coeffInt64 = append(c.coeffInt64, coeff)
	c.coeffBigInt = append(c.coeffBigInt, big.NewInt(1))
	c.coeffPublicWitness = append(c.coeffPublicWitness, nil)

	monomials := make([][]*big.Int, len(x))
	for i := range x {
		monomials[i] = x[i]
	}
	c.monomials = append(c.monomials, monomials)
}

func (c *arithmeticCircuitProve) AddBigIntTerm(coeff *big.Int, x ...ProverWitness) {
	c.coeffInt64 = append(c.coeffInt64, 1)
	c.coeffBigInt = append(c.coeffBigInt, coeff)
	c.coeffPublicWitness = append(c.coeffPublicWitness, nil)

	monomials := make([][]*big.Int, len(x))
	for i := range x {
		monomials[i] = x[i]
	}
	c.monomials = append(c.monomials, monomials)
}

func (c *arithmeticCircuitProve) AddPublicWitnessTerm(coeff int64, pw PublicWitness, x ...ProverWitness) {
	c.coeffInt64 = append(c.coeffInt64, coeff)
	c.coeffBigInt = append(c.coeffBigInt, big.NewInt(1))
	c.coeffPublicWitness = append(c.coeffPublicWitness, pw)

	monomials := make([][]*big.Int, len(x))
	for i := range x {
		monomials[i] = x[i]
	}
	c.monomials = append(c.monomials, monomials)
}

type arithmeticCircuitVerify struct {
	coeffInt64         []int64
	coeffBigInt        []*big.Int
	coeffPublicWitness [][]*big.Int
	monomials          [][]celpc.Commitment
}

func (c *arithmeticCircuitVerify) AddTerm(coeff int64, x ...VerifierWitness) {
	c.coeffInt64 = append(c.coeffInt64, coeff)
	c.coeffBigInt = append(c.coeffBigInt, big.NewInt(1))
	c.coeffPublicWitness = append(c.coeffPublicWitness, nil)

	monmials := make([]celpc.Commitment, len(x))
	for i := range x {
		monmials[i] = x[i]
	}
	c.monomials = append(c.monomials, monmials)
}

func (c *arithmeticCircuitVerify) AddBigIntTerm(coeff *big.Int, x ...VerifierWitness) {
	c.coeffInt64 = append(c.coeffInt64, 1)
	c.coeffBigInt = append(c.coeffBigInt, coeff)
	c.coeffPublicWitness = append(c.coeffPublicWitness, nil)

	monmials := make([]celpc.Commitment, len(x))
	for i := range x {
		monmials[i] = x[i]
	}
	c.monomials = append(c.monomials, monmials)
}

func (c *arithmeticCircuitVerify) AddPublicWitnessTerm(coeff int64, pw PublicWitness, x ...VerifierWitness) {
	c.coeffInt64 = append(c.coeffInt64, coeff)
	c.coeffBigInt = append(c.coeffBigInt, big.NewInt(1))
	c.coeffPublicWitness = append(c.coeffPublicWitness, pw)

	monmials := make([]celpc.Commitment, len(x))
	for i := range x {
		monmials[i] = x[i]
	}
	c.monomials = append(c.monomials, monmials)
}
