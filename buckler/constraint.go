package buckler

import (
	"math/big"
)

// ArithmeticConstraint is the aritmetic constraint for the circuit.
type ArithmeticConstraint struct {
	degree              int
	coeffsInt64         []int64
	coeffsBig           []*big.Int
	coeffsPublicWitness []int64
	witness             [][]int64
}

// AddTerm adds a term to the constraint.
// This adds coeffInt64 * coeffBig * coeff * witness[0] * witness[1] * ... * witness[n] to the constraint.
// If coeffBig and coeff is nil, they are assumed to be 1.
func (c *ArithmeticConstraint) AddTerm(coeffInt64 int64, coeffBig *big.Int, coeff PublicWitness, witness ...Witness) {
	c.coeffsInt64 = append(c.coeffsInt64, coeffInt64)
	c.coeffsBig = append(c.coeffsBig, coeffBig)

	if coeff != nil {
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, coeff[0].Int64())
	} else {
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, -1)
	}

	witnessID := make([]int64, len(witness))
	for i := 0; i < len(witness); i++ {
		witnessID[i] = witness[i][0].Int64()
	}
	c.witness = append(c.witness, witnessID)

	if len(witness) > c.degree {
		c.degree = len(witness)
	}
}
