package buckler

import (
	"math/big"
)

// ArithmeticConstraint is the aritmetic constraint for the circuit.
type ArithmeticConstraint struct {
	degree              int
	coeffsBig           []*big.Int
	coeffsPublicWitness []int64
	witness             [][]int64
}

// AddTerm adds a term to the constraint.
// This adds coeff * coeffPublicWitness * witness[0] * witness[1] * ... * witness[n] to the constraint.
// If coeffPublicWitness is nil, it is ignored.
func (c *ArithmeticConstraint) AddTerm(coeff *big.Int, coeffPublicWitness PublicWitness, witness ...Witness) {
	c.coeffsBig = append(c.coeffsBig, big.NewInt(0).Set(coeff))

	if coeffPublicWitness != nil {
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, coeffPublicWitness[0].Int64())
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
