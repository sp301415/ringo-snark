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

// AddInt64Term adds a int64 term to the constraint.
func (c *ArithmeticConstraint) AddInt64Term(coeff int64, witness ...Witness) {
	c.AddTerm(coeff, big.NewInt(1), nil, witness...)
}

// AddBigTerm adds a big.Int term to the constraint.
func (c *ArithmeticConstraint) AddBigTerm(coeff *big.Int, witness ...Witness) {
	c.AddTerm(1, coeff, nil, witness...)
}

// AddPublicWitnessTerm adds a public witness term to the constraint.
func (c *ArithmeticConstraint) AddPublicWitnessTerm(coeff PublicWitness, witness ...Witness) {
	c.AddTerm(1, big.NewInt(1), coeff, witness...)
}

// AddTerm adds a term to the constraint.
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
