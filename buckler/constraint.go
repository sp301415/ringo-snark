package buckler

import "github.com/sp301415/ringo-snark/math/num"

// ArithmeticConstraint is the arithmetic constraint for the circuit.
type ArithmeticConstraint[E num.Uint[E]] struct {
	rank                int
	coeffs              []E
	coeffsPublicWitness []uint64
	witness             [][]uint64
}

// AddTerm adds a term to the constraint.
// Specifically, it adds coeff * coeffPublicWitness * witness[0] * ... * witness[n] to the constraint.
// If coeffPublicWitness is nil, it is ignored.
func (c *ArithmeticConstraint[E]) AddTerm(coeff E, coeffPublicWitness PublicWitness[E], witness ...Witness[E]) {
	c.coeffs = append(c.coeffs, coeff)

	digits := make([]uint64, coeff.Limb())
	if coeffPublicWitness != nil {
		coeffPublicWitness[0].Slice(digits)
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, digits[0])
	} else {
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, 0)
	}

	witnessID := make([]uint64, len(witness))
	for i := range witness {
		witness[i][0].Slice(digits)
		witnessID[i] = digits[0]
	}
	c.witness = append(c.witness, witnessID)

	if len(witness) > c.rank {
		c.rank = len(witness)
	}
}
