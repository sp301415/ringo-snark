package buckler

import (
	"github.com/sp301415/ringo-snark/math/num"
)

// ArithmeticConstraint is the arithmetic constraint for the circuit.
type ArithmeticConstraint[E num.Uint[E]] struct {
	wRank                 int
	coeffs                []E
	hasCoeffPublicWitness []bool
	coeffsPublicWitness   []uint64
	witness               [][]uint64
}

// AddTerm adds a term to the constraint.
// Specifically, it adds coeff * coeffPublicWitness * witness[0] * ... * witness[n] to the constraint.
// If coeffPublicWitness is nil, it is ignored.
func (c *ArithmeticConstraint[E]) AddTerm(coeff E, coeffPublicWitness PublicWitness[E], witness ...Witness[E]) {
	c.coeffs = append(c.coeffs, coeff)

	if coeffPublicWitness != nil {
		c.hasCoeffPublicWitness = append(c.hasCoeffPublicWitness, true)
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, witnessToID(coeffPublicWitness))
	} else {
		c.hasCoeffPublicWitness = append(c.hasCoeffPublicWitness, false)
		c.coeffsPublicWitness = append(c.coeffsPublicWitness, 0)
	}

	witnessID := make([]uint64, len(witness))
	for i := range witness {
		witnessID[i] = witnessToID(witness[i])
	}
	c.witness = append(c.witness, witnessID)

	if len(witness) > c.wRank {
		c.wRank = len(witness)
	}
}

// maxRank returns the maximum polynomial rank of the constraint.
func (c *ArithmeticConstraint[E]) maxRank(rank int) int {
	maxDeg := 0
	for i := range c.witness {
		deg := 0
		if c.hasCoeffPublicWitness[i] {
			deg += rank - 1
		}
		deg += len(c.witness[i]) * rank
		if deg > maxDeg {
			maxDeg = deg
		}
	}
	return maxDeg + 1
}
