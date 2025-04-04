package buckler

import (
	"math/big"
)

// PublicWitness is a public witness for the relation.
type PublicWitness []*big.Int

// Witness is a witness for the relation.
type Witness []*big.Int

// Circuit is a relation to prove.
// Must have a field of type PublicWitness or Witness.
// To define a relation, implement the Circuit interface by defining the Define method.
// Note that the Define method should be defined with a pointer reciever.
type Circuit interface {
	// Define defines the relation.
	Define(ctx *Context)
}
