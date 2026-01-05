package buckler

import "github.com/sp301415/ringo-snark/math/bignum"

// PublicWitness is a public witness for the relation.
type PublicWitness[E bignum.Uint[E]] []E

// Witness is a witness for the relation.
type Witness[E bignum.Uint[E]] []E

// Circuit is a relation to prove.
// Must have a field of type PublicWitness or Witness.
// To define a relation, implement the Circuit interface by defining the Define method.
// Note that the Define method should be defined with a pointer reciever.
type Circuit[E bignum.Uint[E]] interface {
	// Define defines the relation.
	Define(ctx *Context[E])
}
