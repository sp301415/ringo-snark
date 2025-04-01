package buckler

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/celpc"
)

// PublicWitness is a public witness for the relation.
type PublicWitness []*big.Int

// ProverWitness is a private witness for the relation, used for proving.
type ProverWitness = []*big.Int

// VerifierWitness is a private witness for the relation, used for verifying.
type VerifierWitness = celpc.Commitment

// Witness is a private witness for the relation.
// Must be []*[big.Int] in case for proving,
// and must [celpc.Opening] in case for verifying.
type Witness interface {
	ProverWitness | VerifierWitness
}

// Circuit is a relation.
// Must have a field of type PublicWitness or Witness.
// To define a relation, implement the Circuit interface by defining the Define method.
type Circuit[W Witness] interface {
	// Define defines the relation.
	Define(ctx Context[W])
}
