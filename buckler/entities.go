package buckler

import (
	"github.com/sp301415/ringo-snark/jindo"
	"github.com/sp301415/ringo-snark/math/bignum"
)

// Proof is the proof for the circuit.
type Proof[E bignum.Uint[E]] struct {
	Witness []*jindo.Commitment

	LinCheckMaskSum E
	SumCheckMaskSum E

	Evals     []E
	EvalProof *jindo.Proof
}
