package buckler

import (
	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

// Prover is a prover for Buckler PIOP.
type Prover struct {
	Parameters  celpc.Parameters
	EmbedDegree int

	Encoder    *Encoder
	PolyProver *celpc.Prover

	RingQ *bigring.BigRing

	Oracle *celpc.RandomOracle
}

// NewProver creates a new Prover.
func NewProver(params celpc.Parameters, embedDegree int, ck celpc.AjtaiCommitKey) *Prover {
	return &Prover{
		Parameters:  params,
		EmbedDegree: embedDegree,

		Encoder:    NewEncoder(params, embedDegree),
		PolyProver: celpc.NewProver(params, ck),

		RingQ: bigring.NewBigRing(embedDegree, params.Modulus()),

		Oracle: celpc.NewRandomOracle(params),
	}
}
