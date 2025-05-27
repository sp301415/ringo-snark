package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
)

// Proof is the proof for the circuit.
type Proof struct {
	PublicWitness []PublicWitness
	Witness       []celpc.Commitment
	OpeningProof  celpc.OpeningProof

	LinCheckMaskCommitment SumCheckMaskCommitment
	SumCheckMaskCommitment

	RowCheckCommitment
	LinCheckCommitment SumCheckCommitment
	SumCheckCommitment

	EvalProofs []celpc.EvaluationProof
	RowCheckEvaluationProof
	LinCheckEvaluationProof SumCheckEvaluationProof
	SumCheckEvaluationProof
}

// RowCheckCommitment is the first move of the row check.
type RowCheckCommitment struct {
	QuoCommitment celpc.Commitment
	OpeningProof  celpc.OpeningProof
}

type rowCheckOpening struct {
	QuoOpening celpc.Opening
}

// RowCheckEvaluationProof is the second move of the row check.
type RowCheckEvaluationProof struct {
	QuoEvalProof celpc.EvaluationProof
}

// SumCheckMaskCommitment is the masking polynomial for the sumcheck.
type SumCheckMaskCommitment struct {
	MaskCommitment celpc.Commitment
	OpeningProof   celpc.OpeningProof
	MaskSum        *big.Int
}

type sumCheckMask struct {
	Mask        bigring.BigPoly
	MaskOpening celpc.Opening
}

// SumCheckCommitment is the first move of the sumcheck.
type SumCheckCommitment struct {
	QuoCommitment      celpc.Commitment
	RemCommitment      celpc.Commitment
	RemShiftCommitment celpc.Commitment
	OpeningProof       celpc.OpeningProof
}

type sumCheckOpening struct {
	QuoOpening      celpc.Opening
	RemOpening      celpc.Opening
	RemShiftOpening celpc.Opening
}

// SumCheckEvaluationProof is the second move of the sumcheck.
type SumCheckEvaluationProof struct {
	MaskEvalProof     celpc.EvaluationProof
	QuoEvalProof      celpc.EvaluationProof
	RemEvalProof      celpc.EvaluationProof
	RemShiftEvalProof celpc.EvaluationProof
}
