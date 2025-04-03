package buckler

import (
	"math/big"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
)

// Proof is the proof for the circuit.
type Proof struct {
	PublicWitness []PublicWitness
	Witness       []celpc.Commitment
	OpeningProof  celpc.OpeningProof

	LinCheckMaskCommitment

	RowCheckCommitment
	LinCheckCommitment

	EvalProofs []celpc.EvaluationProof
	RowCheckEvaluationProof
	LinCheckEvaluationProof
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

// LinCheckMaskCommitment is the masking polynomial for the linear check.
type LinCheckMaskCommitment struct {
	MaskCommitment celpc.Commitment
	OpeningProof   celpc.OpeningProof
	MaskSum        *big.Int
}

type linCheckMask struct {
	Mask        bigring.BigPoly
	MaskOpening celpc.Opening
}

// LinCheckCommitment is the first move of the linear check.
type LinCheckCommitment struct {
	QuoCommitment      celpc.Commitment
	RemCommitment      celpc.Commitment
	RemShiftCommitment celpc.Commitment
	OpeningProof       celpc.OpeningProof
}

type linCheckOpening struct {
	QuoOpening      celpc.Opening
	RemOpening      celpc.Opening
	RemShiftOpening celpc.Opening
}

// LinCheckEvaluationProof is the second move of the linear check.
type LinCheckEvaluationProof struct {
	MaskEvalProof     celpc.EvaluationProof
	QuoEvalProof      celpc.EvaluationProof
	RemEvalProof      celpc.EvaluationProof
	RemShiftEvalProof celpc.EvaluationProof
}
