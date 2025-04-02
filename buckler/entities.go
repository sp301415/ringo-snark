package buckler

import "github.com/sp301415/rlwe-piop/celpc"

// Proof is the proof for the circuit.
type Proof struct {
	PublicWitness []PublicWitness
	Witness       []celpc.Commitment
	OpeningProof  celpc.OpeningProof

	RowCheckCommit

	EvalProofs []celpc.EvaluationProof
	RowCheckEvalProof
}

// RowCheckCommit is the first move of the row check.
type RowCheckCommit struct {
	QuoCommitment      celpc.Commitment
	QuoShiftCommitment celpc.Commitment
	OpeningProof       celpc.OpeningProof
}

type rowCheckOpening struct {
	QuoOpening      celpc.Opening
	QuoShiftOpening celpc.Opening
}

// RowCheckEvalProof is the second move of the row check.
type RowCheckEvalProof struct {
	QuoEvalProof      celpc.EvaluationProof
	QuoShiftEvalProof celpc.EvaluationProof
}
