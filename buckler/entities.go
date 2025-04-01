package buckler

import "github.com/sp301415/rlwe-piop/celpc"

// Proof is the proof of the relation.
type Proof struct {
	Witness           map[string]celpc.Commitment
	OpeningProof      celpc.OpeningProof
	DecomposedWitness map[uint64][]celpc.Commitment
	Evaluations       map[uint64]celpc.EvaluationProof

	RowCheckCommit RowCheckCommit
	RowCheckEval   RowCheckEval
}

// RowCheckCommit is the first move of the row check.
type RowCheckCommit struct {
	QuoCommitment      celpc.Commitment
	QuoShiftCommitment celpc.Commitment
	OpeningProof       celpc.OpeningProof
}

// RowCheckEval is the second move of the row check.
type RowCheckEval struct {
	QuoEval      celpc.EvaluationProof
	QuoShiftEval celpc.EvaluationProof
}
