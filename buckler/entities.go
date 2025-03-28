package buckler

import "github.com/sp301415/rlwe-piop/celpc"

// RowCheckFirstMove is the first move of the row check.
type RowCheckFirstMove struct {
	QuoCommitment      celpc.Commitment
	QuoShiftCommitment celpc.Commitment

	OpeningProof celpc.OpeningProof
}
