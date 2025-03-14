package celpc

import (
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

// Commitment is a polynomial commitment.
type Commitment struct {
	// Value is the committed polynomial.
	// Denoted as h.
	Value []AjtaiCommitment
}

// Opening is the opening of polynomial commitment.
type Opening struct {
	// Mask is the masking polynomial.
	// Denoted as h.
	Mask [][]ring.Poly
	// Rand is the random polynomial.
	// Denoted as eta.
	Rand [][]ring.Poly
}

// OpeningProof is a proof for polynomial opening.
type OpeningProof struct {
	// Commitment is the first move of the opening proof.
	Commitment []AjtaiCommitment
	// ResponseMask is the masking in the last move of the opening proof.
	ResponseMask [][]ring.Poly
	// ResponseRand is the randomness in the last move of the opening proof.
	ResponseRand [][]ring.Poly
}

// EvaluationProof is a proof for polynomial evaluation.
type EvaluationProof struct {
	// Value is the evaluated value of the polynomial.
	Value *big.Int
	// Mask is the masking polynomial.
	// Denoted as e.
	Mask []ring.Poly
	// Rand is the random polynomial.
	// Denoted as eta.
	Rand []ring.Poly
}

// NewCommitment creates a new Commitment.
func NewCommitment(params Parameters, N int) Commitment {
	splitCount := N / params.bigIntCommitSize

	com := make([]AjtaiCommitment, splitCount+2)
	for i := 0; i < splitCount+2; i++ {
		com[i] = NewAjtaiCommitment(params)
	}

	return Commitment{
		Value: com,
	}
}

// NewOpening creates a new Opening.
func NewOpening(params Parameters, N int) Opening {
	splitCount := N / params.bigIntCommitSize

	mask := make([][]ring.Poly, splitCount+2)
	for i := 0; i < splitCount+2; i++ {
		mask[i] = make([]ring.Poly, params.polyCommitSize)
		for j := 0; j < params.polyCommitSize; j++ {
			mask[i][j] = params.ringQ.NewPoly()
		}
	}

	rand := make([][]ring.Poly, splitCount+2)
	for i := 0; i < splitCount+2; i++ {
		rand[i] = make([]ring.Poly, params.ajtaiRandSize)
		for j := 0; j < params.ajtaiRandSize; j++ {
			rand[i][j] = params.ringQ.NewPoly()
		}
	}

	return Opening{
		Mask: mask,
		Rand: rand,
	}
}

// NewOpeningProof creates a new OpeningProof.
func NewOpeningProof(params Parameters) OpeningProof {
	com := make([]AjtaiCommitment, params.Repetition())
	resMask := make([][]ring.Poly, params.Repetition())
	resRand := make([][]ring.Poly, params.Repetition())
	for i := 0; i < params.Repetition(); i++ {
		com[i] = NewAjtaiCommitment(params)

		resMask[i] = make([]ring.Poly, params.polyCommitSize)
		for j := 0; j < params.polyCommitSize; j++ {
			resMask[i][j] = params.ringQ.NewPoly()
		}

		resRand[i] = make([]ring.Poly, params.ajtaiRandSize)
		for j := 0; j < params.ajtaiRandSize; j++ {
			resRand[i][j] = params.ringQ.NewPoly()
		}
	}

	return OpeningProof{
		Commitment:   com,
		ResponseMask: resMask,
		ResponseRand: resRand,
	}
}

// NewEvaluationProof creates a new EvaluationProof.
func NewEvaluationProof(params Parameters) EvaluationProof {
	mask := make([]ring.Poly, params.polyCommitSize)
	for i := 0; i < params.polyCommitSize; i++ {
		mask[i] = params.ringQ.NewPoly()
	}

	rand := make([]ring.Poly, params.ajtaiRandSize)
	for i := 0; i < params.ajtaiRandSize; i++ {
		rand[i] = params.ringQ.NewPoly()
	}

	return EvaluationProof{
		Value: big.NewInt(0),
		Mask:  mask,
		Rand:  rand,
	}
}
