package celpc

import "github.com/tuneinsight/lattigo/v6/ring"

// AjtaiCommitKey is a public CRS for Ajtai Commitment.
type AjtaiCommitKey struct {
	// A0 has dimension AjtaiSize * PolyCommitSize.
	A0 [][]ring.Poly
	// A1 has dimension AjtaiSize * (AjtaiRandSize - AjtaiSize).
	A1 [][]ring.Poly
}

// GenAjtaiCommitKey generates a new AjtaiCommitKey.
func GenAjtaiCommitKey(params Parameters) AjtaiCommitKey {
	us := NewStreamSampler(params)

	A0 := make([][]ring.Poly, params.ajtaiSize)
	for i := 0; i < params.ajtaiSize; i++ {
		A0[i] = make([]ring.Poly, params.polyCommitSize)
		for j := 0; j < params.polyCommitSize; j++ {
			A0[i][j] = params.ringQ.NewPoly()
			us.SamplePolyAssign(A0[i][j])
		}
	}

	A1 := make([][]ring.Poly, params.ajtaiSize)
	for i := 0; i < params.ajtaiSize; i++ {
		A1[i] = make([]ring.Poly, params.ajtaiRandSize-params.ajtaiSize)
		for j := 0; j < params.ajtaiRandSize-params.ajtaiSize; j++ {
			A1[i][j] = params.ringQ.NewPoly()
			us.SamplePolyAssign(A1[i][j])
		}
	}

	return AjtaiCommitKey{
		A0: A0,
		A1: A1,
	}
}

// AjtaiCommitment is a Ajtai AjtaiCommitment.
type AjtaiCommitment struct {
	// Value has length AjtaiSize.
	Value []ring.Poly
}

// NewAjtaiCommitment creates a new Commitment.
func NewAjtaiCommitment(params Parameters) AjtaiCommitment {
	com := make([]ring.Poly, params.ajtaiSize)
	for i := 0; i < params.ajtaiSize; i++ {
		com[i] = params.ringQ.NewPoly()
	}

	return AjtaiCommitment{
		Value: com,
	}
}

// Equals checks if two AjtaiCommitments are equal.
func (c AjtaiCommitment) Equals(other AjtaiCommitment) bool {
	if len(c.Value) != len(other.Value) {
		return false
	}

	for i := 0; i < len(c.Value); i++ {
		if !c.Value[i].Equal(&other.Value[i]) {
			return false
		}
	}

	return true
}

// CopyFrom copies the AjtaiCommitment.
func (c AjtaiCommitment) CopyFrom(other AjtaiCommitment) AjtaiCommitment {
	for i := 0; i < len(c.Value); i++ {
		c.Value[i].Copy(other.Value[i])
	}

	return c
}

// AjtaiCommiter commits an Ajtai Commitment.
type AjtaiCommiter struct {
	Parameters Parameters
	CommitKey  AjtaiCommitKey
}

// NewAjtaiCommiter creates a new AjtaiCommiter.
func NewAjtaiCommiter(params Parameters, commitKey AjtaiCommitKey) *AjtaiCommiter {
	return &AjtaiCommiter{
		Parameters: params,
		CommitKey:  commitKey,
	}
}

// Commit commits p using opening r.
// mNTT should have length PolyCommitSize.
// rNTT should have length AjtaiRansSize.
func (c *AjtaiCommiter) Commit(p, r []ring.Poly) AjtaiCommitment {
	comOut := NewAjtaiCommitment(c.Parameters)
	c.CommitAssign(p, r, comOut)
	return comOut
}

// Commit commits p using opening r and writes it to comOut.
// mNTT should have length PolyCommitSize.
// rNTT should have length AjtaiRansSize.
func (c *AjtaiCommiter) CommitAssign(p, r []ring.Poly, comOut AjtaiCommitment) {
	for i := 0; i < c.Parameters.ajtaiSize; i++ {
		c.Parameters.ringQ.MulCoeffsMontgomery(c.CommitKey.A0[i][0], p[0], comOut.Value[i])
		for j := 1; j < c.Parameters.polyCommitSize; j++ {
			c.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(c.CommitKey.A0[i][j], p[j], comOut.Value[i])
		}

		for j := 0; j < c.Parameters.ajtaiRandSize-c.Parameters.ajtaiSize; j++ {
			c.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(c.CommitKey.A1[i][j], r[j], comOut.Value[i])
		}
		c.Parameters.ringQ.Add(comOut.Value[i], r[c.Parameters.ajtaiRandSize-c.Parameters.ajtaiSize+i], comOut.Value[i])
	}
}
