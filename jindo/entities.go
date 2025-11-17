package jindo

import (
	"io"

	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// CommitKey is the key for commitment.
// Must be initialized with CRS.
type CommitKey struct {
	crs []byte

	In   [][]ring.Poly
	MLWE [][]ring.Poly
	Out  [][]ring.Poly
}

// NewCommitKey creates a new [CommitKey].
func NewCommitKey(params Parameters, crs []byte) *CommitKey {
	u := csprng.NewUniformSamplerWithSeed(crs)

	in := make([][]ring.Poly, params.inMSISRank)
	for i := range in {
		in[i] = make([]ring.Poly, params.rows)
		for j := range in[i] {
			in[i][j] = params.ringQ.NewPoly()
			for k := 0; k < params.ringQ.N(); k++ {
				for l := 0; l < params.ringQ.ModuliChainLength(); l++ {
					in[i][j].Coeffs[l][k] = u.SampleN(params.ringQ.SubRings[l].Modulus)
				}
			}
		}
	}

	mlwe := make([][]ring.Poly, params.inMSISRank)
	for i := range mlwe {
		mlwe[i] = make([]ring.Poly, params.mlweRank)
		for j := range mlwe[i] {
			mlwe[i][j] = params.ringQ.NewPoly()
			for k := 0; k < params.ringQ.N(); k++ {
				for l := 0; l < params.ringQ.ModuliChainLength(); l++ {
					mlwe[i][j].Coeffs[l][k] = u.SampleN(params.ringQ.SubRings[l].Modulus)
				}
			}
		}
	}

	out := make([][]ring.Poly, params.outMSISRank)
	for i := range out {
		out[i] = make([]ring.Poly, params.inComDcmpLen)
		for j := range out[i] {
			out[i][j] = params.ringQ.NewPoly()
			for k := 0; k < params.ringQ.N(); k++ {
				for l := 0; l < params.ringQ.ModuliChainLength(); l++ {
					out[i][j].Coeffs[l][k] = u.SampleN(params.ringQ.SubRings[l].Modulus)
				}
			}
		}
	}

	crsCopy := make([]byte, len(crs))
	copy(crsCopy, crs)

	return &CommitKey{
		crs: crsCopy,

		In:   in,
		MLWE: mlwe,
		Out:  out,
	}
}

func (ck *CommitKey) WriteRawTo(w io.Writer) {
	w.Write(ck.crs)
}

// Commitment is a commitment of a polynomial.
type Commitment struct {
	Value []ring.Poly
}

// NewCommitment creates a new [Commitment].
func NewCommitment(params Parameters) *Commitment {
	com := make([]ring.Poly, params.outMSISRank)
	for i := range com {
		com[i] = params.ringQ.NewPoly()
	}

	return &Commitment{
		Value: com,
	}
}

func (com *Commitment) WriteRawTo(w io.Writer) {
	for i := range com.Value {
		com.Value[i].WriteTo(w)
	}
}

// Opening is an opening of a commitment.
type Opening struct {
	InCommit []ring.Poly
	Encode   [][]ring.Poly
	MLWE     [][]ring.Poly
}

// NewOpening creates a new [Opening].
func NewOpening(params Parameters) *Opening {
	inDcmp := make([]ring.Poly, params.inComDcmpLen)
	for i := range inDcmp {
		inDcmp[i] = params.ringQ.NewPoly()
	}

	ecd := make([][]ring.Poly, params.cols)
	for i := range ecd {
		ecd[i] = make([]ring.Poly, params.rows)
		for j := range ecd[i] {
			ecd[i][j] = params.ringQ.NewPoly()
		}
	}

	mlwe := make([][]ring.Poly, params.cols)
	for i := range mlwe {
		mlwe[i] = make([]ring.Poly, params.mlweRank+params.inMSISRank)
		for j := range mlwe[i] {
			mlwe[i][j] = params.ringQ.NewPoly()
		}
	}

	return &Opening{
		InCommit: inDcmp,
		Encode:   ecd,
		MLWE:     mlwe,
	}
}

// Proof is a proof of evaluation.
type Proof struct {
	Commit      []ring.Poly
	Partial     []ring.Poly
	PartialMask ring.Poly

	Encode   []ring.Poly
	MLWE     []ring.Poly
	InCommit []ring.Poly
}

// NewProof creates a new [Proof].
func NewProof(params Parameters) *Proof {
	com := make([]ring.Poly, params.inMSISRank)
	for i := 0; i < params.inMSISRank; i++ {
		com[i] = params.ringQ.NewPoly()
	}

	resEcd := make([]ring.Poly, params.rows)
	for i := 0; i < params.rows; i++ {
		resEcd[i] = params.ringQ.NewPoly()
	}

	resMLWE := make([]ring.Poly, params.mlweRank+params.inMSISRank)
	for i := 0; i < params.mlweRank+params.inMSISRank; i++ {
		resMLWE[i] = params.ringQ.NewPoly()
	}

	partial := make([]ring.Poly, params.cols)
	for i := 0; i < params.cols; i++ {
		partial[i] = params.ringQ.NewPoly()
	}

	inCom := make([]ring.Poly, params.inComDcmpLen)
	for i := 0; i < params.inComDcmpLen; i++ {
		inCom[i] = params.ringQ.NewPoly()
	}

	return &Proof{
		Commit:      com,
		Partial:     partial,
		PartialMask: params.ringQ.NewPoly(),

		Encode:   resEcd,
		MLWE:     resMLWE,
		InCommit: inCom,
	}
}
