package jindo

import (
	"bytes"
	"io"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/csprng"
)

// CommitKey is the key for commitment.
// Must be initialized with CRS.
type CommitKey struct {
	crs []byte

	In   [][]*crt.Element
	MLWE [][]*crt.Element
	Out  [][]*crt.Element

	InS   [][]*crt.ShoupElement
	MLWES [][]*crt.ShoupElement
	OutS  [][]*crt.ShoupElement
}

// NewCommitKey creates a new [CommitKey].
func NewCommitKey[E bignum.Uint[E]](params Parameters[E], crs []byte) *CommitKey {
	u := csprng.NewUniformSamplerWithSeed(crs)

	in := make([][]*crt.Element, params.inMSISRank)
	inS := make([][]*crt.ShoupElement, params.inMSISRank)
	for i := range in {
		in[i] = make([]*crt.Element, params.rows+1)
		inS[i] = make([]*crt.ShoupElement, params.rows+1)
		for j := range in[i] {
			in[i][j] = params.op.NewNTTPoly()
			for k := range params.op.Rank() {
				for l, ql := range params.op.Modulus() {
					in[i][j].Coeffs[l][k] = u.SampleN(ql.Value())
				}
			}
			inS[i][j] = crt.GenShoupElement(in[i][j], params.op.Modulus())
		}
	}

	mlwe := make([][]*crt.Element, params.inMSISRank)
	mlweS := make([][]*crt.ShoupElement, params.inMSISRank)
	for i := range mlwe {
		mlwe[i] = make([]*crt.Element, params.mlweRank)
		mlweS[i] = make([]*crt.ShoupElement, params.mlweRank)
		for j := range mlwe[i] {
			mlwe[i][j] = params.op.NewNTTPoly()
			for k := range params.op.Rank() {
				for l, ql := range params.op.Modulus() {
					mlwe[i][j].Coeffs[l][k] = u.SampleN(ql.Value())
				}
			}
			mlweS[i][j] = crt.GenShoupElement(mlwe[i][j], params.op.Modulus())
		}
	}

	out := make([][]*crt.Element, params.outMSISRank)
	outS := make([][]*crt.ShoupElement, params.outMSISRank)
	for i := range out {
		out[i] = make([]*crt.Element, params.cols*params.inMSISRank)
		outS[i] = make([]*crt.ShoupElement, params.cols*params.inMSISRank)
		for j := range out[i] {
			out[i][j] = params.opOut.NewNTTPoly()
			for k := range params.opOut.Rank() {
				for l, ql := range params.opOut.Modulus() {
					out[i][j].Coeffs[l][k] = u.SampleN(ql.Value())
				}
			}
			outS[i][j] = crt.GenShoupElement(out[i][j], params.opOut.Modulus())
		}
	}

	crsCopy := make([]byte, len(crs))
	copy(crsCopy, crs)

	return &CommitKey{
		crs: crsCopy,

		In:   in,
		MLWE: mlwe,
		Out:  out,

		InS:   inS,
		MLWES: mlweS,
		OutS:  outS,
	}
}

func (ck *CommitKey) WriteRawTo(w io.Writer) {
	w.Write(ck.crs)
}

// Commitment is a commitment of a polynomial.
type Commitment struct {
	Value [][]*crt.Element
}

// NewCommitment creates a new [Commitment].
func NewCommitment[E bignum.Uint[E]](params Parameters[E]) *Commitment {
	com := make([][]*crt.Element, params.split)
	for i := range com {
		com[i] = make([]*crt.Element, params.outMSISRank)
		for j := range com[i] {
			com[i][j] = params.opOut.NewNTTPoly()
		}
	}

	return &Commitment{
		Value: com,
	}
}

// WriteToBuf writes the value to [bytes.Buffer].
func (com *Commitment) WriteToBuf(buf *bytes.Buffer) {
	for i := range com.Value {
		for j := range com.Value[i] {
			com.Value[i][j].WriteToBuf(buf)
		}
	}
}

// Opening is an opening of a commitment.
type Opening[E bignum.Uint[E]] struct {
	InCommit [][]*crt.Element
	Blinder  [][]E
	Encode   [][][]*crt.Element
	MLWE     [][][]*crt.Element
}

// NewOpening creates a new [Opening].
func NewOpening[E bignum.Uint[E]](params Parameters[E]) *Opening[E] {
	inCom := make([][]*crt.Element, params.split)
	for i := range inCom {
		inCom[i] = make([]*crt.Element, params.cols*params.inMSISRank)
		for j := range inCom[i] {
			inCom[i][j] = params.opOut.NewNTTPoly()
		}
	}

	blinder := make([][]E, params.split)
	for i := range blinder {
		blinder[i] = make([]E, params.cols*params.slots)
		for j := range blinder[i] {
			blinder[i][j] = blinder[i][j].New()
		}
	}

	ecd := make([][][]*crt.Element, params.split)
	for i := range ecd {
		ecd[i] = make([][]*crt.Element, params.cols)
		for j := range ecd[i] {
			ecd[i][j] = make([]*crt.Element, params.rows+1)
			for k := range ecd[i][j] {
				ecd[i][j][k] = params.op.NewNTTPoly()
			}
		}
	}

	mlwe := make([][][]*crt.Element, params.split)
	for i := range mlwe {
		mlwe[i] = make([][]*crt.Element, params.cols)
		for j := range mlwe[i] {
			mlwe[i][j] = make([]*crt.Element, params.mlweRank+params.inMSISRank)
			for k := range mlwe[i][j] {
				mlwe[i][j][k] = params.op.NewNTTPoly()
			}
		}
	}

	return &Opening[E]{
		InCommit: inCom,
		Blinder:  blinder,
		Encode:   ecd,
		MLWE:     mlwe,
	}
}

// Proof is a proof of evaluation.
type Proof[E bignum.Uint[E]] struct {
	MaskCom       []*crt.Element
	MaskSplitEval []E

	Partial []*crt.Element

	Encode   []*crt.Element
	MLWE     []*crt.Element
	InCommit []*crt.Element

	BlindEvals []E
	SplitEvals [][][]E
}

// NewProof creates a new [Proof].
func NewProof[E bignum.Uint[E]](params Parameters[E]) *Proof[E] {
	maskCom := make([]*crt.Element, params.outMSISRank)
	for i := range maskCom {
		maskCom[i] = params.opOut.NewNTTPoly()
	}

	maskSplitEval := make([]E, params.slots)
	for i := range maskSplitEval {
		maskSplitEval[i] = maskSplitEval[i].New()
	}

	resEcd := make([]*crt.Element, params.rows+1)
	for i := range resEcd {
		resEcd[i] = params.op.NewNTTPoly()
	}

	resMLWE := make([]*crt.Element, params.mlweRank+params.inMSISRank)
	for i := range resMLWE {
		resMLWE[i] = params.op.NewNTTPoly()
	}

	partial := make([]*crt.Element, params.cols)
	for i := range partial {
		partial[i] = params.op.NewNTTPoly()
	}

	inCom := make([]*crt.Element, params.cols*params.inMSISRank)
	for i := range inCom {
		inCom[i] = params.opOut.NewNTTPoly()
	}

	blindEvals := make([]E, params.batch)
	for i := range blindEvals {
		blindEvals[i] = blindEvals[i].New()
	}

	splitEvals := make([][][]E, params.batch)
	for i := range splitEvals {
		splitEvals[i] = make([][]E, params.split)
		for j := range splitEvals[i] {
			splitEvals[i][j] = make([]E, params.slots)
			for k := range splitEvals[i][j] {
				splitEvals[i][j][k] = splitEvals[i][j][k].New()
			}
		}
	}

	return &Proof[E]{
		MaskCom:       maskCom,
		MaskSplitEval: maskSplitEval,

		Partial: partial,

		Encode:   resEcd,
		MLWE:     resMLWE,
		InCommit: inCom,

		BlindEvals: blindEvals,
		SplitEvals: splitEvals,
	}
}
