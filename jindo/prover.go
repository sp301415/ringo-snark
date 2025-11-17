package jindo

import (
	"crypto/sha3"

	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Prover is a Jindo prover.
type Prover[E num.Uint[E]] struct {
	params Parameters
	ecd    *Encoder[E]

	ck *CommitKey

	uniformSampler *csprng.UniformSampler
	roundedSampler *csprng.RoundedGaussianSampler
	mlweSampler    *csprng.TwinCDTGaussianSampler
}

// NewProver creates a new [Prover].
func NewProver[E num.Uint[E]](params Parameters, crs []byte) *Prover[E] {
	return &Prover[E]{
		params: params,
		ecd:    NewEncoder[E](params),

		ck: NewCommitKey(params, crs),

		uniformSampler: csprng.NewUniformSampler(),
		roundedSampler: csprng.NewRoundedGaussianSampler(),
		mlweSampler:    csprng.NewTwinCDTGaussianSampler(params.mlweStdDev),
	}
}

// Commit commits v.
// Panics if len(v) > params.rank.
// Otherwise, it pads zero.
func (p *Prover[E]) Commit(v *bigpoly.Poly[E]) (*Commitment, *Opening) {
	if v.Rank() > p.params.rank {
		panic("Commit: len(v) > params.rank")
	}

	com := NewCommitment(p.params)
	open := NewOpening(p.params)

	firstRow, lastRow := p.genFirstLastRow(v.Coeffs)
	for i := range p.params.cols {
		p.commitColTo(i, open, v.Coeffs, firstRow, lastRow)
	}

	p.outerCommitTo(com, open)

	return com, open
}

// genFirstLastRow generates the first and last row for committing v.
func (p *Prover[E]) genFirstLastRow(v []E) (firstRow, lastRow []E) {
	var z E

	lastRow = make([]E, p.params.cols*p.params.slots)
	for i := 0; i < p.params.cols*p.params.slots-1; i++ {
		lastRow[i] = z.New().MustSetRandom()
	}
	lastRow[p.params.cols*p.params.slots-1] = z.New()

	firstRow = make([]E, p.params.cols*p.params.slots)
	firstRow[0] = z.New().Set(v[0])
	for i := 1; i < p.params.cols*p.params.slots; i++ {
		firstRow[i] = z.New()
		if i < len(v) {
			firstRow[i].Sub(v[i], lastRow[i-1])
		} else {
			firstRow[i].Sub(firstRow[i], lastRow[i-1])
		}
	}

	return firstRow, lastRow
}

// commitColTo commits the i-th column.
func (p *Prover[E]) commitColTo(i int, open *Opening, v []E, firstRow, lastRow []E) {
	rowStart := i * p.params.slots
	rowEnd := (i + 1) * p.params.slots

	p.ecd.EncodeTo(open.Encode[i][0], firstRow[rowStart:rowEnd])

	for j := 1; j < p.params.rows-1; j++ {
		idxStart := (j * p.params.cols * p.params.slots) + rowStart
		idxEnd := (j * p.params.cols * p.params.slots) + rowEnd
		p.ecd.EncodeTo(open.Encode[i][j], v[min(idxStart, len(v)):min(idxEnd, len(v))])
	}

	p.ecd.EncodeTo(open.Encode[i][p.params.rows-1], lastRow[rowStart:rowEnd])

	for j := 0; j < p.params.inMSISRank+p.params.mlweRank; j++ {
		for k := 0; k < p.params.ringQ.N(); k++ {
			setCoeffSigned(p.params.ringQ, open.MLWE[i][j], p.mlweSampler.Sample(0), k)
		}
		p.params.ringQ.MForm(open.MLWE[i][j], open.MLWE[i][j])
		p.params.ringQ.NTT(open.MLWE[i][j], open.MLWE[i][j])
	}

	com := make([]ring.Poly, p.params.inMSISRank)
	for j := 0; j < p.params.inMSISRank; j++ {
		com[j] = p.params.ringQ.NewPoly()
	}

	for j := 0; j < p.params.inMSISRank; j++ {
		for k := 0; k < p.params.rows; k++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.In[j][k], open.Encode[i][k], com[j])
		}
		for k := 0; k < p.params.mlweRank; k++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.MLWE[j][k], open.MLWE[i][k], com[j])
		}
		p.params.ringQ.Add(open.MLWE[i][p.params.mlweRank+j], com[j], com[j])
	}

	inDcmpStart := i * p.params.inMSISRank * p.params.ringQ.ModuliChainLength()
	// inDcmpEnd := (i + 1) * p.params.inMSISRank * p.params.ringQ.ModuliChainLength()
	comInvNTT := p.params.ringQ.NewPoly()
	for j := 0; j < p.params.inMSISRank; j++ {
		p.params.ringQ.INTT(com[j], comInvNTT)
		p.params.ringQ.IMForm(comInvNTT, comInvNTT)
		for k := 0; k < p.params.ringQ.ModuliChainLength(); k++ {
			idx := j*p.params.ringQ.ModuliChainLength() + k
			for l := 0; l < p.params.ringQ.ModuliChainLength(); l++ {
				if l == k {
					copy(open.InCommit[inDcmpStart+idx].Coeffs[l], com[j].Coeffs[l])
				} else {
					copy(open.InCommit[inDcmpStart+idx].Coeffs[l], comInvNTT.Coeffs[k])
					p.params.ringQ.SubRings[l].MForm(open.InCommit[inDcmpStart+idx].Coeffs[l], open.InCommit[inDcmpStart+idx].Coeffs[l])
					p.params.ringQ.SubRings[l].NTT(open.InCommit[inDcmpStart+idx].Coeffs[l], open.InCommit[inDcmpStart+idx].Coeffs[l])
				}
			}
		}
	}
}

// outerCommitTo computes the outer commitment.
func (p *Prover[E]) outerCommitTo(com *Commitment, open *Opening) {
	for i := 0; i < p.params.outMSISRank; i++ {
		for j := 0; j < p.params.inComDcmpLen; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.Out[i][j], open.InCommit[j], com.Value[i])
		}
	}
}

// Evaluate batch evaluates v at x using batch randomness batch and returns the result with proof.
func (p *Prover[E]) Evaluate(x E, batch []ring.Poly, v []*bigpoly.Poly[E], com []*Commitment, open []*Opening) ([]E, *Proof) {
	switch {
	case len(v) != len(com) || len(v) != len(open):
		panic("EvaluateBatch: len(v), len(com), len(open) are not equal")
	case len(v) != p.params.batch:
		panic("EvaluateBatch: len(v) != params.batch")
	}

	var openBatch *Opening
	if p.params.batch > 1 {
		openBatch = NewOpening(p.params)
		for i := 0; i < p.params.batch; i++ {
			for j := range openBatch.InCommit {
				p.params.ringQ.MulCoeffsMontgomeryThenAdd(open[i].InCommit[j], batch[i], openBatch.InCommit[j])
			}
			for j := range openBatch.Encode {
				for k := range openBatch.Encode[j] {
					p.params.ringQ.MulCoeffsMontgomeryThenAdd(open[i].Encode[j][k], batch[i], openBatch.Encode[j][k])
				}
			}
			for j := range openBatch.MLWE {
				for k := range openBatch.MLWE[j] {
					p.params.ringQ.MulCoeffsMontgomeryThenAdd(open[i].MLWE[j][k], batch[i], openBatch.MLWE[j][k])
				}
			}
		}
	} else {
		openBatch = open[0]
	}

	pf := NewProof(p.params)
	for i := range openBatch.InCommit {
		pf.InCommit[i].Copy(openBatch.InCommit[i])
	}

	oracle := sha3.NewSHAKE128()
	p.ck.WriteRawTo(oracle)
	for i := 0; i < p.params.batch; i++ {
		com[i].WriteRawTo(oracle)
	}
	oracle.Write(x.Marshal())

	leftE := leftVec(p.params, x)
	left := make([]ring.Poly, p.params.rows)
	for i := range left {
		left[i] = p.ecd.Encode([]E{leftE[i]})
	}

	maskEcd, maskMLWE := p.firstMoveTo(pf, left, batch, openBatch)

	for i := range pf.Commit {
		pf.Commit[i].WriteTo(oracle)
	}
	for i := range pf.Partial {
		pf.Partial[i].WriteTo(oracle)
	}
	pf.PartialMask.WriteTo(oracle)

	chals := make([]ring.Poly, p.params.cols)
	chalBytes := make([]byte, 16)
	for i := 0; i < p.params.cols; i++ {
		chals[i] = p.params.ringQ.NewPoly()
		oracle.Read(chalBytes)
		EncodeChallengeTo(p.params, chals[i], chalBytes)
	}

	p.lastMoveTo(pf, maskEcd, maskMLWE, chals, openBatch)

	evals := make([]E, p.params.batch)
	for i := 0; i < p.params.batch; i++ {
		evals[i] = v[i].Evaluate(x)
	}

	return evals, pf
}

// firstMoveTo computes the first move of proving.
func (p *Prover[E]) firstMoveTo(pf *Proof, left []ring.Poly, batch []ring.Poly, open *Opening) (maskEcd, maskMLWE []ring.Poly) {
	maskEcd = make([]ring.Poly, p.params.rows)
	for i := range maskEcd {
		maskEcd[i] = p.params.ringQ.NewPoly()
	}
	maskMLWE = make([]ring.Poly, p.params.mlweRank+p.params.inMSISRank)
	for i := range maskMLWE {
		maskMLWE[i] = p.params.ringQ.NewPoly()
	}
	pSingle := p.params.ringQ.NewPoly()

	for i := 0; i < p.params.batch; i++ {
		for j := 0; j < p.params.rows; j++ {
			for k := 0; k < p.params.ringQ.N(); k++ {
				var c int64
				if j == 0 {
					c = p.roundedSampler.Sample(0, float64(p.params.ecd.base+1)*p.params.maskBlindStdDev)
				} else {
					c = p.roundedSampler.Sample(0, float64(p.params.ecd.base+1)*p.params.maskStdDev)
				}
				setCoeffSigned(p.params.ringQ, pSingle, c, k)
			}
			p.params.ringQ.MForm(pSingle, pSingle)
			p.params.ringQ.NTT(pSingle, pSingle)
			if p.params.batch > 1 {
				p.params.ringQ.MulCoeffsMontgomeryThenAdd(pSingle, batch[i], maskEcd[j])
			} else {
				maskEcd[j].Copy(pSingle)
			}
		}

		for j := 0; j < p.params.mlweRank+p.params.inMSISRank; j++ {
			for k := 0; k < p.params.ringQ.N(); k++ {
				setCoeffSigned(p.params.ringQ, pSingle, p.roundedSampler.Sample(0, p.params.maskMLWEStdDev), k)
			}
			p.params.ringQ.MForm(pSingle, pSingle)
			p.params.ringQ.NTT(pSingle, pSingle)
			if p.params.batch > 1 {
				p.params.ringQ.MulCoeffsMontgomeryThenAdd(pSingle, batch[i], maskMLWE[j])
			} else {
				maskMLWE[j].Copy(pSingle)
			}
		}
	}

	for i := 0; i < p.params.inMSISRank; i++ {
		pf.Commit[i].Zero()
		for j := 0; j < p.params.rows; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.In[i][j], maskEcd[j], pf.Commit[i])
		}
		for j := 0; j < p.params.mlweRank; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.MLWE[i][j], maskMLWE[j], pf.Commit[i])
		}
		p.params.ringQ.Add(maskMLWE[p.params.mlweRank+i], pf.Commit[i], pf.Commit[i])
	}

	for i := 0; i < p.params.cols; i++ {
		pf.Partial[i].Zero()
		for j := 0; j < p.params.rows; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(left[j], open.Encode[i][j], pf.Partial[i])
		}
	}

	pf.PartialMask.Zero()
	for i := 0; i < p.params.rows; i++ {
		p.params.ringQ.MulCoeffsMontgomeryThenAdd(left[i], maskEcd[i], pf.PartialMask)
	}

	return
}

// lastMoveTo computes the last move of proving.
func (p *Prover[E]) lastMoveTo(pf *Proof, maskEcd, maskMLWE, chals []ring.Poly, open *Opening) {
	for i := 0; i < p.params.rows; i++ {
		pf.Encode[i].Copy(maskEcd[i])
		for j := 0; j < p.params.cols; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(chals[j], open.Encode[j][i], pf.Encode[i])
		}
	}

	for i := 0; i < p.params.mlweRank+p.params.inMSISRank; i++ {
		pf.MLWE[i].Copy(maskMLWE[i])
		for j := 0; j < p.params.cols; j++ {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(chals[j], open.MLWE[j][i], pf.MLWE[i])
		}
	}
}

// SafeCopy returns a thread-safe copy.
func (p *Prover[E]) SafeCopy() *Prover[E] {
	return &Prover[E]{
		params: p.params,
		ecd:    p.ecd.SafeCopy(),

		ck: p.ck,

		uniformSampler: csprng.NewUniformSampler(),
		roundedSampler: csprng.NewRoundedGaussianSampler(),
		mlweSampler:    csprng.NewTwinCDTGaussianSampler(p.params.mlweStdDev),
	}
}
