package jindo

import (
	"crypto/sha3"
	"fmt"
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/bigpoly"
	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Prover is a Jindo prover.
type Prover[E bignum.Uint[E]] struct {
	params Parameters
	ecd    *Encoder[E]
	rnsOut *RNSReconstructor

	ck *CommitKey

	uniformSampler *csprng.UniformSampler
	roundedSampler *csprng.RoundedGaussianSampler
	mlweSampler    *csprng.TwinCDTGaussianSampler
}

// NewProver creates a new [Prover].
func NewProver[E bignum.Uint[E]](params Parameters, crs []byte) *Prover[E] {
	return &Prover[E]{
		params: params,
		ecd:    NewEncoder[E](params),
		rnsOut: NewRNSReconstructor(params.ringQOut),

		ck: NewCommitKey(params, crs),

		uniformSampler: csprng.NewUniformSampler(),
		roundedSampler: csprng.NewRoundedGaussianSampler(),
		mlweSampler:    csprng.NewTwinCDTGaussianSampler(params.mlweStdDev),
	}
}

// Commit commits v.
// Panics if len(v) > params.rank.
// Otherwise, it pads zero.
func (p *Prover[E]) Commit(v []E) (*Commitment, *Opening) {
	switch {
	case len(v) > p.params.rank:
		panic("len(v) > params.rank")
	}

	com := NewCommitment(p.params)
	open := NewOpening(p.params)

	firstRow, lastRow := p.genFirstLastRow(v)
	for i := range p.params.cols + 1 {
		p.commitColTo(i, open, v, firstRow, lastRow)
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

	if i == p.params.cols {
		var z E
		mask := make([]E, p.params.slots)
		for j := range mask {
			mask[j] = z.New().MustSetRandom()
		}
		p.ecd.RandEncodeTo(open.Encode[i][0], mask, p.params.maskBlindStdDev)

		for j := 1; j < p.params.rows-1; j++ {
			for k := range mask {
				mask[k].MustSetRandom()
			}
			p.ecd.RandEncodeTo(open.Encode[i][j], mask, p.params.maskStdDev)
		}

		for k := range mask {
			mask[k].MustSetRandom()
		}
		p.ecd.RandEncodeTo(open.Encode[i][p.params.rows-1], mask, p.params.maskStdDev)
	} else {
		p.ecd.RandEncodeTo(open.Encode[i][0], firstRow[rowStart:rowEnd], p.params.ecdBlindStdDev)

		for j := 1; j < p.params.rows-1; j++ {
			idxStart := (j * p.params.cols * p.params.slots) + rowStart
			idxEnd := (j * p.params.cols * p.params.slots) + rowEnd
			if idxStart > len(v) {
				break
			}
			p.ecd.RandEncodeTo(open.Encode[i][j], v[idxStart:min(idxEnd, len(v))], p.params.ecdStdDev)
		}

		p.ecd.RandEncodeTo(open.Encode[i][p.params.rows-1], lastRow[rowStart:rowEnd], p.params.ecdStdDev)
	}

	for j := range p.params.inMSISRank + p.params.mlweRank {
		if i == p.params.cols {
			for k := range p.params.ringQ.N() {
				setCoeffSigned(p.params.ringQ, open.MLWE[i][j], p.roundedSampler.Sample(0, p.params.maskMLWEStdDev), k)
			}
		} else {
			for k := range p.params.ringQ.N() {
				setCoeffSigned(p.params.ringQ, open.MLWE[i][j], p.mlweSampler.Sample(0), k)
			}
		}
		p.params.ringQ.MForm(open.MLWE[i][j], open.MLWE[i][j])
		p.params.ringQ.NTT(open.MLWE[i][j], open.MLWE[i][j])
	}

	com := make([]ring.Poly, p.params.inMSISRank)
	for j := range p.params.inMSISRank {
		com[j] = p.params.ringQ.NewPoly()
	}

	for j := range p.params.inMSISRank {
		for k := range p.params.rows {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.In[j][k], open.Encode[i][k], com[j])
		}
		for k := range p.params.mlweRank {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(p.ck.MLWE[j][k], open.MLWE[i][k], com[j])
		}
		p.params.ringQ.Add(open.MLWE[i][p.params.mlweRank+j], com[j], com[j])
	}

	inComBig := make([]*big.Int, p.params.ringQ.N())
	for j := range inComBig {
		inComBig[j] = new(big.Int)
	}

	for j := range p.params.inMSISRank {
		p.params.ringQ.IMForm(com[j], com[j])
		p.params.ringQ.INTT(com[j], com[j])

		p.ecd.rns.ReconstructTo(inComBig, com[j])
		for k := range p.params.ringQ.N() {
			inComBig[k].Rsh(inComBig[k], uint(p.params.logInCutOff))
		}
		p.rnsOut.SetBigCoeffTo(open.InCommit[i*p.params.inMSISRank+j], inComBig)

		p.params.ringQOut.MForm(open.InCommit[i*p.params.inMSISRank+j], open.InCommit[i*p.params.inMSISRank+j])
		p.params.ringQOut.NTT(open.InCommit[i*p.params.inMSISRank+j], open.InCommit[i*p.params.inMSISRank+j])
	}
}

// outerCommitTo computes the outer commitment.
func (p *Prover[E]) outerCommitTo(com *Commitment, open *Opening) {
	comBig := make([]*big.Int, p.params.ringQOut.N())
	for i := range comBig {
		comBig[i] = new(big.Int)
	}

	for i := range p.params.outMSISRank {
		for j := range p.params.inComDcmpLen {
			p.params.ringQOut.MulCoeffsMontgomeryThenAdd(p.ck.Out[i][j], open.InCommit[j], com.Value[i])
		}
		p.params.ringQOut.IMForm(com.Value[i], com.Value[i])
		p.params.ringQOut.INTT(com.Value[i], com.Value[i])

		p.rnsOut.ReconstructTo(comBig, com.Value[i])
		for k := range p.params.ringQOut.N() {
			comBig[k].Rsh(comBig[k], uint(p.params.logOutCutOff))
		}
		p.rnsOut.SetBigCoeffTo(com.Value[i], comBig)

		p.params.ringQOut.MForm(com.Value[i], com.Value[i])
		p.params.ringQOut.NTT(com.Value[i], com.Value[i])
	}
}

// Evaluate batch evaluates v at x using batch randomness batch and returns the result with proof.
func (p *Prover[E]) Evaluate(x E, v [][]E, com []*Commitment, open []*Opening) ([]E, *Proof) {
	switch {
	case len(v) != len(com) || len(v) != len(open):
		panic("len(v), len(com), len(open) are not equal")
	case len(v) != p.params.batch:
		panic("len(v) != params.batch")
	}

	for i := range p.params.batch {
		switch {
		case len(v[i]) > p.params.rank:
			panic(fmt.Sprintf("len(v[%v]) > params.rank", i))
		}
	}

	oracle := sha3.NewSHAKE128()
	p.ck.WriteRawTo(oracle)
	for i := range p.params.batch {
		com[i].WriteRawTo(oracle)
	}
	oracle.Write(x.Marshal())

	var batchOut, batch []ring.Poly

	var openBatch *Opening
	if p.params.batch > 1 {
		batch = make([]ring.Poly, p.params.batch)
		batchOut = make([]ring.Poly, p.params.batch)
		batchBytes := make([]byte, p.params.batch*16)
		for i := range p.params.batch {
			oracle.Read(batchBytes[i*16 : (i+1)*16])
			batch[i] = p.params.ringQ.NewPoly()
			encodeChallengeTo(p.params, p.params.ringQ, batch[i], batchBytes[i*16:(i+1)*16])
			batchOut[i] = p.params.ringQOut.NewPoly()
			encodeChallengeTo(p.params, p.params.ringQOut, batchOut[i], batchBytes[i*16:(i+1)*16])
		}
		oracle.Reset()

		p.ck.WriteRawTo(oracle)
		for i := range p.params.batch {
			com[i].WriteRawTo(oracle)
		}
		oracle.Write(x.Marshal())
		oracle.Write(batchBytes)

		openBatch = NewOpening(p.params)
		for i := range p.params.batch {
			for j := range open[i].InCommit {
				p.params.ringQOut.MulCoeffsMontgomeryThenAdd(open[i].InCommit[j], batchOut[i], openBatch.InCommit[j])
			}
			for j := range open[i].Encode {
				for k := range open[i].Encode[j] {
					p.params.ringQ.MulCoeffsMontgomeryThenAdd(open[i].Encode[j][k], batch[i], openBatch.Encode[j][k])
				}
			}
			for j := range open[i].MLWE {
				for k := range open[i].MLWE[j] {
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

	leftE := leftVec(p.params, x)
	left := make([]ring.Poly, p.params.rows)
	for i := range left {
		left[i] = p.ecd.Encode([]E{leftE[i]})
	}

	for i := range p.params.cols {
		for j := range p.params.rows {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(left[j], openBatch.Encode[i][j], pf.Partial[i])
		}
	}

	for j := range p.params.rows {
		p.params.ringQ.MulCoeffsMontgomeryThenAdd(left[j], openBatch.Encode[p.params.cols][j], pf.PartialMask)
	}

	for i := range pf.InCommit {
		pf.InCommit[i].WriteTo(oracle)
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
		encodeChallengeTo(p.params, p.params.ringQ, chals[i], chalBytes)
	}

	for i := range p.params.rows {
		pf.Encode[i].Copy(openBatch.Encode[p.params.cols][i])
		for j := range p.params.cols {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(chals[j], openBatch.Encode[j][i], pf.Encode[i])
		}
	}

	for i := range p.params.mlweRank + p.params.inMSISRank {
		pf.MLWE[i].Copy(openBatch.MLWE[p.params.cols][i])
		for j := range p.params.cols {
			p.params.ringQ.MulCoeffsMontgomeryThenAdd(chals[j], openBatch.MLWE[j][i], pf.MLWE[i])
		}
	}

	evals := make([]E, p.params.batch)
	for i := 0; i < p.params.batch; i++ {
		evals[i] = (&bigpoly.Poly[E]{Coeffs: v[i]}).Evaluate(x)
	}

	return evals, pf
}

// SafeCopy returns a thread-safe copy.
func (p *Prover[E]) SafeCopy() *Prover[E] {
	return &Prover[E]{
		params: p.params,
		ecd:    p.ecd.SafeCopy(),
		rnsOut: p.rnsOut.SafeCopy(),

		ck: p.ck,

		uniformSampler: csprng.NewUniformSampler(),
		roundedSampler: csprng.NewRoundedGaussianSampler(),
		mlweSampler:    csprng.NewTwinCDTGaussianSampler(p.params.mlweStdDev),
	}
}
