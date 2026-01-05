package jindo

import (
	"crypto/sha3"
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Verifier is a Jindo verifier.
type Verifier[E bignum.Uint[E]] struct {
	params     Parameters
	ecd        *Encoder[E]
	rnsOut     *RNSReconstructor
	embQOutToQ *ring.BasisExtender

	inCutOff  ring.RNSScalar
	outCutOff ring.RNSScalar

	ck *CommitKey
}

// NewVerifier creates a new [Verifier].
func NewVerifier[E bignum.Uint[E]](params Parameters, crs []byte) *Verifier[E] {
	inCutOff := big.NewInt(1)
	inCutOff.Lsh(inCutOff, uint(params.logInCutOff))
	inCutOffRNS := params.ringQ.NewRNSScalarFromBigint(inCutOff)
	params.ringQ.MFormRNSScalar(inCutOffRNS, inCutOffRNS)

	outCutOff := big.NewInt(1)
	outCutOff.Lsh(outCutOff, uint(params.logOutCutOff))
	outCutOffRNS := params.ringQOut.NewRNSScalarFromBigint(outCutOff)
	params.ringQOut.MFormRNSScalar(outCutOffRNS, outCutOffRNS)

	return &Verifier[E]{
		params:     params,
		ecd:        NewEncoder[E](params),
		rnsOut:     NewRNSReconstructor(params.ringQOut),
		embQOutToQ: ring.NewBasisExtender(params.ringQOut, params.ringQ),

		inCutOff:  inCutOffRNS,
		outCutOff: outCutOffRNS,

		ck: NewCommitKey(params, crs),
	}
}

// Verify verfies the polynomial commitment.
func (v *Verifier[E]) Verify(x E, com []*Commitment, y []E, pf *Proof) bool {
	switch {
	case len(com) != v.params.batch || len(y) != v.params.batch:
		panic("len(v) != params.batch")
	}

	oracle := sha3.NewSHAKE128()
	v.ck.WriteRawTo(oracle)
	for i := 0; i < v.params.batch; i++ {
		com[i].WriteRawTo(oracle)
	}
	oracle.Write(x.Marshal())

	var batch, batchOut []ring.Poly
	if v.params.batch > 1 {
		batch = make([]ring.Poly, v.params.batch)
		batchOut = make([]ring.Poly, v.params.batch)
		batchBytes := make([]byte, v.params.batch*16)
		for i := 0; i < v.params.batch; i++ {
			oracle.Read(batchBytes[i*16 : (i+1)*16])
			batch[i] = v.params.ringQ.NewPoly()
			encodeChallengeTo(v.params, v.params.ringQ, batch[i], batchBytes[i*16:(i+1)*16])
			batchOut[i] = v.params.ringQOut.NewPoly()
			encodeChallengeTo(v.params, v.params.ringQOut, batchOut[i], batchBytes[i*16:(i+1)*16])
		}
		oracle.Reset()

		v.ck.WriteRawTo(oracle)
		for i := 0; i < v.params.batch; i++ {
			com[i].WriteRawTo(oracle)
		}
		oracle.Write(x.Marshal())
		oracle.Write(batchBytes)
	}

	for i := range pf.Commit {
		pf.Commit[i].WriteTo(oracle)
	}
	for i := range pf.Partial {
		pf.Partial[i].WriteTo(oracle)
	}
	pf.PartialMask.WriteTo(oracle)

	chals := make([]ring.Poly, v.params.cols)
	chalBytes := make([]byte, 16)
	for i := 0; i < v.params.cols; i++ {
		chals[i] = v.params.ringQ.NewPoly()
		oracle.Read(chalBytes)
		encodeChallengeTo(v.params, v.params.ringQ, chals[i], chalBytes)
	}

	pfInv := NewProof(v.params)
	for i := range pf.Partial {
		v.params.ringQ.IMForm(pf.Partial[i], pfInv.Partial[i])
		v.params.ringQ.INTT(pfInv.Partial[i], pfInv.Partial[i])
	}
	for i := range pf.Encode {
		v.params.ringQ.IMForm(pf.Encode[i], pfInv.Encode[i])
		v.params.ringQ.INTT(pfInv.Encode[i], pfInv.Encode[i])
	}
	for i := range pf.MLWE {
		v.params.ringQ.IMForm(pf.MLWE[i], pfInv.MLWE[i])
		v.params.ringQ.INTT(pfInv.MLWE[i], pfInv.MLWE[i])
	}
	for i := range pf.InCommit {
		v.params.ringQOut.IMForm(pf.InCommit[i], pfInv.InCommit[i])
		v.params.ringQOut.INTT(pfInv.InCommit[i], pfInv.InCommit[i])
	}

	if !v.verifyOuterCommitment(batchOut, com, pf, pfInv) {
		return false
	}

	if !v.verifyInnerCommitment(chals, pf, pfInv) {
		return false
	}

	if !v.verifyConsistency(x, chals, pf) {
		return false
	}

	if !v.verifyEval(x, batch, y, pf, pfInv) {
		return false
	}

	return true
}

// verifyOuterCommitment verfies the outer commitment.
func (v *Verifier[E]) verifyOuterCommitment(batch []ring.Poly, com []*Commitment, pf, pfInv *Proof) bool {
	inDcmpInv := append(pfInv.InCommit, make([]ring.Poly, v.params.outMSISRank)...)

	cutoff := inDcmpInv[v.params.inComDcmpLen:]
	for i := range v.params.outMSISRank {
		cutoff[i] = v.params.ringQOut.NewPoly()
		if v.params.batch > 1 {
			for j := range v.params.batch {
				v.params.ringQOut.MulCoeffsMontgomeryThenAdd(com[j].Value[i], batch[j], cutoff[i])
			}
		} else {
			cutoff[i].Copy(com[0].Value[i])
		}

		v.params.ringQOut.MulRNSScalarMontgomery(cutoff[i], v.outCutOff, cutoff[i])

		for j := range v.params.inComDcmpLen {
			v.params.ringQOut.MulCoeffsMontgomeryThenSub(v.ck.Out[i][j], pf.InCommit[j], cutoff[i])
		}

		v.params.ringQOut.IMForm(cutoff[i], cutoff[i])
		v.params.ringQOut.INTT(cutoff[i], cutoff[i])
	}

	return v.verifyNorm(v.params.ringQOut, v.rnsOut, inDcmpInv, v.params.inComDcmpTwoNm)
}

// verifyInnerCommitment verfies the inner commitment.
func (v *Verifier[E]) verifyInnerCommitment(chals []ring.Poly, pf, pfInv *Proof) bool {
	resInv := append(pfInv.Encode, pfInv.MLWE...)
	resInv = append(resInv, make([]ring.Poly, v.params.inMSISRank)...)

	inComQ := v.params.ringQ.NewPoly()
	cutoff := resInv[v.params.rows+v.params.mlweRank+v.params.inMSISRank:]
	for i := range v.params.inMSISRank {
		cutoff[i] = v.params.ringQ.NewPoly()
		for j := range v.params.cols {
			v.embQOutToQ.ModUpQtoP(v.params.ringQOut.Level(), v.params.ringQ.Level(), pfInv.InCommit[j*v.params.inMSISRank+i], inComQ)

			v.params.ringQ.MForm(inComQ, inComQ)
			v.params.ringQ.NTT(inComQ, inComQ)

			v.params.ringQ.MulCoeffsMontgomeryThenAdd(inComQ, chals[j], cutoff[i])
		}

		v.params.ringQ.MulRNSScalarMontgomery(cutoff[i], v.inCutOff, cutoff[i])

		v.params.ringQ.Add(cutoff[i], pf.Commit[i], cutoff[i])
		for j := range v.params.rows {
			v.params.ringQ.MulCoeffsMontgomeryThenSub(v.ck.In[i][j], pf.Encode[j], cutoff[i])
		}
		for j := range v.params.mlweRank {
			v.params.ringQ.MulCoeffsMontgomeryThenSub(v.ck.MLWE[i][j], pf.MLWE[j], cutoff[i])
		}
		v.params.ringQ.Sub(pf.MLWE[v.params.mlweRank+i], cutoff[i], cutoff[i])

		v.params.ringQ.IMForm(cutoff[i], cutoff[i])
		v.params.ringQ.INTT(cutoff[i], cutoff[i])
	}

	return v.verifyNorm(v.params.ringQ, v.ecd.rns, resInv, v.params.resTwoNm)
}

// verifyConsistency verifies the consistency of the proof.
func (v *Verifier[E]) verifyConsistency(x E, challenge []ring.Poly, pf *Proof) bool {
	zero := v.params.ringQ.NewPoly()
	test := v.params.ringQ.NewPoly()

	left := leftVec(v.params, x)
	leftEcd := v.params.ringQ.NewPoly()

	for i := 0; i < v.params.rows; i++ {
		v.ecd.EncodeTo(leftEcd, []E{left[i]})
		v.params.ringQ.MulCoeffsMontgomeryThenAdd(leftEcd, pf.Encode[i], test)
	}

	for i := 0; i < v.params.cols; i++ {
		v.params.ringQ.MulCoeffsMontgomeryThenSub(challenge[i], pf.Partial[i], test)
	}
	v.params.ringQ.Sub(test, pf.PartialMask, test)

	return test.Equal(&zero)
}

// verifyEval verifies the evaluation.
func (v *Verifier[E]) verifyEval(x E, batch []ring.Poly, y []E, pf, pfInv *Proof) bool {
	right := rightVec(v.params, x)

	yBatch := x.New()
	mul := x.New()
	if v.params.batch > 1 {
		batchInv := v.params.ringQ.NewPoly()
		batchDcd := make([]E, v.params.slots)
		for i := 0; i < v.params.slots; i++ {
			batchDcd[i] = x.New()
		}

		for i := 0; i < v.params.batch; i++ {
			v.params.ringQ.IMForm(batch[i], batchInv)
			v.params.ringQ.INTT(batchInv, batchInv)
			v.ecd.DecodeTo(batchDcd, batchInv)
			yBatch.Add(yBatch, mul.Mul(batchDcd[0], y[i]))
		}
	} else {
		yBatch.Set(y[0])
	}

	test := x.New()
	dcd := make([]E, v.params.slots)
	for i := 0; i < v.params.slots; i++ {
		dcd[i] = x.New()
	}
	for i := 0; i < v.params.cols; i++ {
		v.ecd.DecodeTo(dcd, pfInv.Partial[i])
		for j := 0; j < v.params.slots; j++ {
			test.Add(test, mul.Mul(right[i*v.params.slots+j], dcd[j]))
		}
	}

	return test.Cmp(yBatch) == 0
}

// verifyNorm checks the norm of the given polynomials.
func (v *Verifier[E]) verifyNorm(ringQ *ring.Ring, rns *RNSReconstructor, p []ring.Poly, nm float64) bool {
	nmSq := big.NewInt(0)
	sq := big.NewInt(0)
	pBig := make([]*big.Int, ringQ.N())
	for i := range pBig {
		pBig[i] = big.NewInt(0)
	}

	for i := range p {
		rns.ReconstructTo(pBig, p[i])
		for j := 0; j < v.params.ringQ.N(); j++ {
			sq.Mul(pBig[j], pBig[j])
			nmSq.Add(nmSq, sq)
		}
	}

	nmSq.Sqrt(nmSq)
	nmTest, _ := nmSq.Float64()
	return nmTest < nm
}
