package jindo

import (
	"crypto/sha3"
	"math/big"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Verifier is a Jindo verifier.
type Verifier[E num.Uint[E]] struct {
	params Parameters
	ecd    *Encoder[E]
	rns    *RNSReconstructor

	ck *CommitKey
}

// NewVerifier creates a new [Verifier].
func NewVerifier[E num.Uint[E]](params Parameters, crs []byte) *Verifier[E] {
	return &Verifier[E]{
		params: params,
		ecd:    NewEncoder[E](params),
		rns:    NewRNSReconstructor(params.ringQ),

		ck: NewCommitKey(params, crs),
	}
}

// Verify verfies the polynomial commitment.
func (v *Verifier[E]) Verify(x E, batch []ring.Poly, com []*Commitment, y []E, pf *Proof) bool {
	switch {
	case len(com) != v.params.batch:
		panic("EvaluateBatch: len(v) != params.batch")
	}

	oracle := sha3.NewSHAKE128()
	v.ck.WriteRawTo(oracle)
	for i := 0; i < v.params.batch; i++ {
		com[i].WriteRawTo(oracle)
	}
	oracle.Write(x.Marshal())

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
		EncodeChallengeTo(v.params, chals[i], chalBytes)
	}

	inCommitInv := make([]ring.Poly, v.params.inComDcmpLen)
	for i := range inCommitInv {
		inCommitInv[i] = *pf.InCommit[i].CopyNew()
		v.params.ringQ.IMForm(inCommitInv[i], inCommitInv[i])
		v.params.ringQ.INTT(inCommitInv[i], inCommitInv[i])
	}

	partialInv := make([]ring.Poly, v.params.cols)
	for i := range partialInv {
		partialInv[i] = *pf.Partial[i].CopyNew()
		v.params.ringQ.IMForm(partialInv[i], partialInv[i])
		v.params.ringQ.INTT(partialInv[i], partialInv[i])
	}

	resInv := make([]ring.Poly, v.params.cols+v.params.mlweRank+v.params.inMSISRank)
	for i := 0; i < v.params.cols; i++ {
		resInv[i] = *pf.Encode[i].CopyNew()
		v.params.ringQ.IMForm(resInv[i], resInv[i])
		v.params.ringQ.INTT(resInv[i], resInv[i])
	}
	for i := 0; i < v.params.mlweRank+v.params.inMSISRank; i++ {
		resInv[v.params.cols+i] = *pf.MLWE[i].CopyNew()
		v.params.ringQ.IMForm(resInv[v.params.cols+i], resInv[v.params.cols+i])
		v.params.ringQ.INTT(resInv[v.params.cols+i], resInv[v.params.cols+i])
	}

	if !v.verifyOuterCommitment(batch, com, pf) {
		return false
	}

	if !v.verifyInnerCommitment(chals, inCommitInv, pf) {
		return false
	}

	if !v.verifyConsistency(x, chals, pf) {
		return false
	}

	if !v.verifyEval(x, batch, y, partialInv) {
		return false
	}

	if !v.verifyNorm(resInv, v.params.resTwoNm) {
		return false
	}

	if !v.verifyNorm(partialInv, v.params.prTwoNm) {
		return false
	}

	if !v.verifyNorm(inCommitInv, v.params.inComDcmpTwoNm) {
		return false
	}

	return true
}

// verifyOuterCommitment verfies the outer commitment.
// Checks that \sum \alpha_i * u_i = D * G(t).
func (v *Verifier[E]) verifyOuterCommitment(batch []ring.Poly, com []*Commitment, pf *Proof) bool {
	zero := v.params.ringQ.NewPoly()
	test := v.params.ringQ.NewPoly()
	for i := 0; i < v.params.outMSISRank; i++ {
		test.Zero()
		if v.params.batch > 1 {
			for j := 0; j < v.params.batch; j++ {
				v.params.ringQ.MulCoeffsMontgomeryThenAdd(com[j].Value[i], batch[j], test)
			}
		} else {
			test.Copy(com[0].Value[i])
		}

		for j := 0; j < v.params.cols*v.params.inMSISRank*v.params.ringQ.ModuliChainLength(); j++ {
			v.params.ringQ.MulCoeffsMontgomeryThenSub(v.ck.Out[i][j], pf.InCommit[j], test)
		}

		if !test.Equal(&zero) {
			return false
		}
	}

	return true
}

// verifyInnerCommitment verfies the inner commitment.
// Checks that Ah + Bs = w + \sum c_i * t_i.
func (v *Verifier[E]) verifyInnerCommitment(challenge, inCommitInv []ring.Poly, pf *Proof) bool {
	zero := v.params.ringQ.NewPoly()
	test := v.params.ringQ.NewPoly()
	inCom := v.params.ringQ.NewPoly()
	for i := 0; i < v.params.inMSISRank; i++ {
		for j := 0; j < v.params.rows; j++ {
			v.params.ringQ.MulCoeffsMontgomeryThenAdd(v.ck.In[i][j], pf.Encode[j], test)
		}
		for j := 0; j < v.params.mlweRank; j++ {
			v.params.ringQ.MulCoeffsMontgomeryThenAdd(v.ck.MLWE[i][j], pf.MLWE[j], test)
		}
		v.params.ringQ.Add(pf.MLWE[v.params.mlweRank+i], test, test)

		v.params.ringQ.Sub(test, pf.Commit[i], test)
		for j := 0; j < v.params.cols; j++ {
			idx := i + j*v.params.inMSISRank
			for k := 0; k < v.params.ringQ.ModuliChainLength(); k++ {
				copy(inCom.Coeffs[k], inCommitInv[idx*v.params.ringQ.ModuliChainLength()+k].Coeffs[k])
			}
			v.params.ringQ.MForm(inCom, inCom)
			v.params.ringQ.NTT(inCom, inCom)
			v.params.ringQ.MulCoeffsMontgomeryThenSub(inCom, challenge[j], test)
		}

		if !test.Equal(&zero) {
			return false
		}
	}

	return true
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
func (v *Verifier[E]) verifyEval(x E, batch []ring.Poly, y []E, partialInv []ring.Poly) bool {
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
		v.ecd.DecodeTo(dcd, partialInv[i])
		for j := 0; j < v.params.slots; j++ {
			test.Add(test, mul.Mul(right[i*v.params.slots+j], dcd[j]))
		}
	}

	return test.Cmp(yBatch) == 0
}

// verifyNorm checks the norm of the given polynomials.
func (v *Verifier[E]) verifyNorm(p []ring.Poly, nm float64) bool {
	nmSq := big.NewInt(0)
	sq := big.NewInt(0)
	pBig := make([]*big.Int, v.params.ringQ.N())
	for i := range pBig {
		pBig[i] = big.NewInt(0)
	}

	for i := range p {
		v.rns.ReconstructTo(pBig, p[i])
		for j := 0; j < v.params.ringQ.N(); j++ {
			sq.Mul(pBig[j], pBig[j])
			nmSq.Add(nmSq, sq)
		}
	}

	nmSq.Sqrt(nmSq)
	nmTest, _ := nmSq.Float64()
	return nmTest < nm
}
