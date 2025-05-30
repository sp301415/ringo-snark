package celpc

import (
	"math"
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

// Verifier is a verifier for polynomial commitment.
type Verifier struct {
	Parameters Parameters
	Encoder    *Encoder
	Commiter   *AjtaiCommiter
	Oracle     *RandomOracle

	buffer verifierBuffer
}

type verifierBuffer struct {
	coeffs []*big.Int
	norm   *big.Int

	challenge      ring.Poly
	commitResponse AjtaiCommitment
	commitCombine  AjtaiCommitment

	exp     *big.Int
	xEcd    ring.Poly
	xPowEcd ring.Poly

	xPow     *big.Int
	xPowSkip *big.Int

	xPowBasis []*big.Int
	maskDcd   []*big.Int

	valueCombine *big.Int
}

// NewVerifier creates a new Verifier.
func NewVerifier(params Parameters, ck AjtaiCommitKey) *Verifier {
	return &Verifier{
		Parameters: params,
		Encoder:    NewEncoder(params),
		Commiter:   NewAjtaiCommiter(params, ck),
		Oracle:     NewRandomOracle(params),

		buffer: newVerifierBuffer(params),
	}
}

// newVerifierBuffer creates a new verifierBuffer.
func newVerifierBuffer(params Parameters) verifierBuffer {
	coeffs := make([]*big.Int, params.ringQ.N())
	for i := 0; i < params.ringQ.N(); i++ {
		coeffs[i] = big.NewInt(0).Set(params.ringQ.Modulus())
	}

	xPowBasis := make([]*big.Int, params.bigIntCommitSize)
	maskDcd := make([]*big.Int, params.bigIntCommitSize)
	for i := 0; i < params.bigIntCommitSize; i++ {
		xPowBasis[i] = big.NewInt(0).Set(params.modulus)
		maskDcd[i] = big.NewInt(0).Set(params.modulus)
	}

	return verifierBuffer{
		coeffs: coeffs,
		norm:   big.NewInt(0).Set(params.ringQ.Modulus()),

		challenge:      params.ringQ.NewPoly(),
		commitResponse: NewAjtaiCommitment(params),
		commitCombine:  NewAjtaiCommitment(params),

		exp:     big.NewInt(0).Set(params.modulus),
		xEcd:    params.ringQ.NewPoly(),
		xPowEcd: params.ringQ.NewPoly(),

		xPow:     big.NewInt(0).Set(params.modulus),
		xPowSkip: big.NewInt(0).Set(params.modulus),

		xPowBasis: xPowBasis,
		maskDcd:   maskDcd,

		valueCombine: big.NewInt(0).Set(params.modulus),
	}
}

// ShallowCopy creates a copy of Verifier that is thread-safe.
func (v *Verifier) ShallowCopy() *Verifier {
	return &Verifier{
		Parameters: v.Parameters,

		Encoder:  v.Encoder.ShallowCopy(),
		Commiter: v.Commiter,
		Oracle:   NewRandomOracle(v.Parameters),
	}
}

// VerifyOpeningProof verifies the proof of opening.
func (v *Verifier) VerifyOpeningProof(comVec []Commitment, openPf OpeningProof) bool {
	v.Oracle.Reset()

	for i := 0; i < v.Parameters.Repetition(); i++ {
		v.buffer.norm.SetUint64(0)
		for j := 0; j < v.Parameters.polyCommitSize; j++ {
			v.Encoder.ReconstructAssign(openPf.ResponseMask[i][j], v.buffer.coeffs)
			for k := 0; k < v.Parameters.ringQ.N(); k++ {
				v.buffer.coeffs[k].Mul(v.buffer.coeffs[k], v.buffer.coeffs[k])
				v.buffer.norm.Add(v.buffer.norm, v.buffer.coeffs[k])
			}
		}

		for j := 0; j < v.Parameters.ajtaiRandSize; j++ {
			v.Encoder.ReconstructAssign(openPf.ResponseRand[i][j], v.buffer.coeffs)
			for k := 0; k < v.Parameters.ringQ.N(); k++ {
				v.buffer.coeffs[k].Mul(v.buffer.coeffs[k], v.buffer.coeffs[k])
				v.buffer.norm.Add(v.buffer.norm, v.buffer.coeffs[k])
			}
		}

		normFloat, _ := v.buffer.norm.Float64()
		if math.Sqrt(normFloat) > v.Parameters.openProofBound {
			return false
		}
	}

	for i := 0; i < v.Parameters.Repetition(); i++ {
		v.Oracle.WriteAjtaiCommitment(openPf.Commitment[i])
	}
	v.Oracle.Finalize()

	batchCommitment := make([]AjtaiCommitment, 0)
	for i := 0; i < len(comVec); i++ {
		batchCommitment = append(batchCommitment, comVec[i].Value[:len(comVec[i].Value)-1]...)
	}
	batchCount := len(batchCommitment)

	for i := 0; i < v.Parameters.Repetition(); i++ {
		v.Commiter.CommitAssign(openPf.ResponseMask[i], openPf.ResponseRand[i], v.buffer.commitResponse)

		v.buffer.commitCombine.CopyFrom(openPf.Commitment[i])
		for j := 0; j < batchCount; j++ {
			v.Oracle.SampleMonomialAssign(v.buffer.challenge)
			for k := 0; k < v.Parameters.ajtaiSize; k++ {
				v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(v.buffer.challenge, batchCommitment[j].Value[k], v.buffer.commitCombine.Value[k])
			}
		}

		if !v.buffer.commitResponse.Equals(v.buffer.commitCombine) {
			return false
		}
	}

	return true
}

// VerifyevalPf verifies the evaluation proof.
func (v *Verifier) VerifyEvaluation(x *big.Int, com Commitment, evalPf EvaluationProof) bool {
	v.buffer.norm.SetUint64(0)
	for i := 0; i < v.Parameters.polyCommitSize; i++ {
		v.Encoder.ReconstructAssign(evalPf.Mask[i], v.buffer.coeffs)
		for j := 0; j < v.Parameters.ringQ.N(); j++ {
			v.buffer.coeffs[j].Mul(v.buffer.coeffs[j], v.buffer.coeffs[j])
			v.buffer.norm.Add(v.buffer.norm, v.buffer.coeffs[j])
		}
	}
	for i := 0; i < v.Parameters.ajtaiRandSize; i++ {
		v.Encoder.ReconstructAssign(evalPf.Rand[i], v.buffer.coeffs)
		for j := 0; j < v.Parameters.ringQ.N(); j++ {
			v.buffer.coeffs[j].Mul(v.buffer.coeffs[j], v.buffer.coeffs[j])
			v.buffer.norm.Add(v.buffer.norm, v.buffer.coeffs[j])
		}
	}

	normFloat, _ := v.buffer.norm.Float64()
	if math.Sqrt(normFloat) > v.Parameters.evalProofBound {
		return false
	}

	commitCount := len(com.Value) - 2

	v.buffer.xPow.Mod(x, v.Parameters.modulus)
	v.Encoder.EncodeAssign([]*big.Int{v.buffer.xPow}, v.buffer.xEcd)

	v.buffer.xPowSkip.Exp(x, v.buffer.exp.SetUint64(uint64(v.Parameters.bigIntCommitSize)), v.Parameters.modulus)
	v.buffer.xPow.SetUint64(1)

	v.Commiter.CommitAssign(evalPf.Mask, evalPf.Rand, v.buffer.commitResponse)

	v.buffer.commitCombine.CopyFrom(com.Value[commitCount+1])
	for j := 0; j < v.Parameters.ajtaiSize; j++ {
		v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(v.buffer.xEcd, com.Value[commitCount].Value[j], v.buffer.commitCombine.Value[j])
	}
	for i := 0; i < commitCount; i++ {
		v.Encoder.EncodeAssign([]*big.Int{v.buffer.xPow}, v.buffer.xPowEcd)
		v.buffer.xPow.Mul(v.buffer.xPow, v.buffer.xPowSkip)
		v.buffer.xPow.Mod(v.buffer.xPow, v.Parameters.modulus)
		for j := 0; j < v.Parameters.ajtaiSize; j++ {
			v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(v.buffer.xPowEcd, com.Value[i].Value[j], v.buffer.commitCombine.Value[j])
		}
	}

	if !v.buffer.commitResponse.Equals(v.buffer.commitCombine) {
		return false
	}

	v.buffer.xPowBasis[0].SetUint64(1)
	for i := 1; i < v.Parameters.bigIntCommitSize; i++ {
		v.buffer.xPowBasis[i].Mul(v.buffer.xPowBasis[i-1], x)
		v.buffer.xPowBasis[i].Mod(v.buffer.xPowBasis[i], v.Parameters.modulus)
	}

	v.Encoder.DecodeChunkAssign(evalPf.Mask, v.buffer.maskDcd)

	v.buffer.valueCombine.SetUint64(0)
	for i := 0; i < v.Parameters.bigIntCommitSize; i++ {
		v.buffer.xPow.Mul(v.buffer.xPowBasis[i], v.buffer.maskDcd[i])
		v.buffer.valueCombine.Add(v.buffer.valueCombine, v.buffer.xPow)
	}
	v.buffer.valueCombine.Mod(v.buffer.valueCombine, v.Parameters.modulus)

	return v.buffer.valueCombine.Cmp(evalPf.Value) == 0
}
