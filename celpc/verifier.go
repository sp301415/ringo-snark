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
}

// NewVerifier creates a new Verifier.
func NewVerifier(params Parameters, ck AjtaiCommitKey) Verifier {
	return Verifier{
		Parameters: params,
		Encoder:    NewEncoder(params),
		Commiter:   NewAjtaiCommiter(params, ck),
		Oracle:     NewRandomOracle(params),
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
	for i := 0; i < v.Parameters.ajtaiSize; i++ {
		for j := 0; j < v.Parameters.polyCommitSize; j++ {
			v.Oracle.WritePoly(v.Commiter.CommitKey.A0[i][j])
		}
		for j := 0; j < v.Parameters.ajtaiRandSize-v.Parameters.ajtaiSize; j++ {
			v.Oracle.WritePoly(v.Commiter.CommitKey.A1[i][j])
		}
	}
	for i := 0; i < len(comVec); i++ {
		for j := 0; j < len(comVec[i].Value)-1; j++ {
			v.Oracle.WriteAjtaiCommitment(comVec[i].Value[j])
		}
	}

	coeffs := make([]*big.Int, v.Parameters.ringQ.N())
	for i := 0; i < v.Parameters.ringQ.N(); i++ {
		coeffs[i] = big.NewInt(0)
	}

	for i := 0; i < v.Parameters.Repetition(); i++ {
		norm := big.NewInt(0)
		for j := 0; j < v.Parameters.polyCommitSize; j++ {
			polyToBigIntCenteredAssign(v.Parameters, openPf.ResponseMask[i][j], coeffs)
			for k := 0; k < v.Parameters.ringQ.N(); k++ {
				coeffs[k].Mul(coeffs[k], coeffs[k])
				norm.Add(norm, coeffs[k])
			}
		}

		for j := 0; j < v.Parameters.ajtaiRandSize; j++ {
			polyToBigIntCenteredAssign(v.Parameters, openPf.ResponseRand[i][j], coeffs)
			for k := 0; k < v.Parameters.ringQ.N(); k++ {
				coeffs[k].Mul(coeffs[k], coeffs[k])
				norm.Add(norm, coeffs[k])
			}
		}

		normFloat, _ := norm.Float64()
		if math.Sqrt(normFloat) > v.Parameters.openProofBound {
			return false
		}
	}

	for i := 0; i < v.Parameters.Repetition(); i++ {
		v.Oracle.WriteAjtaiCommitment(openPf.Commitment[i])
	}

	challenge := make([][]ring.Poly, v.Parameters.Repetition())
	batchCommitment := make([]AjtaiCommitment, 0)
	for i := 0; i < len(comVec); i++ {
		batchCommitment = append(batchCommitment, comVec[i].Value[:len(comVec[i].Value)-1]...)
	}
	batchCount := len(batchCommitment)

	for i := 0; i < v.Parameters.Repetition(); i++ {
		challenge[i] = make([]ring.Poly, batchCount)
		for j := 0; j < batchCount; j++ {
			challenge[i][j] = v.Parameters.ringQ.NewPoly()
			v.Oracle.SampleMonomialAssign(challenge[i][j])
		}
	}

	commitResponse := NewAjtaiCommitment(v.Parameters)
	commitCombine := NewAjtaiCommitment(v.Parameters)
	for i := 0; i < v.Parameters.Repetition(); i++ {
		v.Commiter.CommitAssign(openPf.ResponseMask[i], openPf.ResponseRand[i], commitResponse)

		commitCombine.CopyFrom(openPf.Commitment[i])
		for j := 0; j < batchCount; j++ {
			for k := 0; k < v.Parameters.ajtaiSize; k++ {
				v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchCommitment[j].Value[k], commitCombine.Value[k])
			}
		}

		if !commitResponse.Equals(commitCombine) {
			return false
		}
	}

	return true
}

// VerifyevalPf verifies the evaluation proof.
func (v *Verifier) VerifyEvaluation(x *big.Int, com Commitment, evalPf EvaluationProof) bool {
	coeffs := make([]*big.Int, v.Parameters.ringQ.N())
	for i := 0; i < v.Parameters.ringQ.N(); i++ {
		coeffs[i] = big.NewInt(0)
	}
	norm := big.NewInt(0)
	for i := 0; i < v.Parameters.polyCommitSize; i++ {
		polyToBigIntCenteredAssign(v.Parameters, evalPf.Mask[i], coeffs)
		for j := 0; j < v.Parameters.ringQ.N(); j++ {
			coeffs[j].Mul(coeffs[j], coeffs[j])
			norm.Add(norm, coeffs[j])
		}
	}
	for i := 0; i < v.Parameters.ajtaiRandSize; i++ {
		polyToBigIntCenteredAssign(v.Parameters, evalPf.Rand[i], coeffs)
		for j := 0; j < v.Parameters.ringQ.N(); j++ {
			coeffs[j].Mul(coeffs[j], coeffs[j])
			norm.Add(norm, coeffs[j])
		}
	}

	normFloat, _ := norm.Float64()
	if math.Sqrt(normFloat) > v.Parameters.evalBound {
		return false
	}

	commitCount := len(com.Value) - 2

	xEcd := v.Encoder.Encode([]*big.Int{big.NewInt(0).Mod(x, v.Parameters.modulus)})
	xPowBuf, xPowSkip := big.NewInt(1), big.NewInt(0).Exp(x, big.NewInt(int64(v.Parameters.bigIntCommitSize)), v.Parameters.modulus)
	xPowEcd := make([]ring.Poly, commitCount)
	for i := 0; i < commitCount; i++ {
		xPowEcd[i] = v.Encoder.Encode([]*big.Int{xPowBuf})
		xPowBuf.Mul(xPowBuf, xPowSkip)
		xPowBuf.Mod(xPowBuf, v.Parameters.modulus)
	}

	commitevalPf := v.Commiter.Commit(evalPf.Mask, evalPf.Rand)
	commitCombine := NewAjtaiCommitment(v.Parameters)
	commitCombine.CopyFrom(com.Value[commitCount+1])
	for j := 0; j < v.Parameters.ajtaiSize; j++ {
		v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, com.Value[commitCount].Value[j], commitCombine.Value[j])
	}
	for i := 0; i < commitCount; i++ {
		for j := 0; j < v.Parameters.ajtaiSize; j++ {
			v.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[i], com.Value[i].Value[j], commitCombine.Value[j])
		}
	}

	if !commitevalPf.Equals(commitCombine) {
		return false
	}

	xPowBasis := make([]*big.Int, v.Parameters.bigIntCommitSize)
	xPowBasis[0] = big.NewInt(1)
	for i := 1; i < v.Parameters.bigIntCommitSize; i++ {
		xPowBasis[i] = big.NewInt(0).Mul(xPowBasis[i-1], x)
		xPowBasis[i].Mod(xPowBasis[i], v.Parameters.modulus)
	}

	maskDcd := v.Encoder.DecodeChunk(evalPf.Mask)
	valueCombine := big.NewInt(0)
	prodBuf := big.NewInt(0)
	for i := 0; i < v.Parameters.bigIntCommitSize; i++ {
		prodBuf.Mul(xPowBasis[i], maskDcd[i])
		valueCombine.Add(valueCombine, prodBuf)
	}
	valueCombine.Mod(valueCombine, v.Parameters.modulus)

	return valueCombine.Cmp(evalPf.Value) == 0
}
