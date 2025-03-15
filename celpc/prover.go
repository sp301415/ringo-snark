package celpc

import (
	"math"
	"math/big"
	"sync"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// Prover is a prover for polynomial commitment.
type Prover struct {
	Parameters Parameters

	UniformSampler  *UniformSampler
	GaussianSampler *COSACSampler
	Oracle          *RandomOracle

	Encoder  *Encoder
	Commiter *AjtaiCommiter

	CommitEncoder     *EncoderFixedStdDev
	CommitRandSampler *TwinCDTSampler
}

// NewProver creates a new Prover.
func NewProver(params Parameters, ck AjtaiCommitKey) *Prover {
	return &Prover{
		Parameters: params,

		UniformSampler:  NewUniformSampler(params),
		GaussianSampler: NewCOSACSampler(params),
		Oracle:          NewRandomOracle(params),

		Encoder:  NewEncoder(params),
		Commiter: NewAjtaiCommiter(params, ck),

		CommitEncoder:     NewEncoderFixedStdDev(params, params.commitStdDev),
		CommitRandSampler: NewTwinCDTSampler(params, params.commitRandStdDev),
	}
}

// ShallowCopy creates a copy of Prover that is thread-safe.
func (p *Prover) ShallowCopy() *Prover {
	return &Prover{
		Parameters: p.Parameters,

		UniformSampler:  NewUniformSampler(p.Parameters),
		GaussianSampler: NewCOSACSampler(p.Parameters),
		Oracle:          NewRandomOracle(p.Parameters),

		Encoder:  p.Encoder.ShallowCopy(),
		Commiter: p.Commiter,

		CommitEncoder:     p.CommitEncoder.ShallowCopy(),
		CommitRandSampler: p.CommitRandSampler.ShallowCopy(),
	}
}

// Commit commits pBig.
func (p *Prover) Commit(pBig bigring.BigPoly) (Commitment, Opening) {
	comOut := NewCommitment(p.Parameters, pBig.Degree())
	openPfOut := NewOpening(p.Parameters, pBig.Degree())
	p.CommitAssign(pBig, comOut, openPfOut)
	return comOut, openPfOut
}

// CommitAssign commits pBig and assigns it to comOut and openOut.
func (p *Prover) CommitAssign(pBig bigring.BigPoly, comOut Commitment, openOut Opening) {
	commitCount := pBig.Degree() / p.Parameters.bigIntCommitSize

	for i := 0; i < commitCount; i++ {
		pBigChunk := pBig.Coeffs[i*p.Parameters.bigIntCommitSize : (i+1)*p.Parameters.bigIntCommitSize]
		p.CommitEncoder.RandomEncodeChunkAssign(pBigChunk, openOut.Mask[i])
		for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
			p.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[i][j])
		}
		p.Commiter.CommitAssign(openOut.Mask[i], openOut.Rand[i], comOut.Value[i])
	}

	bigBlind0 := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlind1 := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlind0[p.Parameters.bigIntCommitSize-1] = big.NewInt(0)
	bigBlind1[0] = big.NewInt(0)
	for i := 0; i < p.Parameters.bigIntCommitSize-1; i++ {
		bigBlind0[i] = big.NewInt(0)
		p.UniformSampler.SampleModAssign(bigBlind0[i])

		bigBlind1[i+1] = big.NewInt(0).Sub(p.Parameters.modulus, bigBlind0[i])
	}

	p.CommitEncoder.RandomEncodeChunkAssign(bigBlind0, openOut.Mask[commitCount])
	for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
		p.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[commitCount][j])
	}
	p.Commiter.CommitAssign(openOut.Mask[commitCount], openOut.Rand[commitCount], comOut.Value[commitCount])

	blindStdDev := math.Sqrt(float64(commitCount+2)) * p.Parameters.blindStdDev
	blindRandStdDev := math.Sqrt(float64(commitCount+2)) * p.Parameters.blindRandStdDev
	p.Encoder.RandomEncodeChunkAssign(bigBlind1, blindStdDev, openOut.Mask[commitCount+1])
	for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
		p.GaussianSampler.SamplePolyAssign(0, blindRandStdDev, openOut.Rand[commitCount+1][j])
	}
	p.Commiter.CommitAssign(openOut.Mask[commitCount+1], openOut.Rand[commitCount+1], comOut.Value[commitCount+1])
}

// CommitParallel commits pBig in parallel.
func (p *Prover) CommitParallel(pBig bigring.BigPoly) (Commitment, Opening) {
	comOut := NewCommitment(p.Parameters, pBig.Degree())
	openOut := NewOpening(p.Parameters, pBig.Degree())
	p.CommitParallelAssign(pBig, comOut, openOut)
	return comOut, openOut
}

// CommitParallelAssign commits pBig and assigns it to comOut and openOut in parallel.
func (p *Prover) CommitParallelAssign(pBig bigring.BigPoly, comOut Commitment, openOut Opening) {
	commitCount := pBig.Degree() / p.Parameters.bigIntCommitSize

	proverPool := make([]*Prover, commitCount+2)
	for i := 0; i < commitCount+2; i++ {
		proverPool[i] = p.ShallowCopy()
	}

	bigBlind0 := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlind1 := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlind0[p.Parameters.bigIntCommitSize-1] = big.NewInt(0)
	bigBlind1[0] = big.NewInt(0)
	for i := 0; i < p.Parameters.bigIntCommitSize-1; i++ {
		bigBlind0[i] = big.NewInt(0)
		p.UniformSampler.SampleModAssign(bigBlind0[i])

		bigBlind1[i+1] = big.NewInt(0).Sub(p.Parameters.modulus, bigBlind0[i])
	}

	var wg sync.WaitGroup
	wg.Add(commitCount + 2)

	for i := 0; i < commitCount; i++ {
		go func(i int) {
			pIdx := proverPool[i]

			pBigChunk := pBig.Coeffs[i*pIdx.Parameters.bigIntCommitSize : (i+1)*pIdx.Parameters.bigIntCommitSize]
			pIdx.CommitEncoder.RandomEncodeChunkAssign(pBigChunk, openOut.Mask[i])
			for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
				pIdx.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[i][j])
			}
			pIdx.Commiter.CommitAssign(openOut.Mask[i], openOut.Rand[i], comOut.Value[i])

			wg.Done()
		}(i)
	}

	go func() {
		pIdx := proverPool[commitCount]

		pIdx.CommitEncoder.RandomEncodeChunkAssign(bigBlind0, openOut.Mask[commitCount])
		for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
			pIdx.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[commitCount][j])
		}
		pIdx.Commiter.CommitAssign(openOut.Mask[commitCount], openOut.Rand[commitCount], comOut.Value[commitCount])

		wg.Done()
	}()

	go func() {
		pIdx := proverPool[commitCount+1]

		blindStdDev := math.Sqrt(float64(commitCount+2)) * pIdx.Parameters.blindStdDev
		blindRandStdDev := math.Sqrt(float64(commitCount+2)) * pIdx.Parameters.blindRandStdDev

		pIdx.Encoder.RandomEncodeChunkAssign(bigBlind1, blindStdDev, openOut.Mask[commitCount+1])
		for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
			pIdx.GaussianSampler.SamplePolyAssign(0, blindRandStdDev, openOut.Rand[commitCount+1][j])
		}
		pIdx.Commiter.CommitAssign(openOut.Mask[commitCount+1], openOut.Rand[commitCount+1], comOut.Value[commitCount+1])

		wg.Done()
	}()

	wg.Wait()
}

// ProveOpening proves the opening of commitments.
func (p *Prover) ProveOpening(comVec []Commitment, openVec []Opening) OpeningProof {
	openPfOut := NewOpeningProof(p.Parameters)
	p.ProveOpeningAssign(comVec, openVec, openPfOut)
	return openPfOut
}

// ProveOpeningAssign proves the opening of commitments.
func (p *Prover) ProveOpeningAssign(comVec []Commitment, openVec []Opening, openPfOut OpeningProof) {
	p.Oracle.Reset()
	for i := 0; i < len(comVec); i++ {
		for j := 0; j < len(comVec[i].Value)-1; j++ {
			p.Oracle.WriteAjtaiCommitment(comVec[i].Value[j])
		}
	}

	batchMask := make([][]ring.Poly, 0)
	batchRand := make([][]ring.Poly, 0)
	for i := 0; i < len(openVec); i++ {
		batchMask = append(batchMask, openVec[i].Mask[:len(openVec[i].Mask)-1]...)
		batchRand = append(batchRand, openVec[i].Rand[:len(openVec[i].Rand)-1]...)
	}
	batchCount := len(batchMask)

	bigMask := make([]*big.Int, p.Parameters.bigIntCommitSize)
	for i := 0; i < p.Parameters.bigIntCommitSize; i++ {
		bigMask[i] = big.NewInt(0)
	}

	openingProofStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofStdDev
	openingProofRandStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofRandStdDev
	for i := 0; i < p.Parameters.Repetition(); i++ {
		for j := 0; j < p.Parameters.bigIntCommitSize; j++ {
			p.UniformSampler.SampleModAssign(bigMask[j])
		}
		p.Encoder.RandomEncodeChunkAssign(bigMask, openingProofStdDev, openPfOut.ResponseMask[i])
		for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
			p.GaussianSampler.SamplePolyAssign(0, openingProofRandStdDev, openPfOut.ResponseRand[i][j])
		}
		p.Commiter.CommitAssign(openPfOut.ResponseMask[i], openPfOut.ResponseRand[i], openPfOut.Commitment[i])
	}

	for i := 0; i < p.Parameters.Repetition(); i++ {
		p.Oracle.WriteAjtaiCommitment(openPfOut.Commitment[i])
	}

	challenge := make([][]ring.Poly, p.Parameters.Repetition())
	for i := 0; i < p.Parameters.Repetition(); i++ {
		challenge[i] = make([]ring.Poly, batchCount)
		for j := 0; j < batchCount; j++ {
			challenge[i][j] = p.Parameters.ringQ.NewPoly()
			p.Oracle.SampleMonomialAssign(challenge[i][j])
		}
	}

	for i := 0; i < p.Parameters.Repetition(); i++ {
		for j := 0; j < batchCount; j++ {
			for k := 0; k < p.Parameters.polyCommitSize; k++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchMask[j][k], openPfOut.ResponseMask[i][k])
			}
			for k := 0; k < p.Parameters.ajtaiRandSize; k++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchRand[j][k], openPfOut.ResponseRand[i][k])
			}
		}
	}
}

// ProveOpeningParallel proves the opening of commitments in parallel.
func (p *Prover) ProveOpeningParallel(comVec []Commitment, openVec []Opening) OpeningProof {
	openPfOut := NewOpeningProof(p.Parameters)
	p.ProveOpeningParallelAssign(comVec, openVec, openPfOut)
	return openPfOut
}

// ProveOpeningParallelAssign proves the opening of commitments in parallel.
func (p *Prover) ProveOpeningParallelAssign(comVec []Commitment, openVec []Opening, openPfOut OpeningProof) {
	p.Oracle.Reset()
	for i := 0; i < len(comVec); i++ {
		for j := 0; j < len(comVec[i].Value)-1; j++ {
			p.Oracle.WriteAjtaiCommitment(comVec[i].Value[j])
		}
	}

	batchMask := make([][]ring.Poly, 0)
	batchRand := make([][]ring.Poly, 0)
	for i := 0; i < len(openVec); i++ {
		batchMask = append(batchMask, openVec[i].Mask[:len(openVec[i].Mask)-1]...)
		batchRand = append(batchRand, openVec[i].Rand[:len(openVec[i].Rand)-1]...)
	}
	batchCount := len(batchMask)

	openingProofStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofStdDev
	openingProofRandStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofRandStdDev

	proverPool := make([]*Prover, p.Parameters.Repetition())
	for i := 0; i < p.Parameters.Repetition(); i++ {
		proverPool[i] = p.ShallowCopy()
	}

	var wg sync.WaitGroup
	wg.Add(p.Parameters.Repetition())

	for i := 0; i < p.Parameters.Repetition(); i++ {
		go func(i int) {
			pIdx := proverPool[i]

			bigMask := make([]*big.Int, pIdx.Parameters.bigIntCommitSize)
			for i := 0; i < pIdx.Parameters.bigIntCommitSize; i++ {
				bigMask[i] = big.NewInt(0)
				pIdx.UniformSampler.SampleModAssign(bigMask[i])
			}
			pIdx.Encoder.RandomEncodeChunkAssign(bigMask, openingProofStdDev, openPfOut.ResponseMask[i])
			for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
				pIdx.GaussianSampler.SamplePolyAssign(0, openingProofRandStdDev, openPfOut.ResponseRand[i][j])
			}
			pIdx.Commiter.CommitAssign(openPfOut.ResponseMask[i], openPfOut.ResponseRand[i], openPfOut.Commitment[i])

			wg.Done()
		}(i)
	}

	wg.Wait()

	for i := 0; i < p.Parameters.Repetition(); i++ {
		p.Oracle.WriteAjtaiCommitment(openPfOut.Commitment[i])
	}

	challenge := make([][]ring.Poly, p.Parameters.Repetition())
	for i := 0; i < p.Parameters.Repetition(); i++ {
		challenge[i] = make([]ring.Poly, batchCount)
		for j := 0; j < batchCount; j++ {
			challenge[i][j] = p.Parameters.ringQ.NewPoly()
			p.Oracle.SampleMonomialAssign(challenge[i][j])
		}
	}

	wg.Add(p.Parameters.Repetition() * (p.Parameters.polyCommitSize + p.Parameters.ajtaiRandSize))

	for i := 0; i < p.Parameters.Repetition(); i++ {
		for k := 0; k < p.Parameters.polyCommitSize; k++ {
			go func(i, k int) {
				for j := 0; j < batchCount; j++ {
					p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchMask[j][k], openPfOut.ResponseMask[i][k])
				}
				wg.Done()
			}(i, k)
		}
	}

	for i := 0; i < p.Parameters.Repetition(); i++ {
		for k := 0; k < p.Parameters.ajtaiRandSize; k++ {
			go func(i, k int) {
				for j := 0; j < batchCount; j++ {
					p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchRand[j][k], openPfOut.ResponseRand[i][k])
				}
				wg.Done()
			}(i, k)
		}
	}

	wg.Wait()
}

// Evaluate evaluates pBig at x with proof.
func (p *Prover) Evaluate(x *big.Int, open Opening) EvaluationProof {
	evalPfOut := NewEvaluationProof(p.Parameters)
	p.EvaluateAssign(x, open, evalPfOut)
	return evalPfOut
}

// EvaluateAssign evaluates pBig at x with proof and assigns it to evalPfOut.
func (p *Prover) EvaluateAssign(x *big.Int, open Opening, evalPfOut EvaluationProof) {
	commitCount := len(open.Mask) - 2

	xEcd := p.Encoder.Encode([]*big.Int{big.NewInt(0).Mod(x, p.Parameters.modulus)})
	xPowBuf, xPowSkip := big.NewInt(1), big.NewInt(0).Exp(x, big.NewInt(int64(p.Parameters.bigIntCommitSize)), p.Parameters.modulus)
	xPowEcd := make([]ring.Poly, commitCount)
	for i := 0; i < commitCount; i++ {
		xPowEcd[i] = p.Encoder.Encode([]*big.Int{xPowBuf})
		xPowBuf.Mul(xPowBuf, xPowSkip)
		xPowBuf.Mod(xPowBuf, p.Parameters.modulus)
	}

	for i := 0; i < p.Parameters.polyCommitSize; i++ {
		evalPfOut.Mask[i].Copy(open.Mask[commitCount+1][i])
		p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Mask[commitCount][i], evalPfOut.Mask[i])
		for j := 0; j < commitCount; j++ {
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Mask[j][i], evalPfOut.Mask[i])
		}
	}

	for i := 0; i < p.Parameters.ajtaiRandSize; i++ {
		evalPfOut.Rand[i].Copy(open.Rand[commitCount+1][i])
		p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Rand[commitCount][i], evalPfOut.Rand[i])
		for j := 0; j < commitCount; j++ {
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Rand[j][i], evalPfOut.Rand[i])
		}
	}

	xPowBasis := make([]*big.Int, p.Parameters.bigIntCommitSize)
	xPowBasis[0] = big.NewInt(1)
	for i := 1; i < p.Parameters.bigIntCommitSize; i++ {
		xPowBasis[i] = big.NewInt(0).Mul(xPowBasis[i-1], x)
		xPowBasis[i].Mod(xPowBasis[i], p.Parameters.modulus)
	}

	maskDcd := p.Encoder.DecodeChunk(evalPfOut.Mask)
	evalPfOut.Value.SetInt64(0)
	prodBuf := big.NewInt(0)
	for i := 0; i < p.Parameters.bigIntCommitSize; i++ {
		prodBuf.Mul(xPowBasis[i], maskDcd[i])
		evalPfOut.Value.Add(evalPfOut.Value, prodBuf)
	}
	evalPfOut.Value.Mod(evalPfOut.Value, p.Parameters.modulus)
}

// EvaluateParallel evaluates pBig at x with proof in parallel.
func (p *Prover) EvaluateParallel(x *big.Int, open Opening) EvaluationProof {
	evalPfOut := NewEvaluationProof(p.Parameters)
	p.EvaluateParallelAssign(x, open, evalPfOut)
	return evalPfOut
}

// EvaluateParallelAssign evaluates pBig at x with proof and assigns it to evalPfOut in parallel.
func (p *Prover) EvaluateParallelAssign(x *big.Int, open Opening, evalPfOut EvaluationProof) {
	commitCount := len(open.Mask) - 2

	xEcd := p.Encoder.Encode([]*big.Int{big.NewInt(0).Mod(x, p.Parameters.modulus)})
	xPowBuf, xPowSkip := big.NewInt(1), big.NewInt(0).Exp(x, big.NewInt(int64(p.Parameters.bigIntCommitSize)), p.Parameters.modulus)
	xPowEcd := make([]ring.Poly, commitCount)
	for i := 0; i < commitCount; i++ {
		xPowEcd[i] = p.Encoder.Encode([]*big.Int{xPowBuf})
		xPowBuf.Mul(xPowBuf, xPowSkip)
		xPowBuf.Mod(xPowBuf, p.Parameters.modulus)
	}

	var wg sync.WaitGroup
	wg.Add(p.Parameters.polyCommitSize + p.Parameters.ajtaiRandSize)

	for i := 0; i < p.Parameters.polyCommitSize; i++ {
		go func(i int) {
			evalPfOut.Mask[i].Copy(open.Mask[commitCount+1][i])
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Mask[commitCount][i], evalPfOut.Mask[i])
			for j := 0; j < commitCount; j++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Mask[j][i], evalPfOut.Mask[i])
			}
			wg.Done()
		}(i)
	}

	for i := 0; i < p.Parameters.ajtaiRandSize; i++ {
		go func(i int) {
			evalPfOut.Rand[i].Copy(open.Rand[commitCount+1][i])
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Rand[commitCount][i], evalPfOut.Rand[i])
			for j := 0; j < commitCount; j++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Rand[j][i], evalPfOut.Rand[i])
			}
			wg.Done()
		}(i)
	}

	xPowBasis := make([]*big.Int, p.Parameters.bigIntCommitSize)
	xPowBasis[0] = big.NewInt(1)
	for i := 1; i < p.Parameters.bigIntCommitSize; i++ {
		xPowBasis[i] = big.NewInt(0).Mul(xPowBasis[i-1], x)
		xPowBasis[i].Mod(xPowBasis[i], p.Parameters.modulus)
	}

	maskDcd := p.Encoder.DecodeChunk(evalPfOut.Mask)
	evalPfOut.Value.SetInt64(0)
	prodBuf := big.NewInt(0)
	for i := 0; i < p.Parameters.bigIntCommitSize; i++ {
		prodBuf.Mul(xPowBasis[i], maskDcd[i])
		evalPfOut.Value.Add(evalPfOut.Value, prodBuf)
	}
	evalPfOut.Value.Mod(evalPfOut.Value, p.Parameters.modulus)
}
