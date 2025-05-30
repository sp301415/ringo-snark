package celpc

import (
	"math"
	"math/big"
	"runtime"
	"sync"

	"github.com/sp301415/ringo-snark/bigring"
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

	buffer proverBuffer
}

type proverBuffer struct {
	expBuf *big.Int

	bigBlind      []*big.Int
	bigBlindShift []*big.Int

	bigMask   []*big.Int
	challenge ring.Poly

	xEcd    ring.Poly
	xPowEcd ring.Poly

	xPow     *big.Int
	xPowSkip *big.Int

	xPowBasis []*big.Int
	maskDcd   []*big.Int
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

		buffer: newProverBuffer(params),
	}
}

// newProverBuffer creates a new proverBuffer.
func newProverBuffer(params Parameters) proverBuffer {
	bigBlind := make([]*big.Int, params.bigIntCommitSize)
	bigBlindShift := make([]*big.Int, params.bigIntCommitSize)

	bigMask := make([]*big.Int, params.bigIntCommitSize)

	xPowBasis := make([]*big.Int, params.bigIntCommitSize)
	maskDcd := make([]*big.Int, params.bigIntCommitSize)

	for i := 0; i < params.bigIntCommitSize; i++ {
		bigBlind[i] = big.NewInt(0).Set(params.modulus)
		bigBlindShift[i] = big.NewInt(0).Set(params.modulus)

		bigMask[i] = big.NewInt(0).Set(params.modulus)

		xPowBasis[i] = big.NewInt(0).Set(params.modulus)
		maskDcd[i] = big.NewInt(0).Set(params.modulus)
	}

	return proverBuffer{
		expBuf: big.NewInt(0).Set(params.modulus),

		bigBlind:      bigBlind,
		bigBlindShift: bigBlindShift,

		bigMask:   bigMask,
		challenge: params.ringQ.NewPoly(),

		xEcd:    params.ringQ.NewPoly(),
		xPowEcd: params.ringQ.NewPoly(),

		xPow:     big.NewInt(0).Set(params.modulus),
		xPowSkip: big.NewInt(0).Set(params.modulus),

		xPowBasis: xPowBasis,
		maskDcd:   maskDcd,
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

		buffer: newProverBuffer(p.Parameters),
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

	p.buffer.bigBlind[p.Parameters.bigIntCommitSize-1].SetUint64(0)
	p.buffer.bigBlindShift[0].SetUint64(0)
	for i := 0; i < p.Parameters.bigIntCommitSize-1; i++ {
		p.UniformSampler.SampleModAssign(p.buffer.bigBlind[i])
		p.buffer.bigBlindShift[i+1].Sub(p.Parameters.modulus, p.buffer.bigBlind[i])
	}

	p.CommitEncoder.RandomEncodeChunkAssign(p.buffer.bigBlind, openOut.Mask[commitCount])
	for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
		p.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[commitCount][j])
	}
	p.Commiter.CommitAssign(openOut.Mask[commitCount], openOut.Rand[commitCount], comOut.Value[commitCount])

	blindStdDev := math.Sqrt(float64(commitCount+2)) * p.Parameters.blindStdDev
	blindRandStdDev := math.Sqrt(float64(commitCount+2)) * p.Parameters.blindRandStdDev
	p.Encoder.RandomEncodeChunkAssign(p.buffer.bigBlindShift, blindStdDev, openOut.Mask[commitCount+1])
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

	bigBlind := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlindShift := make([]*big.Int, p.Parameters.bigIntCommitSize)
	bigBlind[p.Parameters.bigIntCommitSize-1] = big.NewInt(0)
	bigBlindShift[0] = big.NewInt(0)
	for i := 0; i < p.Parameters.bigIntCommitSize-1; i++ {
		bigBlind[i] = p.UniformSampler.SampleMod()
		bigBlindShift[i+1] = big.NewInt(0).Sub(p.Parameters.modulus, bigBlind[i])
	}

	workSize := min(runtime.NumCPU(), commitCount+2)

	proverPool := make([]*Prover, workSize)
	for i := 0; i < workSize; i++ {
		proverPool[i] = p.ShallowCopy()
	}

	jobs := make(chan int)
	go func() {
		defer close(jobs)
		for i := 0; i < commitCount+2; i++ {
			jobs <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	for i := 0; i < workSize; i++ {
		go func(i int) {
			defer wg.Done()
			pIdx := proverPool[i]

			for i := range jobs {
				switch {
				case i < commitCount:
					pBigChunk := pBig.Coeffs[i*pIdx.Parameters.bigIntCommitSize : (i+1)*pIdx.Parameters.bigIntCommitSize]
					pIdx.CommitEncoder.RandomEncodeChunkAssign(pBigChunk, openOut.Mask[i])
					for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
						pIdx.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[i][j])
					}
					pIdx.Commiter.CommitAssign(openOut.Mask[i], openOut.Rand[i], comOut.Value[i])

				case i == commitCount:
					pIdx.CommitEncoder.RandomEncodeChunkAssign(bigBlind, openOut.Mask[commitCount])
					for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
						pIdx.CommitRandSampler.SamplePolyAssign(0, openOut.Rand[commitCount][j])
					}
					pIdx.Commiter.CommitAssign(openOut.Mask[commitCount], openOut.Rand[commitCount], comOut.Value[commitCount])

				case i == commitCount+1:
					blindStdDev := math.Sqrt(float64(commitCount+2)) * pIdx.Parameters.blindStdDev
					blindRandStdDev := math.Sqrt(float64(commitCount+2)) * pIdx.Parameters.blindRandStdDev

					pIdx.Encoder.RandomEncodeChunkAssign(bigBlindShift, blindStdDev, openOut.Mask[commitCount+1])
					for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
						pIdx.GaussianSampler.SamplePolyAssign(0, blindRandStdDev, openOut.Rand[commitCount+1][j])
					}
					pIdx.Commiter.CommitAssign(openOut.Mask[commitCount+1], openOut.Rand[commitCount+1], comOut.Value[commitCount+1])

				}
			}
		}(i)
	}

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

	batchMask := make([][]ring.Poly, 0)
	batchRand := make([][]ring.Poly, 0)
	for i := 0; i < len(openVec); i++ {
		batchMask = append(batchMask, openVec[i].Mask[:len(openVec[i].Mask)-1]...)
		batchRand = append(batchRand, openVec[i].Rand[:len(openVec[i].Rand)-1]...)
	}
	batchCount := len(batchMask)

	openingProofStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofStdDev
	openingProofRandStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofRandStdDev
	for i := 0; i < p.Parameters.Repetition(); i++ {
		for j := 0; j < p.Parameters.bigIntCommitSize; j++ {
			p.UniformSampler.SampleModAssign(p.buffer.bigMask[j])
		}
		p.Encoder.RandomEncodeChunkAssign(p.buffer.bigMask, openingProofStdDev, openPfOut.ResponseMask[i])
		for j := 0; j < p.Parameters.ajtaiRandSize; j++ {
			p.GaussianSampler.SamplePolyAssign(0, openingProofRandStdDev, openPfOut.ResponseRand[i][j])
		}
		p.Commiter.CommitAssign(openPfOut.ResponseMask[i], openPfOut.ResponseRand[i], openPfOut.Commitment[i])
	}

	for i := 0; i < p.Parameters.Repetition(); i++ {
		p.Oracle.WriteAjtaiCommitment(openPfOut.Commitment[i])
	}
	p.Oracle.Finalize()

	for i := 0; i < p.Parameters.Repetition(); i++ {
		for j := 0; j < batchCount; j++ {
			p.Oracle.SampleMonomialAssign(p.buffer.challenge)
			for k := 0; k < p.Parameters.polyCommitSize; k++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.challenge, batchMask[j][k], openPfOut.ResponseMask[i][k])
			}
			for k := 0; k < p.Parameters.ajtaiRandSize; k++ {
				p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.challenge, batchRand[j][k], openPfOut.ResponseRand[i][k])
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

	batchMask := make([][]ring.Poly, 0)
	batchRand := make([][]ring.Poly, 0)
	for i := 0; i < len(openVec); i++ {
		batchMask = append(batchMask, openVec[i].Mask[:len(openVec[i].Mask)-1]...)
		batchRand = append(batchRand, openVec[i].Rand[:len(openVec[i].Rand)-1]...)
	}
	batchCount := len(batchMask)

	openingProofStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofStdDev
	openingProofRandStdDev := math.Sqrt(float64(batchCount+1)) * p.Parameters.openingProofRandStdDev

	workSizeFirstMove := min(runtime.NumCPU(), p.Parameters.Repetition())

	proverPool := make([]*Prover, workSizeFirstMove)
	for i := 0; i < workSizeFirstMove; i++ {
		proverPool[i] = p.ShallowCopy()
	}

	jobsFirstMove := make(chan int)
	go func() {
		defer close(jobsFirstMove)
		for i := 0; i < p.Parameters.Repetition(); i++ {
			jobsFirstMove <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSizeFirstMove)

	for i := 0; i < workSizeFirstMove; i++ {
		go func(i int) {
			defer wg.Done()
			pIdx := proverPool[i]

			for i := range jobsFirstMove {
				bigMask := make([]*big.Int, pIdx.Parameters.bigIntCommitSize)
				for i := 0; i < pIdx.Parameters.bigIntCommitSize; i++ {
					bigMask[i] = pIdx.UniformSampler.SampleMod()
				}
				pIdx.Encoder.RandomEncodeChunkAssign(bigMask, openingProofStdDev, openPfOut.ResponseMask[i])
				for j := 0; j < pIdx.Parameters.ajtaiRandSize; j++ {
					pIdx.GaussianSampler.SamplePolyAssign(0, openingProofRandStdDev, openPfOut.ResponseRand[i][j])
				}
				pIdx.Commiter.CommitAssign(openPfOut.ResponseMask[i], openPfOut.ResponseRand[i], openPfOut.Commitment[i])
			}
		}(i)
	}

	wg.Wait()

	for i := 0; i < p.Parameters.Repetition(); i++ {
		p.Oracle.WriteAjtaiCommitment(openPfOut.Commitment[i])
	}
	p.Oracle.Finalize()

	challenge := make([][]ring.Poly, p.Parameters.Repetition())
	for i := 0; i < p.Parameters.Repetition(); i++ {
		challenge[i] = make([]ring.Poly, batchCount)
		for j := 0; j < batchCount; j++ {
			challenge[i][j] = p.Parameters.ringQ.NewPoly()
			p.Oracle.SampleMonomialAssign(challenge[i][j])
		}
	}

	workSizeSecondMove := min(runtime.NumCPU(), p.Parameters.Repetition()*(p.Parameters.polyCommitSize+p.Parameters.ajtaiRandSize))

	jobsSecondMove := make(chan [2]int)
	go func() {
		defer close(jobsSecondMove)
		for i := 0; i < p.Parameters.Repetition(); i++ {
			for k := 0; k < p.Parameters.polyCommitSize+p.Parameters.ajtaiRandSize; k++ {
				jobsSecondMove <- [2]int{i, k}
			}
		}
	}()

	wg.Add(workSizeSecondMove)

	for i := 0; i < workSizeSecondMove; i++ {
		go func() {
			defer wg.Done()
			for idx := range jobsSecondMove {
				i, k := idx[0], idx[1]
				switch {
				case k < p.Parameters.polyCommitSize:
					for j := 0; j < batchCount; j++ {
						p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchMask[j][k], openPfOut.ResponseMask[i][k])
					}

				case k >= p.Parameters.polyCommitSize:
					k -= p.Parameters.polyCommitSize
					for j := 0; j < batchCount; j++ {
						p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(challenge[i][j], batchRand[j][k], openPfOut.ResponseRand[i][k])
					}
				}
			}
		}()
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

	p.buffer.xPow.Mod(x, p.Parameters.modulus)
	p.Encoder.EncodeAssign([]*big.Int{p.buffer.xPow}, p.buffer.xEcd)

	p.buffer.xPowSkip.Exp(x, p.buffer.expBuf.SetUint64(uint64(p.Parameters.bigIntCommitSize)), p.Parameters.modulus)
	p.buffer.xPow.SetUint64(1)

	for i := 0; i < p.Parameters.polyCommitSize; i++ {
		evalPfOut.Mask[i].Copy(open.Mask[commitCount+1][i])
		p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.xEcd, open.Mask[commitCount][i], evalPfOut.Mask[i])
	}

	for i := 0; i < p.Parameters.ajtaiRandSize; i++ {
		evalPfOut.Rand[i].Copy(open.Rand[commitCount+1][i])
		p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.xEcd, open.Rand[commitCount][i], evalPfOut.Rand[i])
	}

	for j := 0; j < commitCount; j++ {
		p.Encoder.EncodeAssign([]*big.Int{p.buffer.xPow}, p.buffer.xPowEcd)
		p.buffer.xPow.Mul(p.buffer.xPow, p.buffer.xPowSkip)
		p.buffer.xPow.Mod(p.buffer.xPow, p.Parameters.modulus)

		for i := 0; i < p.Parameters.polyCommitSize; i++ {
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.xPowEcd, open.Mask[j][i], evalPfOut.Mask[i])
		}

		for i := 0; i < p.Parameters.ajtaiRandSize; i++ {
			p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(p.buffer.xPowEcd, open.Rand[j][i], evalPfOut.Rand[i])
		}
	}

	p.buffer.xPowBasis[0].SetUint64(1)
	for i := 1; i < p.Parameters.bigIntCommitSize; i++ {
		p.buffer.xPowBasis[i].Mul(p.buffer.xPowBasis[i-1], x)
		p.buffer.xPowBasis[i].Mod(p.buffer.xPowBasis[i], p.Parameters.modulus)
	}

	p.Encoder.DecodeChunkAssign(evalPfOut.Mask, p.buffer.maskDcd)

	evalPfOut.Value.SetUint64(0)
	for i := 0; i < p.Parameters.bigIntCommitSize; i++ {
		p.buffer.xPow.Mul(p.buffer.xPowBasis[i], p.buffer.maskDcd[i])
		evalPfOut.Value.Add(evalPfOut.Value, p.buffer.xPow)
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

	workSize := min(runtime.NumCPU(), p.Parameters.polyCommitSize+p.Parameters.ajtaiRandSize)

	jobs := make(chan int)
	go func() {
		defer close(jobs)
		for i := 0; i < p.Parameters.polyCommitSize+p.Parameters.ajtaiRandSize; i++ {
			jobs <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	for i := 0; i < workSize; i++ {
		go func() {
			defer wg.Done()
			for i := range jobs {
				switch {
				case i < p.Parameters.polyCommitSize:
					evalPfOut.Mask[i].Copy(open.Mask[commitCount+1][i])
					p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Mask[commitCount][i], evalPfOut.Mask[i])
					for j := 0; j < commitCount; j++ {
						p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Mask[j][i], evalPfOut.Mask[i])
					}

				case i >= p.Parameters.polyCommitSize:
					i -= p.Parameters.polyCommitSize
					evalPfOut.Rand[i].Copy(open.Rand[commitCount+1][i])
					p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xEcd, open.Rand[commitCount][i], evalPfOut.Rand[i])
					for j := 0; j < commitCount; j++ {
						p.Parameters.ringQ.MulCoeffsMontgomeryThenAdd(xPowEcd[j], open.Rand[j][i], evalPfOut.Rand[i])
					}
				}
			}
		}()
	}

	wg.Wait()

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
