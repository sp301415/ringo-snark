package buckler

import (
	"fmt"
	"math"
	"math/big"
	"reflect"
	"runtime"
	"sync"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
)

func (p *Prover) ProveParallel(ck celpc.AjtaiCommitKey, c Circuit) (Proof, error) {
	p.oracle.Reset()
	p.polyProver.Commiter = celpc.NewAjtaiCommiter(p.Parameters, ck)
	witnessData := p.newWitnessData()

	if p.ctx.circuitType != reflect.TypeOf(c).Elem() {
		return Proof{}, fmt.Errorf("circuit type mismatch")
	}

	wk := &walker{}
	if err := wk.walkForProve(p, reflect.ValueOf(c), witnessData.publicWitnesses, witnessData.witnesses); err != nil {
		return Proof{}, err
	}

	for wID, wDcmpIDs := range p.ctx.InfDecomposedWitness {
		for i := 0; i < p.Parameters.Degree(); i++ {
			p.bigSignedDecomposeAssign(witnessData.witnesses[wID][i], p.buffer.infDcmpBase[wID], p.buffer.infDcmp[wID])
			for j, wDcmpID := range wDcmpIDs {
				witnessData.witnesses[wDcmpID[0].Int64()][i].Set(p.buffer.infDcmp[wID][j])
			}
		}
	}

	for wID := range p.ctx.TwoDecomposeBound {
		pwBaseID := p.ctx.TwoDecomposeBase[wID][0].Int64()
		pwMaskID := p.ctx.TwoDecomposeMask[wID][0].Int64()
		for i := range p.buffer.twoDcmpBase[wID] {
			witnessData.publicWitnesses[pwBaseID][i].Set(p.buffer.twoDcmpBase[wID][i])
			witnessData.publicWitnesses[pwMaskID][i].SetInt64(1)
		}

		p.buffer.sqNorm.SetUint64(0)
		for i := 0; i < p.Parameters.Degree(); i++ {
			p.buffer.sqNormSum.Mul(witnessData.witnesses[wID][i], witnessData.witnesses[wID][i])
			p.buffer.sqNorm.Add(p.buffer.sqNorm, p.buffer.sqNormSum)
		}
		wDcmpID := p.ctx.TwoDecomposedWitness[wID][0].Int64()
		p.bigSignedDecomposeAssign(p.buffer.sqNorm, p.buffer.twoDcmpBase[wID], witnessData.witnesses[wDcmpID][:len(p.buffer.twoDcmpBase[wID])])
	}

	commitWorkSize := min(runtime.NumCPU(), int(p.ctx.publicWitnessCount+p.ctx.witnessCount))
	encoderPool := make([]*Encoder, commitWorkSize)
	ringQPool := make([]*bigring.BigRing, commitWorkSize)
	polyProverPool := make([]*celpc.Prover, commitWorkSize)
	for i := 0; i < commitWorkSize; i++ {
		encoderPool[i] = p.encoder.ShallowCopy()
		ringQPool[i] = p.ringQ.ShallowCopy()
		polyProverPool[i] = p.polyProver.ShallowCopy()
	}

	type commitJob struct {
		idx      int
		isPublic bool
	}

	commitJobChan := make(chan commitJob)
	go func() {
		defer close(commitJobChan)
		for i := range witnessData.witnesses {
			commitJobChan <- commitJob{
				idx:      i,
				isPublic: false,
			}
		}
		for i := range witnessData.publicWitnesses {
			commitJobChan <- commitJob{
				idx:      i,
				isPublic: true,
			}
		}
	}()

	var wg sync.WaitGroup
	wg.Add(commitWorkSize)

	witnessCommitDeg := p.Parameters.Degree() + p.Parameters.BigIntCommitSize()
	commitments := make([]celpc.Commitment, p.ctx.witnessCount)
	openings := make([]celpc.Opening, p.ctx.witnessCount)
	for i := 0; i < commitWorkSize; i++ {
		go func(idx int) {
			defer wg.Done()

			pEcd := p.ringQ.NewPoly()
			encoder := encoderPool[idx]
			ringQ := ringQPool[idx]
			polyProver := polyProverPool[idx]

			for job := range commitJobChan {
				i := job.idx
				if job.isPublic {
					encoder.EncodeAssign(witnessData.publicWitnesses[i], pEcd)
					ringQ.ToNTTPolyAssign(pEcd, witnessData.publicWitnessEncodings[i])
				} else {
					encoder.RandomEncodeAssign(witnessData.witnesses[i], pEcd)
					ringQ.ToNTTPolyAssign(pEcd, witnessData.witnessEncodings[i])

					commitments[i], openings[i] = polyProver.CommitParallel(bigring.BigPoly{Coeffs: pEcd.Coeffs[:witnessCommitDeg]})
				}
			}
		}(i)
	}

	wg.Wait()

	openingProof := p.polyProver.ProveOpeningParallel(commitments, openings)

	for i := range commitments {
		p.oracle.WriteCommitment(commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)

	rowCheckProver := &Prover{
		Parameters: p.Parameters,

		ringQ: p.ringQ.ShallowCopy(),

		polyProver: p.polyProver.ShallowCopy(),

		ctx: p.ctx,

		rowCheckBuffer: newRowCheckBuffer(p.Parameters, p.ringQ, p.ctx),
	}

	linCheckProver := &Prover{
		Parameters: p.Parameters,

		ringQ: p.ringQ.ShallowCopy(),

		encoder:    p.encoder.ShallowCopy(),
		polyProver: p.polyProver.ShallowCopy(),

		ctx: p.ctx,

		buffer:         p.buffer,
		linCheckBuffer: newLinCheckBuffer(p.Parameters, p.ringQ, p.ctx),
	}

	sumCheckProver := &Prover{
		Parameters: p.Parameters,

		ringQ: p.ringQ.ShallowCopy(),

		encoder:    p.encoder.ShallowCopy(),
		polyProver: p.polyProver.ShallowCopy(),

		ctx: p.ctx,

		sumCheckBuffer: newSumCheckBuffer(p.Parameters, p.ringQ, p.ctx),
	}

	wg.Add(2)

	var linCheckMaskCommit SumCheckMaskCommitment
	var linCheckMask sumCheckMask
	go func() {
		defer wg.Done()
		if p.ctx.HasLinCheck() {
			linCheckMaskCommit, linCheckMask = linCheckProver.sumCheckMaskParallel(2 * p.Parameters.Degree())
		}
	}()

	var sumCheckMaskCommit SumCheckMaskCommitment
	var sumCheckMask sumCheckMask
	go func() {
		defer wg.Done()
		if p.ctx.HasSumCheck() {
			sumCheckMaskCommit, sumCheckMask = sumCheckProver.sumCheckMaskParallel(p.ctx.maxDegree)
		}
	}()

	wg.Wait()

	if p.ctx.HasLinCheck() {
		p.oracle.WriteCommitment(linCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(linCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(linCheckMaskCommit.MaskSum)
	}

	if p.ctx.HasSumCheck() {
		p.oracle.WriteCommitment(sumCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(sumCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(sumCheckMaskCommit.MaskSum)
	}

	p.oracle.Finalize()

	if p.ctx.HasRowCheck() {
		p.oracle.SampleModAssign(rowCheckProver.rowCheckBuffer.batchConstPow[0])
		for i := 1; i < len(rowCheckProver.rowCheckBuffer.batchConstPow); i++ {
			rowCheckProver.rowCheckBuffer.batchConstPow[i].Mul(rowCheckProver.rowCheckBuffer.batchConstPow[i-1], rowCheckProver.rowCheckBuffer.batchConstPow[0])
			rowCheckProver.rowCheckBuffer.batchConstPow[i].Mod(rowCheckProver.rowCheckBuffer.batchConstPow[i], p.Parameters.Modulus())
		}
	}

	if p.ctx.HasLinCheck() {
		p.oracle.SampleModAssign(linCheckProver.linCheckBuffer.batchConstPow[0])
		for i := 1; i < len(linCheckProver.linCheckBuffer.batchConstPow); i++ {
			linCheckProver.linCheckBuffer.batchConstPow[i].Mul(linCheckProver.linCheckBuffer.batchConstPow[i-1], linCheckProver.linCheckBuffer.batchConstPow[0])
			linCheckProver.linCheckBuffer.batchConstPow[i].Mod(linCheckProver.linCheckBuffer.batchConstPow[i], p.Parameters.Modulus())
		}

		p.oracle.SampleModAssign(linCheckProver.linCheckBuffer.linCheckVec[0])
		for i := 1; i < len(linCheckProver.linCheckBuffer.linCheckVec); i++ {
			linCheckProver.linCheckBuffer.linCheckVec[i].Mul(linCheckProver.linCheckBuffer.linCheckVec[i-1], linCheckProver.linCheckBuffer.linCheckVec[0])
			linCheckProver.linCheckBuffer.linCheckVec[i].Mod(linCheckProver.linCheckBuffer.linCheckVec[i], p.Parameters.Modulus())
		}
	}

	if p.ctx.HasSumCheck() {
		p.oracle.SampleModAssign(sumCheckProver.sumCheckBuffer.batchConstPow[0])
		for i := 1; i < len(sumCheckProver.sumCheckBuffer.batchConstPow); i++ {
			sumCheckProver.sumCheckBuffer.batchConstPow[i].Mul(sumCheckProver.sumCheckBuffer.batchConstPow[i-1], sumCheckProver.sumCheckBuffer.batchConstPow[0])
			sumCheckProver.sumCheckBuffer.batchConstPow[i].Mod(sumCheckProver.sumCheckBuffer.batchConstPow[i], p.Parameters.Modulus())
		}
	}

	wg.Add(3)

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpen rowCheckOpening
	go func() {
		defer wg.Done()
		if p.ctx.HasRowCheck() {
			rowCheckCommit, rowCheckOpen = rowCheckProver.rowCheckParallel(rowCheckProver.rowCheckBuffer.batchConstPow, witnessData)
		}
	}()

	var linCheckCommit SumCheckCommitment
	var linCheckOpen sumCheckOpening
	go func() {
		defer wg.Done()
		if p.ctx.HasLinCheck() {
			linCheckCommit, linCheckOpen = linCheckProver.linCheckParallel(linCheckProver.linCheckBuffer.batchConstPow, linCheckProver.linCheckBuffer.linCheckVec, linCheckMask, witnessData)
		}
	}()

	var sumCheckCommit SumCheckCommitment
	var sumCheckOpen sumCheckOpening
	go func() {
		defer wg.Done()
		if p.ctx.HasSumCheck() {
			sumCheckCommit, sumCheckOpen = sumCheckProver.sumCheckParallel(sumCheckProver.sumCheckBuffer.batchConstPow, sumCheckMask, witnessData)
		}
	}()

	wg.Wait()

	if p.ctx.HasRowCheck() {
		p.oracle.WriteCommitment(rowCheckCommit.QuoCommitment)
		p.oracle.WriteOpeningProof(rowCheckCommit.OpeningProof)
	}

	if p.ctx.HasLinCheck() {
		p.oracle.WriteCommitment(linCheckCommit.QuoCommitment)
		p.oracle.WriteCommitment(linCheckCommit.RemCommitment)
		p.oracle.WriteCommitment(linCheckCommit.RemShiftCommitment)
		p.oracle.WriteOpeningProof(linCheckCommit.OpeningProof)
	}

	if p.ctx.HasSumCheck() {
		p.oracle.WriteCommitment(sumCheckCommit.QuoCommitment)
		p.oracle.WriteCommitment(sumCheckCommit.RemCommitment)
		p.oracle.WriteCommitment(sumCheckCommit.RemShiftCommitment)
		p.oracle.WriteOpeningProof(sumCheckCommit.OpeningProof)
	}

	p.oracle.Finalize()

	p.oracle.SampleModAssign(p.buffer.evalPoint)

	evalWorkSize := min(runtime.NumCPU(), int(p.ctx.witnessCount))
	evalJobChan := make(chan int)
	go func() {
		defer close(evalJobChan)
		for i := 0; i < int(p.ctx.witnessCount); i++ {
			evalJobChan <- i
		}
	}()

	evalProofs := make([]celpc.EvaluationProof, len(commitments))

	wg.Add(evalWorkSize + 3)

	for i := 0; i < evalWorkSize; i++ {
		go func(idx int) {
			defer wg.Done()

			polyProver := polyProverPool[idx]

			for i := range evalJobChan {
				evalProofs[i] = polyProver.EvaluateParallel(p.buffer.evalPoint, openings[i])
			}
		}(i)
	}

	var rowCheckEvalProof RowCheckEvaluationProof
	go func() {
		defer wg.Done()
		if p.ctx.HasRowCheck() {
			rowCheckEvalProof = RowCheckEvaluationProof{
				QuoEvalProof: rowCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, rowCheckOpen.QuoOpening),
			}
		}
	}()

	var linCheckEvalProof SumCheckEvaluationProof
	go func() {
		defer wg.Done()
		if p.ctx.HasLinCheck() {
			linCheckEvalProof = SumCheckEvaluationProof{
				MaskEvalProof:     linCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, linCheckMask.MaskOpening),
				QuoEvalProof:      linCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, linCheckOpen.QuoOpening),
				RemEvalProof:      linCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, linCheckOpen.RemOpening),
				RemShiftEvalProof: linCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, linCheckOpen.RemShiftOpening),
			}
		}
	}()

	var sumCheckEvalProof SumCheckEvaluationProof
	go func() {
		defer wg.Done()
		if p.ctx.HasSumCheck() {
			sumCheckEvalProof = SumCheckEvaluationProof{
				MaskEvalProof:     sumCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, sumCheckMask.MaskOpening),
				QuoEvalProof:      sumCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, sumCheckOpen.QuoOpening),
				RemEvalProof:      sumCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, sumCheckOpen.RemOpening),
				RemShiftEvalProof: sumCheckProver.polyProver.EvaluateParallel(p.buffer.evalPoint, sumCheckOpen.RemShiftOpening),
			}
		}
	}()

	wg.Wait()

	return Proof{
		PublicWitness: witnessData.publicWitnesses,
		Witness:       commitments,
		OpeningProof:  openingProof,

		LinCheckMaskCommitment: linCheckMaskCommit,
		SumCheckMaskCommitment: sumCheckMaskCommit,

		RowCheckCommitment: rowCheckCommit,
		LinCheckCommitment: linCheckCommit,
		SumCheckCommitment: sumCheckCommit,

		EvalProofs:              evalProofs,
		RowCheckEvaluationProof: rowCheckEvalProof,
		LinCheckEvaluationProof: linCheckEvalProof,
		SumCheckEvaluationProof: sumCheckEvalProof,
	}, nil
}

func (p *Prover) evaluateCircuitParallelAssign(batchConstPow []*big.Int, constraints []ArithmeticConstraint, witnessData witnessData, termNTT, evalNTT, batchedNTT bigring.BigNTTPoly, batchedOut bigring.BigPoly) {
	batchedNTT.Clear()

	workSize := min(runtime.NumCPU(), p.ringQ.Degree())

	batchJobs := make(chan int)
	go func() {
		defer close(batchJobs)
		for i := 0; i < p.ringQ.Degree(); i++ {
			batchJobs <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	for i := 0; i < workSize; i++ {
		go func() {
			defer wg.Done()

			for k := range batchJobs {
				for c, constraint := range constraints {
					evalNTT.Coeffs[k].SetInt64(0)
					for i := range constraint.witness {
						termNTT.Coeffs[k].Set(constraint.coeffsBig[i])

						if constraint.coeffsPublicWitness[i] != -1 {
							termNTT.Coeffs[k].Mul(termNTT.Coeffs[k], witnessData.publicWitnessEncodings[constraint.coeffsPublicWitness[i]].Coeffs[k])
							termNTT.Coeffs[k].Mod(termNTT.Coeffs[k], p.Parameters.Modulus())
						}

						for j := range constraint.witness[i] {
							termNTT.Coeffs[k].Mul(termNTT.Coeffs[k], witnessData.witnessEncodings[constraint.witness[i][j]].Coeffs[k])
							termNTT.Coeffs[k].Mod(termNTT.Coeffs[k], p.Parameters.Modulus())
						}

						evalNTT.Coeffs[k].Add(evalNTT.Coeffs[k], termNTT.Coeffs[k])
					}
					evalNTT.Coeffs[k].Mul(evalNTT.Coeffs[k], batchConstPow[c])
					batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], evalNTT.Coeffs[k])
					batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())
				}
			}
		}()
	}

	wg.Wait()

	p.ringQ.ToPolyAssign(batchedNTT, batchedOut)
}

func (p *Prover) rowCheckParallel(batchConstPow []*big.Int, witnessData witnessData) (RowCheckCommitment, rowCheckOpening) {
	p.evaluateCircuitParallelAssign(
		batchConstPow, p.ctx.arithConstraints, witnessData,
		p.rowCheckBuffer.termNTT, p.rowCheckBuffer.evalNTT, p.rowCheckBuffer.batchedNTT, p.rowCheckBuffer.batched)
	p.ringQ.QuoRemByVanishingAssign(p.rowCheckBuffer.batched, p.Parameters.Degree(), p.rowCheckBuffer.quo, p.rowCheckBuffer.rem)

	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.rowCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel([]celpc.Commitment{com.QuoCommitment}, []celpc.Opening{open.QuoOpening})

	return com, open
}

func (p *Prover) sumCheckMaskParallel(maskDeg int) (SumCheckMaskCommitment, sumCheckMask) {
	var com SumCheckMaskCommitment
	var open sumCheckMask

	open.Mask = p.ringQ.NewPoly()
	for i := 0; i < p.Parameters.Degree(); i++ {
		p.encoder.UniformSampler.SampleModAssign(open.Mask.Coeffs[i])
	}
	com.MaskSum = big.NewInt(0).Set(open.Mask.Coeffs[0])
	for i := p.Parameters.Degree(); i < maskDeg; i++ {
		p.encoder.UniformSampler.SampleModAssign(open.Mask.Coeffs[i])
		open.Mask.Coeffs[i-p.Parameters.Degree()].Sub(open.Mask.Coeffs[i-p.Parameters.Degree()], open.Mask.Coeffs[i])
		if open.Mask.Coeffs[i-p.Parameters.Degree()].Sign() < 0 {
			open.Mask.Coeffs[i-p.Parameters.Degree()].Add(open.Mask.Coeffs[i-p.Parameters.Degree()], p.Parameters.Modulus())
		}
	}

	maskCommitDeg := int(math.Ceil(float64(maskDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
	com.MaskCommitment, open.MaskOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: open.Mask.Coeffs[:maskCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel([]celpc.Commitment{com.MaskCommitment}, []celpc.Opening{open.MaskOpening})

	return com, open
}

func (p *Prover) linCheckParallel(batchConstPow []*big.Int, linCheckVec []*big.Int, linCheckMask sumCheckMask, witnessData witnessData) (SumCheckCommitment, sumCheckOpening) {
	p.encoder.EncodeAssign(linCheckVec, p.buffer.pEcd)
	p.ringQ.ToNTTPolyAssign(p.buffer.pEcd, p.linCheckBuffer.linCheckVecEcdNTT)

	lincheckVecTransEcdNTTs := make([]bigring.BigNTTPoly, len(p.ctx.linTransformers))
	for i, transformer := range p.ctx.linTransformers {
		transformer.TransformAssign(linCheckVec, p.linCheckBuffer.linCheckVecTrans)
		p.encoder.EncodeAssign(p.linCheckBuffer.linCheckVecTrans, p.buffer.pEcd)
		lincheckVecTransEcdNTTs[i] = p.ringQ.ToNTTPoly(p.buffer.pEcd)
	}

	p.linCheckBuffer.batchedNTT.Clear()

	workSize := min(runtime.NumCPU(), p.ringQ.Degree())
	batchJobs := make(chan int)
	go func() {
		defer close(batchJobs)
		for i := 0; i < p.ringQ.Degree(); i++ {
			batchJobs <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	for i := 0; i < workSize; i++ {
		go func() {
			defer wg.Done()

			for k := range batchJobs {
				powIdx := 0
				for t, transformer := range p.ctx.linTransformers {
					for i := range p.ctx.linCheckConstraints[transformer] {
						wEcdIn := witnessData.witnessEncodings[p.ctx.linCheckConstraints[transformer][i][0]]
						wEcdOut := witnessData.witnessEncodings[p.ctx.linCheckConstraints[transformer][i][1]]

						p.linCheckBuffer.evalNTT.Coeffs[k].Mul(wEcdIn.Coeffs[k], lincheckVecTransEcdNTTs[t].Coeffs[k])
						p.buffer.pEcdNTT.Coeffs[k].Mul(wEcdOut.Coeffs[k], p.linCheckBuffer.linCheckVecEcdNTT.Coeffs[k])
						p.linCheckBuffer.evalNTT.Coeffs[k].Sub(p.linCheckBuffer.evalNTT.Coeffs[k], p.buffer.pEcdNTT.Coeffs[k])
						p.linCheckBuffer.evalNTT.Coeffs[k].Mod(p.linCheckBuffer.evalNTT.Coeffs[k], p.Parameters.Modulus())

						p.linCheckBuffer.evalNTT.Coeffs[k].Mul(p.linCheckBuffer.evalNTT.Coeffs[k], batchConstPow[powIdx])
						p.linCheckBuffer.batchedNTT.Coeffs[k].Add(p.linCheckBuffer.batchedNTT.Coeffs[k], p.linCheckBuffer.evalNTT.Coeffs[k])
						p.linCheckBuffer.batchedNTT.Coeffs[k].Mod(p.linCheckBuffer.batchedNTT.Coeffs[k], p.Parameters.Modulus())

						powIdx++
					}
				}
			}
		}()
	}

	wg.Wait()

	p.ringQ.ToPolyAssign(p.linCheckBuffer.batchedNTT, p.linCheckBuffer.batched)
	p.ringQ.AddAssign(p.linCheckBuffer.batched, linCheckMask.Mask, p.linCheckBuffer.batched)

	p.ringQ.QuoRemByVanishingAssign(p.linCheckBuffer.batched, p.Parameters.Degree(), p.linCheckBuffer.quo, p.linCheckBuffer.remShift)
	p.linCheckBuffer.remShift.Coeffs[0].SetInt64(0)

	quoCommitDeg := p.Parameters.Degree()
	remCommitDeg := p.Parameters.Degree()

	for i, ii := 0, 1; ii < remCommitDeg; i, ii = i+1, ii+1 {
		p.linCheckBuffer.rem.Coeffs[i].Set(p.linCheckBuffer.remShift.Coeffs[ii])
	}
	p.linCheckBuffer.rem.Coeffs[remCommitDeg-1].SetInt64(0)

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.linCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.linCheckBuffer.rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.linCheckBuffer.remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}

func (p *Prover) sumCheckParallel(batchConstPow []*big.Int, sumCheckMask sumCheckMask, witnessData witnessData) (SumCheckCommitment, sumCheckOpening) {
	p.evaluateCircuitParallelAssign(
		batchConstPow, p.ctx.sumCheckConstraints, witnessData,
		p.sumCheckBuffer.termNTT, p.sumCheckBuffer.evalNTT, p.sumCheckBuffer.batchedNTT, p.sumCheckBuffer.batched)
	p.ringQ.AddAssign(p.sumCheckBuffer.batched, sumCheckMask.Mask, p.sumCheckBuffer.batched)

	p.ringQ.QuoRemByVanishingAssign(p.sumCheckBuffer.batched, p.Parameters.Degree(), p.sumCheckBuffer.quo, p.sumCheckBuffer.remShift)
	p.sumCheckBuffer.remShift.Coeffs[0].SetInt64(0)

	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
	remCommitDeg := p.Parameters.Degree()

	for i, ii := 0, 1; ii < remCommitDeg; i, ii = i+1, ii+1 {
		p.sumCheckBuffer.rem.Coeffs[i].Set(p.sumCheckBuffer.remShift.Coeffs[ii])
	}
	p.sumCheckBuffer.rem.Coeffs[remCommitDeg-1].SetInt64(0)

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.sumCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.sumCheckBuffer.rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: p.sumCheckBuffer.remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
