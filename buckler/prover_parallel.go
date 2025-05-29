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

// Prove proves the circuit in given assignment in parallel.
func (p *Prover) ProveParallel(ck celpc.AjtaiCommitKey, c Circuit) (Proof, error) {
	p.oracle.Reset()
	p.polyProver.Commiter = celpc.NewAjtaiCommiter(p.Parameters, ck)
	buf := p.newBuffer()

	if p.ctx.circuitType != reflect.TypeOf(c).Elem() {
		return Proof{}, fmt.Errorf("circuit type mismatch")
	}

	walker := &walker{}
	if err := walker.walkForProve(p, reflect.ValueOf(c), buf.publicWitnesses, buf.witnesses); err != nil {
		return Proof{}, err
	}

	for wID, wDcmpIDs := range p.ctx.InfDecomposedWitness {
		w := buf.witnesses[wID]
		dcmpBound := p.ctx.InfDecomposeBound[wID]
		dcmpBase := getDecomposeBase(dcmpBound)

		wDcmp := make([]Witness, len(dcmpBase))
		for i := 0; i < len(dcmpBase); i++ {
			wDcmp[i] = make(Witness, p.Parameters.Degree())
		}

		for i := 0; i < p.Parameters.Degree(); i++ {
			coeffDcmp := bigSignedDecompose(w[i], p.Parameters.Modulus(), dcmpBase)
			for j := 0; j < len(dcmpBase); j++ {
				wDcmp[j][i] = coeffDcmp[j]
			}
		}

		for i, wDcmpID := range wDcmpIDs {
			buf.witnesses[wDcmpID[0].Int64()] = wDcmp[i]
		}
	}

	for wID := range p.ctx.TwoDecomposeBound {
		dcmpBase := getDecomposeBase(p.ctx.TwoDecomposeBound[wID])

		pwBase := PublicWitness(p.ringQ.NewPoly().Coeffs)
		pwMask := PublicWitness(p.ringQ.NewPoly().Coeffs)
		for i := 0; i < len(dcmpBase); i++ {
			pwBase[i].Set(dcmpBase[i])
			pwMask[i].SetInt64(1)
		}

		pwBaseID := p.ctx.TwoDecomposeBase[wID][0].Int64()
		buf.publicWitnesses[pwBaseID] = pwBase
		pwMaskID := p.ctx.TwoDecomposeMask[wID][0].Int64()
		buf.publicWitnesses[pwMaskID] = pwMask

		w := buf.witnesses[wID]
		wSqNorm, sq := big.NewInt(0), big.NewInt(0)
		for i := 0; i < p.Parameters.Degree(); i++ {
			sq.Mul(w[i], w[i])
			wSqNorm.Add(wSqNorm, sq)
		}

		wSqNormDcmp := bigSignedDecompose(wSqNorm, p.Parameters.Modulus(), dcmpBase)
		wDcmp := Witness(p.ringQ.NewPoly().Coeffs)
		for i := 0; i < len(wSqNormDcmp); i++ {
			wDcmp[i].Set(wSqNormDcmp[i])
		}

		wDcmpID := p.ctx.TwoDecomposedWitness[wID][0].Int64()
		buf.witnesses[wDcmpID] = wDcmp
	}

	workSize := min(runtime.NumCPU(), len(buf.witnesses))
	proverPool := make([]*Prover, workSize)
	for i := 0; i < workSize; i++ {
		proverPool[i] = p.ShallowCopy()
	}

	type commitJob struct {
		idx      int
		isPublic bool
	}
	commitJobs := make(chan commitJob)
	go func() {
		defer close(commitJobs)
		for i := 0; i < len(buf.witnesses); i++ {
			commitJobs <- commitJob{
				idx:      i,
				isPublic: false,
			}
		}
		for i := 0; i < len(buf.publicWitnesses); i++ {
			commitJobs <- commitJob{
				idx:      i,
				isPublic: true,
			}
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	witnessCommitDeg := p.Parameters.Degree() + p.Parameters.BigIntCommitSize()
	for i := 0; i < workSize; i++ {
		go func(i int) {
			defer wg.Done()
			for job := range commitJobs {
				j := job.idx
				if job.isPublic {
					pwEcd := proverPool[i].encoder.Encode(buf.publicWitnesses[j])
					buf.publicWitnessEncodings[j] = p.ringQ.ToNTTPoly(pwEcd)
				} else {
					wEcd := proverPool[i].encoder.RandomEncode(buf.witnesses[j])
					buf.witnessEncodings[j] = p.ringQ.ToNTTPoly(wEcd)

					wCommit := bigring.BigPoly{Coeffs: wEcd.Coeffs[:witnessCommitDeg]}
					buf.commitments[j], buf.openings[j] = proverPool[i].polyProver.CommitParallel(wCommit)
				}
			}
		}(i)
	}

	wg.Wait()

	openingProof := p.polyProver.ProveOpeningParallel(buf.commitments, buf.openings)

	for i := 0; i < len(buf.commitments); i++ {
		p.oracle.WriteCommitment(buf.commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)

	var linCheckMaskCommit SumCheckMaskCommitment
	var linCheckMask sumCheckMask
	if p.ctx.HasLinCheck() {
		linCheckMaskCommit, linCheckMask = p.sumCheckMaskParallel(2 * p.Parameters.Degree())

		p.oracle.WriteCommitment(linCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(linCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(linCheckMaskCommit.MaskSum)
	}

	var sumCheckMaskCommit SumCheckMaskCommitment
	var sumCheckMask sumCheckMask
	if p.ctx.HasSumCheck() {
		sumCheckMaskCommit, sumCheckMask = p.sumCheckMask(p.ctx.maxDegree)

		p.oracle.WriteCommitment(sumCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(sumCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(sumCheckMaskCommit.MaskSum)
	}

	p.oracle.Finalize()

	var batchRowCheckConst *big.Int
	if p.ctx.HasRowCheck() {
		batchRowCheckConst = p.oracle.SampleMod()
	}

	var batchLinConst *big.Int
	var batchLinVec []*big.Int
	if p.ctx.HasLinCheck() {
		batchLinConst = p.oracle.SampleMod()
		batchLinVec = make([]*big.Int, p.Parameters.Degree())
		batchLinVec[0] = p.oracle.SampleMod()
		for i := 1; i < p.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], p.Parameters.Modulus())
		}
	}

	var batchSumCheckConst *big.Int
	if p.ctx.HasSumCheck() {
		batchSumCheckConst = p.oracle.SampleMod()
	}

	if len(proverPool) < 3 {
		proverPool = []*Prover{p.ShallowCopy(), p.ShallowCopy(), p.ShallowCopy()}
	}
	wg.Add(3)

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpening rowCheckOpening
	go func() {
		if p.ctx.HasRowCheck() {
			rowCheckCommit, rowCheckOpening = proverPool[0].rowCheckParallel(batchRowCheckConst, buf)
		}
		wg.Done()
	}()

	var linCheckCommit SumCheckCommitment
	var linCheckOpen sumCheckOpening
	go func() {
		if p.ctx.HasLinCheck() {
			linCheckCommit, linCheckOpen = proverPool[1].linCheckParallel(batchLinConst, batchLinVec, linCheckMask, buf)
		}
		wg.Done()
	}()

	var sumCheckCommit SumCheckCommitment
	var sumCheckOpen sumCheckOpening
	go func() {
		if p.ctx.HasSumCheck() {
			sumCheckCommit, sumCheckOpen = proverPool[2].sumCheckParallel(batchSumCheckConst, sumCheckMask, buf)
		}
		wg.Done()
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

	evaluatePoint := p.oracle.SampleMod()

	evalJobs := make(chan int)
	go func() {
		defer close(evalJobs)
		for i := 0; i < len(buf.commitments); i++ {
			evalJobs <- i
		}
	}()

	wg.Add(workSize)

	evalProofs := make([]celpc.EvaluationProof, len(buf.commitments))
	for i := 0; i < workSize; i++ {
		go func(i int) {
			defer wg.Done()
			for j := range evalJobs {
				evalProofs[j] = proverPool[i].polyProver.EvaluateParallel(evaluatePoint, buf.openings[j])
			}
		}(i)
	}

	wg.Wait()

	var rowCheckEvalProof RowCheckEvaluationProof
	if p.ctx.HasRowCheck() {
		rowCheckEvalProof = RowCheckEvaluationProof{
			QuoEvalProof: p.polyProver.EvaluateParallel(evaluatePoint, rowCheckOpening.QuoOpening),
		}
	}

	var linCheckEvalProof SumCheckEvaluationProof
	if p.ctx.HasLinCheck() {
		linCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.EvaluateParallel(evaluatePoint, linCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.EvaluateParallel(evaluatePoint, linCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.EvaluateParallel(evaluatePoint, linCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.EvaluateParallel(evaluatePoint, linCheckOpen.RemShiftOpening),
		}
	}

	var sumCheckEvalProof SumCheckEvaluationProof
	if p.ctx.HasSumCheck() {
		sumCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.EvaluateParallel(evaluatePoint, sumCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.EvaluateParallel(evaluatePoint, sumCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.EvaluateParallel(evaluatePoint, sumCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.EvaluateParallel(evaluatePoint, sumCheckOpen.RemShiftOpening),
		}
	}

	return Proof{
		PublicWitness: buf.publicWitnesses,
		Witness:       buf.commitments,
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

func (p *Prover) evaluateCircuitParallel(batchConst *big.Int, constraints []ArithmeticConstraint, buf proverBuffer) bigring.BigPoly {
	batchConstsPow := make([]*big.Int, len(constraints))
	batchConstsPow[0] = big.NewInt(0).Set(batchConst)
	for i := 1; i < len(batchConstsPow); i++ {
		batchConstsPow[i] = big.NewInt(0).Mul(batchConstsPow[i-1], batchConst)
		batchConstsPow[i].Mod(batchConstsPow[i], p.Parameters.Modulus())
	}

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

	batchedNTT := p.ringQ.NewNTTPoly()
	for i := 0; i < workSize; i++ {
		go func() {
			defer wg.Done()
			for k := range batchJobs {
				for c, constraint := range constraints {
					constraintEvalNTT := big.NewInt(0)
					termNTT := big.NewInt(0)

					for i := 0; i < len(constraint.witness); i++ {
						termNTT.Set(constraint.coeffsBig[i])

						if constraint.coeffsPublicWitness[i] != -1 {
							pwEcdNTT := buf.publicWitnessEncodings[constraint.coeffsPublicWitness[i]].Coeffs[k]
							termNTT.Mul(termNTT, pwEcdNTT)
							termNTT.Mod(termNTT, p.Parameters.Modulus())
						}

						for j := 0; j < len(constraint.witness[i]); j++ {
							witnessEcdNTT := buf.witnessEncodings[constraint.witness[i][j]].Coeffs[k]
							termNTT.Mul(termNTT, witnessEcdNTT)
							termNTT.Mod(termNTT, p.Parameters.Modulus())
						}

						constraintEvalNTT.Add(constraintEvalNTT, termNTT)
						constraintEvalNTT.Mod(constraintEvalNTT, p.Parameters.Modulus())
					}
					constraintEvalNTT.Mul(constraintEvalNTT, batchConstsPow[c])
					batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], constraintEvalNTT)
					batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())
				}
			}
		}()
	}

	wg.Wait()

	batched := p.ringQ.ToPoly(batchedNTT)
	return batched
}

func (p *Prover) rowCheckParallel(batchConst *big.Int, buf proverBuffer) (RowCheckCommitment, rowCheckOpening) {
	batched := p.evaluateCircuitParallel(batchConst, p.ctx.arithConstraints, buf)

	quo, _ := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
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

func (p *Prover) linCheckParallel(batchConst *big.Int, linCheckVec []*big.Int, linCheckMask sumCheckMask, buf proverBuffer) (SumCheckCommitment, sumCheckOpening) {
	linCheckVecEcd := p.encoder.Encode(linCheckVec)
	linCheckVecEcdNTT := p.ringQ.ToNTTPoly(linCheckVecEcd)

	linCheckTransformedEcdNTTs := make([]bigring.BigNTTPoly, len(p.ctx.linTransformers))
	for i, transformer := range p.ctx.linTransformers {
		linCheckVecTransformed := transformer.TransposeTransform(linCheckVec)
		linCheckVecTransformedEcd := p.encoder.Encode(linCheckVecTransformed)
		linCheckTransformedEcdNTTs[i] = p.ringQ.ToNTTPoly(linCheckVecTransformedEcd)
	}

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

	batchedNTT := p.ringQ.NewNTTPoly()
	for i := 0; i < workSize; i++ {
		go func() {
			defer wg.Done()
			for k := range batchJobs {
				batchConstPow := big.NewInt(0).Set(batchConst)
				constraintEval0, constraintEval1 := big.NewInt(0), big.NewInt(0)
				for t, transformer := range p.ctx.linTransformers {
					for i := range p.ctx.linCheckConstraints[transformer] {
						wEcdIn := buf.witnessEncodings[p.ctx.linCheckConstraints[transformer][i][0]].Coeffs[k]
						wEcdOut := buf.witnessEncodings[p.ctx.linCheckConstraints[transformer][i][1]].Coeffs[k]

						constraintEval0.Mul(wEcdIn, linCheckTransformedEcdNTTs[t].Coeffs[k])
						constraintEval1.Mul(wEcdOut, linCheckVecEcdNTT.Coeffs[k])
						constraintEval0.Sub(constraintEval0, constraintEval1)
						constraintEval0.Mod(constraintEval0, p.Parameters.Modulus())

						constraintEval0.Mul(constraintEval0, batchConstPow)
						batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], constraintEval0)
						batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())

						batchConstPow.Mul(batchConstPow, batchConst)
						batchConstPow.Mod(batchConstPow, p.Parameters.Modulus())
					}
				}
			}
		}()
	}

	wg.Wait()

	batched := p.ringQ.ToPoly(batchedNTT)
	p.ringQ.AddAssign(batched, linCheckMask.Mask, batched)

	quo, remShift := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	remShift.Coeffs[0].SetInt64(0)

	quoCommitDeg := p.Parameters.Degree()
	remCommitDeg := p.Parameters.Degree()

	rem := p.ringQ.NewPoly()
	for i, ii := 0, 1; ii < remCommitDeg; i, ii = i+1, ii+1 {
		rem.Coeffs[i].Set(remShift.Coeffs[ii])
	}

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}

func (p *Prover) sumCheckParallel(batchConst *big.Int, sumCheckMask sumCheckMask, buf proverBuffer) (SumCheckCommitment, sumCheckOpening) {
	batched := p.evaluateCircuitParallel(batchConst, p.ctx.sumCheckConstraints, buf)
	p.ringQ.AddAssign(batched, sumCheckMask.Mask, batched)

	quo, remShift := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	remShift.Coeffs[0].SetInt64(0)

	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
	remCommitDeg := p.Parameters.Degree()

	rem := p.ringQ.NewPoly()
	for i, ii := 0, 1; ii < remCommitDeg; i, ii = i+1, ii+1 {
		rem.Coeffs[i].Set(remShift.Coeffs[ii])
	}

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
