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
	"github.com/sp301415/ringo-snark/num"
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

	for wID, wDcmpIDs := range p.ctx.decomposedWitness {
		w := buf.witnesses[wID]
		dcmpBound := p.ctx.decomposeBound[wID]
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
		linCheckMaskCommit, linCheckMask = p.linCheckMaskParallel()

		p.oracle.WriteCommitment(linCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(linCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(linCheckMaskCommit.MaskSum)
	}

	p.oracle.Finalize()

	var batchArithConsts map[int]*big.Int
	if p.ctx.HasRowCheck() {
		batchArithConsts = make(map[int]*big.Int)
		for _, constraint := range p.ctx.arithConstraints {
			if _, ok := batchArithConsts[constraint.degree]; !ok {
				batchArithConsts[constraint.degree] = p.oracle.SampleMod()
			}
		}

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

	if len(proverPool) < 2 {
		proverPool = []*Prover{p.ShallowCopy(), p.ShallowCopy()}
	}
	wg.Add(2)

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpening rowCheckOpening
	go func() {
		if p.ctx.HasRowCheck() {
			rowCheckCommit, rowCheckOpening = proverPool[0].rowCheckParallel(batchArithConsts, buf)
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

	return Proof{
		PublicWitness: buf.publicWitnesses,
		Witness:       buf.commitments,
		OpeningProof:  openingProof,

		LinCheckMaskCommitment: linCheckMaskCommit,

		RowCheckCommitment: rowCheckCommit,
		LinCheckCommitment: linCheckCommit,

		EvalProofs:              evalProofs,
		RowCheckEvaluationProof: rowCheckEvalProof,
		LinCheckEvaluationProof: linCheckEvalProof,
	}, nil
}

func (p *Prover) rowCheckParallel(batchConsts map[int]*big.Int, buf proverBuffer) (RowCheckCommitment, rowCheckOpening) {
	batchConstsPowMap := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPowMap[k] = big.NewInt(0).Set(v)
	}

	batchConstsPow := make([]*big.Int, len(p.ctx.arithConstraints))
	for i, constraint := range p.ctx.arithConstraints {
		batchConstsPow[i] = big.NewInt(0).Set(batchConstsPowMap[constraint.degree])
		batchConstsPowMap[constraint.degree].Mul(batchConstsPowMap[constraint.degree], batchConsts[constraint.degree])
		batchConstsPowMap[constraint.degree].Mod(batchConstsPowMap[constraint.degree], p.Parameters.Modulus())
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
				for c, constraint := range p.ctx.arithConstraints {
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

	quo, _ := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel([]celpc.Commitment{com.QuoCommitment}, []celpc.Opening{open.QuoOpening})

	return com, open
}

func (p *Prover) linCheckMaskParallel() (SumCheckMaskCommitment, sumCheckMask) {
	var com SumCheckMaskCommitment
	var open sumCheckMask

	open.Mask = p.ringQ.NewPoly()
	maskDegree := 2 * p.Parameters.Degree()
	for i := 0; i < p.Parameters.Degree(); i++ {
		p.encoder.UniformSampler.SampleModAssign(open.Mask.Coeffs[i])
	}
	com.MaskSum = big.NewInt(0).Set(open.Mask.Coeffs[0])
	for i := p.Parameters.Degree(); i < maskDegree; i++ {
		p.encoder.UniformSampler.SampleModAssign(open.Mask.Coeffs[i])
		open.Mask.Coeffs[i-p.Parameters.Degree()].Sub(open.Mask.Coeffs[i-p.Parameters.Degree()], open.Mask.Coeffs[i])
		if open.Mask.Coeffs[i-p.Parameters.Degree()].Sign() < 0 {
			open.Mask.Coeffs[i-p.Parameters.Degree()].Add(open.Mask.Coeffs[i-p.Parameters.Degree()], p.Parameters.Modulus())
		}
	}

	maskCommitDegree := 2 * p.Parameters.Degree()
	com.MaskCommitment, open.MaskOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: open.Mask.Coeffs[:maskCommitDegree]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel([]celpc.Commitment{com.MaskCommitment}, []celpc.Opening{open.MaskOpening})

	return com, open
}

func (p *Prover) linCheckParallel(batchConst *big.Int, linCheckVec []*big.Int, linCheckMask sumCheckMask, buf proverBuffer) (SumCheckCommitment, sumCheckOpening) {
	linCheckVecEcd := p.encoder.Encode(linCheckVec)
	linCheckVecEcdNTT := p.ringQ.ToNTTPoly(linCheckVecEcd)

	linCheckVecNTTTrans := make([]*big.Int, p.Parameters.Degree())
	for i := 0; i < p.Parameters.Degree(); i++ {
		linCheckVecNTTTrans[i] = big.NewInt(0).Set(linCheckVec[p.Parameters.Degree()-i-1])
	}
	p.baseRingQ.InvNTTInPlace(linCheckVecNTTTrans)
	linCheckVecNTTTransEcd := p.encoder.Encode(linCheckVecNTTTrans)
	linCheckVecNTTTransEcdNTT := p.ringQ.ToNTTPoly(linCheckVecNTTTransEcd)

	linCheckVecAutTransEcdNTT := make([]bigring.BigNTTPoly, len(p.ctx.autConstraints))
	for i := range p.ctx.autConstraints {
		autIdx := p.ctx.autConstraintsIdx[i]
		autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*p.Parameters.Degree())))
		linCheckVecAutTrans := p.baseRingQ.AutomorphismNTT(bigring.BigNTTPoly{Coeffs: linCheckVec}, autIdxInv).Coeffs
		linCheckVecAutTransEcd := p.encoder.Encode(linCheckVecAutTrans)
		linCheckVecAutTransEcdNTT[i] = p.ringQ.ToNTTPoly(linCheckVecAutTransEcd)
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
				for _, nttConstraint := range p.ctx.nttConstraints {
					nttConstraintEvalNTT0 := big.NewInt(0)
					nttConstraintEvalNTT1 := big.NewInt(0)

					wEcdIn := buf.witnessEncodings[nttConstraint[0]].Coeffs[k]
					wEcdOut := buf.witnessEncodings[nttConstraint[1]].Coeffs[k]

					nttConstraintEvalNTT0.Mul(wEcdIn, linCheckVecNTTTransEcdNTT.Coeffs[k])
					nttConstraintEvalNTT1.Mul(wEcdOut, linCheckVecEcdNTT.Coeffs[k])
					nttConstraintEvalNTT0.Sub(nttConstraintEvalNTT0, nttConstraintEvalNTT1)
					nttConstraintEvalNTT0.Mod(nttConstraintEvalNTT0, p.Parameters.Modulus())

					nttConstraintEvalNTT0.Mul(nttConstraintEvalNTT0, batchConstPow)
					batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], nttConstraintEvalNTT0)
					batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())

					batchConstPow.Mul(batchConstPow, batchConst)
					batchConstPow.Mod(batchConstPow, p.Parameters.Modulus())
				}

				for i := range p.ctx.autConstraints {
					for _, autConstraint := range p.ctx.autConstraints[i] {
						autConstraintEvalNTT0 := big.NewInt(0)
						autConstraintEvalNTT1 := big.NewInt(0)

						wEcdIn := buf.witnessEncodings[autConstraint[0]].Coeffs[k]
						wEcdOut := buf.witnessEncodings[autConstraint[1]].Coeffs[k]

						autConstraintEvalNTT0.Mul(wEcdIn, linCheckVecAutTransEcdNTT[i].Coeffs[k])
						autConstraintEvalNTT1.Mul(wEcdOut, linCheckVecEcdNTT.Coeffs[k])
						autConstraintEvalNTT0.Sub(autConstraintEvalNTT0, autConstraintEvalNTT1)
						autConstraintEvalNTT0.Mod(autConstraintEvalNTT0, p.Parameters.Modulus())

						autConstraintEvalNTT0.Mul(autConstraintEvalNTT0, batchConstPow)
						batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], autConstraintEvalNTT0)
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

	quoCommitDegree := p.Parameters.Degree()
	remCommitDegree := p.Parameters.Degree()

	rem := p.ringQ.NewPoly()
	for i, ii := 0, 1; ii < remCommitDegree; i, ii = i+1, ii+1 {
		rem.Coeffs[i].Set(remShift.Coeffs[ii])
	}

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDegree]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDegree]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDegree]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
