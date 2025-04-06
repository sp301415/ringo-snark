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

	for i := 0; i < len(buf.publicWitnesses); i++ {
		pwEcd := p.encoder.Encode(buf.publicWitnesses[i])
		buf.publicWitnessEncodings[i] = p.ringQ.ToNTTPoly(pwEcd)
	}

	for wID, wDcmpIDs := range p.ctx.decomposedWitness {
		w := buf.witnesses[wID]
		dcmpBound := p.ctx.decomposeBound[wID]
		dcmpBase := getDcmpBase(dcmpBound)

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
	encoderPool := make([]*Encoder, workSize)
	polyProverPool := make([]*celpc.Prover, workSize)
	for i := 0; i < workSize; i++ {
		encoderPool[i] = p.encoder.ShallowCopy()
		polyProverPool[i] = p.polyProver.ShallowCopy()
	}

	commitJobs := make(chan int)
	go func() {
		defer close(commitJobs)
		for i := 0; i < len(buf.witnesses); i++ {
			commitJobs <- i
		}
	}()

	var wg sync.WaitGroup
	wg.Add(workSize)

	witnessCommitDeg := p.Parameters.Degree() + p.Parameters.BigIntCommitSize()
	for i := 0; i < workSize; i++ {
		go func(i int) {
			defer wg.Done()
			for j := range commitJobs {
				wEcd := encoderPool[i].RandomEncode(buf.witnesses[j])
				buf.witnessEncodings[j] = p.ringQ.ToNTTPoly(wEcd)

				wCommit := bigring.BigPoly{Coeffs: wEcd.Coeffs[:witnessCommitDeg]}
				buf.commitments[j], buf.openings[j] = polyProverPool[i].CommitParallel(wCommit)
			}
		}(i)
	}

	wg.Wait()
	openingProof := p.polyProver.ProveOpeningParallel(buf.commitments, buf.openings)

	for i := 0; i < len(buf.commitments); i++ {
		p.oracle.WriteCommitment(buf.commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)

	var linCheckMaskCommit LinCheckMaskCommitment
	var linCheckMask linCheckMask
	if p.ctx.HasLinearCheck() {
		linCheckMaskCommit, linCheckMask = p.linCheckMask()

		p.oracle.WriteCommitment(linCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(linCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(linCheckMaskCommit.MaskSum)
	}

	p.oracle.Finalize()

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpening rowCheckOpening
	if p.ctx.HasRowCheck() {
		batchArithConsts := make(map[int]*big.Int)
		for _, constraint := range p.ctx.arithConstraints {
			if _, ok := batchArithConsts[constraint.degree]; !ok {
				batchArithConsts[constraint.degree] = p.oracle.SampleMod()
			}
		}

		rowCheckCommit, rowCheckOpening = p.rowCheckParallel(batchArithConsts, buf)
	}

	var linCheckCommit LinCheckCommitment
	var linCheckOpen linCheckOpening
	if p.ctx.HasLinearCheck() {
		batchLinConst := p.oracle.SampleMod()

		batchLinVec := make([]*big.Int, p.Parameters.Degree())
		batchLinVec[0] = p.oracle.SampleMod()
		for i := 1; i < p.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], p.Parameters.Modulus())
		}

		linCheckCommit, linCheckOpen = p.linCheckParallel(batchLinConst, batchLinVec, linCheckMask, buf)
	}

	if p.ctx.HasRowCheck() {
		p.oracle.WriteCommitment(rowCheckCommit.QuoCommitment)
		p.oracle.WriteOpeningProof(rowCheckCommit.OpeningProof)
	}

	if p.ctx.HasLinearCheck() {
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

	evalProofs := make([]celpc.EvaluationProof, len(buf.commitments))
	wg.Add(workSize)

	for i := 0; i < workSize; i++ {
		go func(i int) {
			defer wg.Done()
			for j := range evalJobs {
				evalProofs[j] = polyProverPool[i].EvaluateParallel(evaluatePoint, buf.openings[j])
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

	var linCheckEvalProof LinCheckEvaluationProof
	if p.ctx.HasLinearCheck() {
		linCheckEvalProof = LinCheckEvaluationProof{
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

func (p *Prover) linCheckParallel(batchConst *big.Int, linCheckVec []*big.Int, linCheckMask linCheckMask, buf proverBuffer) (LinCheckCommitment, linCheckOpening) {
	batchConstPow := make([]*big.Int, len(p.ctx.nttConstraints)+len(p.ctx.autConstraints))
	batchConstPow[0] = big.NewInt(0).Set(batchConst)
	for i := 1; i < len(batchConstPow); i++ {
		batchConstPow[i] = big.NewInt(0).Mul(batchConstPow[i-1], batchConst)
		batchConstPow[i].Mod(batchConstPow[i], p.Parameters.Modulus())
	}

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
				for c, nttConstraint := range p.ctx.nttConstraints {
					nttConstraintEvalNTT0 := big.NewInt(0)
					nttConstraintEvalNTT1 := big.NewInt(0)

					wEcdIn := buf.witnessEncodings[nttConstraint[0]].Coeffs[k]
					wEcdOut := buf.witnessEncodings[nttConstraint[1]].Coeffs[k]

					nttConstraintEvalNTT0.Mul(wEcdIn, linCheckVecNTTTransEcdNTT.Coeffs[k])
					nttConstraintEvalNTT1.Mul(wEcdOut, linCheckVecEcdNTT.Coeffs[k])
					nttConstraintEvalNTT0.Sub(nttConstraintEvalNTT0, nttConstraintEvalNTT1)
					nttConstraintEvalNTT0.Mod(nttConstraintEvalNTT0, p.Parameters.Modulus())

					nttConstraintEvalNTT0.Mul(nttConstraintEvalNTT0, batchConstPow[c])
					batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], nttConstraintEvalNTT0)
					batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())
				}

				for i := range p.ctx.autConstraints {
					for c, autConstraint := range p.ctx.autConstraints[i] {
						autConstraintEvalNTT0 := big.NewInt(0)
						autConstraintEvalNTT1 := big.NewInt(0)

						wEcdIn := buf.witnessEncodings[autConstraint[0]].Coeffs[k]
						wEcdOut := buf.witnessEncodings[autConstraint[1]].Coeffs[k]

						autConstraintEvalNTT0.Mul(wEcdIn, linCheckVecAutTransEcdNTT[i].Coeffs[k])
						autConstraintEvalNTT1.Mul(wEcdOut, linCheckVecEcdNTT.Coeffs[k])
						autConstraintEvalNTT0.Sub(autConstraintEvalNTT0, autConstraintEvalNTT1)
						autConstraintEvalNTT0.Mod(autConstraintEvalNTT0, p.Parameters.Modulus())

						autConstraintEvalNTT0.Mul(autConstraintEvalNTT0, batchConstPow[len(p.ctx.nttConstraints)+c])
						batchedNTT.Coeffs[k].Add(batchedNTT.Coeffs[k], autConstraintEvalNTT0)
						batchedNTT.Coeffs[k].Mod(batchedNTT.Coeffs[k], p.Parameters.Modulus())
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

	var com LinCheckCommitment
	var open linCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDegree]})
	com.RemCommitment, open.RemOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDegree]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.CommitParallel(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDegree]})
	com.OpeningProof = p.polyProver.ProveOpeningParallel(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
