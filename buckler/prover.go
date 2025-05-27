package buckler

import (
	"fmt"
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/sp301415/ringo-snark/num"
)

func (w *walker) walkForProve(prover *Prover, v reflect.Value, pw []PublicWitness, sw []Witness) error {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness{}):
		pw[w.publicWitnessCount] = v.Interface().(PublicWitness)
		if len(pw[w.publicWitnessCount]) != prover.Parameters.Degree() {
			return fmt.Errorf("degree mismatch")
		}
		w.publicWitnessCount++
		return nil
	case reflect.TypeOf(Witness{}):
		sw[w.witnessCount] = v.Interface().(Witness)
		if len(sw[w.witnessCount]) != prover.Parameters.Degree() {
			return fmt.Errorf("degree mismatch")
		}
		w.witnessCount++
		return nil
	}

	switch v.Kind() {
	case reflect.Ptr, reflect.Interface:
		return w.walkForProve(prover, v.Elem(), pw, sw)
	case reflect.Invalid:
		panic("invalid type")
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			if err := w.walkForProve(prover, v.Field(i), pw, sw); err != nil {
				return err
			}
		}
	case reflect.Slice, reflect.Array:
		for i := 0; i < v.Len(); i++ {
			if err := w.walkForProve(prover, v.Index(i), pw, sw); err != nil {
				return err
			}
		}
	}

	return nil
}

// Prover proves the given circuit.
type Prover struct {
	Parameters celpc.Parameters

	ringQ     *bigring.BigRing
	baseRingQ *bigring.BigRing

	encoder    *Encoder
	polyProver *celpc.Prover

	oracle *celpc.RandomOracle

	ctx *Context
}

type proverBuffer struct {
	publicWitnesses []PublicWitness
	witnesses       []Witness

	publicWitnessEncodings []bigring.BigNTTPoly
	witnessEncodings       []bigring.BigNTTPoly

	commitments []celpc.Commitment
	openings    []celpc.Opening
}

func (p *Prover) newBuffer() proverBuffer {
	return proverBuffer{
		publicWitnesses:        make([]PublicWitness, p.ctx.publicWitnessCount),
		witnesses:              make([]Witness, p.ctx.witnessCount),
		publicWitnessEncodings: make([]bigring.BigNTTPoly, p.ctx.publicWitnessCount),
		witnessEncodings:       make([]bigring.BigNTTPoly, p.ctx.witnessCount),
		commitments:            make([]celpc.Commitment, p.ctx.witnessCount),
		openings:               make([]celpc.Opening, p.ctx.witnessCount),
	}
}

// ShallowCopy creates a shallow copy of the Prover.
func (p *Prover) ShallowCopy() *Prover {
	return &Prover{
		Parameters: p.Parameters,

		ringQ:     p.ringQ,
		baseRingQ: p.baseRingQ,

		encoder:    p.encoder.ShallowCopy(),
		polyProver: p.polyProver.ShallowCopy(),

		oracle: celpc.NewRandomOracle(p.Parameters),

		ctx: p.ctx,
	}
}

// Prove proves the circuit in given assignment.
func (p *Prover) Prove(ck celpc.AjtaiCommitKey, c Circuit) (Proof, error) {
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

	for wID, _ := range p.ctx.TwoDecomposeBound {
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

	for i := 0; i < len(buf.publicWitnesses); i++ {
		pwEcd := p.encoder.Encode(buf.publicWitnesses[i])
		buf.publicWitnessEncodings[i] = p.ringQ.ToNTTPoly(pwEcd)
	}

	witnessCommitDeg := p.Parameters.Degree() + p.Parameters.BigIntCommitSize()
	for i := 0; i < len(buf.witnesses); i++ {
		wEcd := p.encoder.RandomEncode(buf.witnesses[i])
		buf.witnessEncodings[i] = p.ringQ.ToNTTPoly(wEcd)

		wCommit := bigring.BigPoly{Coeffs: wEcd.Coeffs[:witnessCommitDeg]}
		buf.commitments[i], buf.openings[i] = p.polyProver.Commit(wCommit)
	}
	openingProof := p.polyProver.ProveOpening(buf.commitments, buf.openings)

	for i := 0; i < len(buf.commitments); i++ {
		p.oracle.WriteCommitment(buf.commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)

	var linCheckMaskCommit SumCheckMaskCommitment
	var linCheckMask sumCheckMask
	if p.ctx.HasLinCheck() {
		linCheckMaskCommit, linCheckMask = p.sumCheckMask(2 * p.Parameters.Degree())

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

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpen rowCheckOpening
	if p.ctx.HasRowCheck() {
		batchRowCheckConsts := make(map[int]*big.Int)
		for _, constraint := range p.ctx.arithConstraints {
			if _, ok := batchRowCheckConsts[constraint.degree]; !ok {
				batchRowCheckConsts[constraint.degree] = p.oracle.SampleMod()
			}
		}

		rowCheckCommit, rowCheckOpen = p.rowCheck(batchRowCheckConsts, buf)
	}

	var linCheckCommit SumCheckCommitment
	var linCheckOpen sumCheckOpening
	if p.ctx.HasLinCheck() {
		batchLinConst := p.oracle.SampleMod()

		batchLinVec := make([]*big.Int, p.Parameters.Degree())
		batchLinVec[0] = p.oracle.SampleMod()
		for i := 1; i < p.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], p.Parameters.Modulus())
		}

		linCheckCommit, linCheckOpen = p.linCheck(batchLinConst, batchLinVec, linCheckMask, buf)
	}

	var sumCheckCommit SumCheckCommitment
	var sumCheckOpen sumCheckOpening
	if p.ctx.HasSumCheck() {
		batchSumCheckConsts := make(map[int]*big.Int)
		for _, constraint := range p.ctx.sumCheckConstraints {
			if _, ok := batchSumCheckConsts[constraint.degree]; !ok {
				batchSumCheckConsts[constraint.degree] = p.oracle.SampleMod()
			}
		}

		sumCheckCommit, sumCheckOpen = p.sumCheck(batchSumCheckConsts, sumCheckMask, buf)
	}

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

	evalProofs := make([]celpc.EvaluationProof, len(buf.commitments))
	for i := 0; i < len(buf.commitments); i++ {
		evalProofs[i] = p.polyProver.Evaluate(evaluatePoint, buf.openings[i])
	}

	var rowCheckEvalProof RowCheckEvaluationProof
	if p.ctx.HasRowCheck() {
		rowCheckEvalProof = RowCheckEvaluationProof{
			QuoEvalProof: p.polyProver.Evaluate(evaluatePoint, rowCheckOpen.QuoOpening),
		}
	}

	var linCheckEvalProof SumCheckEvaluationProof
	if p.ctx.HasLinCheck() {
		linCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.Evaluate(evaluatePoint, linCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.Evaluate(evaluatePoint, linCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.Evaluate(evaluatePoint, linCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.Evaluate(evaluatePoint, linCheckOpen.RemShiftOpening),
		}
	}

	var sumCheckEvalProof SumCheckEvaluationProof
	if p.ctx.HasSumCheck() {
		sumCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.Evaluate(evaluatePoint, sumCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.Evaluate(evaluatePoint, sumCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.Evaluate(evaluatePoint, sumCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.Evaluate(evaluatePoint, sumCheckOpen.RemShiftOpening),
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

func (p *Prover) evaluateCircuit(batchConsts map[int]*big.Int, constraints []ArithmeticConstraint, buf proverBuffer) bigring.BigPoly {
	batchConstsPow := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPow[k] = big.NewInt(0).Set(v)
	}

	batchedNTT := p.ringQ.NewNTTPoly()
	for _, constraint := range constraints {
		constraintEvalNTT := p.ringQ.NewNTTPoly()
		termNTT := p.ringQ.NewNTTPoly()
		for i := 0; i < len(constraint.witness); i++ {
			for j := 0; j < p.ringQ.Degree(); j++ {
				termNTT.Coeffs[j].Set(constraint.coeffsBig[i])
			}

			if constraint.coeffsPublicWitness[i] != -1 {
				pwEcdNTT := buf.publicWitnessEncodings[constraint.coeffsPublicWitness[i]]
				p.ringQ.MulNTTAssign(termNTT, pwEcdNTT, termNTT)
			}

			for j := 0; j < len(constraint.witness[i]); j++ {
				witnessEcdNTT := buf.witnessEncodings[constraint.witness[i][j]]
				p.ringQ.MulNTTAssign(termNTT, witnessEcdNTT, termNTT)
			}

			p.ringQ.AddNTTAssign(constraintEvalNTT, termNTT, constraintEvalNTT)
		}
		p.ringQ.ScalarMulAddNTTAssign(constraintEvalNTT, batchConstsPow[constraint.degree], batchedNTT)

		batchConstsPow[constraint.degree].Mul(batchConstsPow[constraint.degree], batchConsts[constraint.degree])
		batchConstsPow[constraint.degree].Mod(batchConstsPow[constraint.degree], p.Parameters.Modulus())
	}
	batched := p.ringQ.ToPoly(batchedNTT)

	return batched
}

func (p *Prover) rowCheck(batchConsts map[int]*big.Int, buf proverBuffer) (RowCheckCommitment, rowCheckOpening) {
	batched := p.evaluateCircuit(batchConsts, p.ctx.arithConstraints, buf)
	quo, _ := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())

	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening([]celpc.Commitment{com.QuoCommitment}, []celpc.Opening{open.QuoOpening})

	return com, open
}

func (p *Prover) sumCheckMask(maskDeg int) (SumCheckMaskCommitment, sumCheckMask) {
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
	com.MaskCommitment, open.MaskOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: open.Mask.Coeffs[:maskCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening([]celpc.Commitment{com.MaskCommitment}, []celpc.Opening{open.MaskOpening})

	return com, open
}

func (p *Prover) linCheck(batchConst *big.Int, linCheckVec []*big.Int, linCheckMask sumCheckMask, buf proverBuffer) (SumCheckCommitment, sumCheckOpening) {
	batchConstPow := big.NewInt(0).Set(batchConst)

	linCheckVecEcd := p.encoder.Encode(linCheckVec)
	linCheckVecEcdNTT := p.ringQ.ToNTTPoly(linCheckVecEcd)

	batchedNTT := p.ringQ.NewNTTPoly()

	linCheckVecNTTTrans := make([]*big.Int, p.Parameters.Degree())
	for i := 0; i < p.Parameters.Degree(); i++ {
		linCheckVecNTTTrans[i] = big.NewInt(0).Set(linCheckVec[p.Parameters.Degree()-i-1])
	}
	p.baseRingQ.InvNTTInPlace(linCheckVecNTTTrans)
	linCheckVecNTTTransEcd := p.encoder.Encode(linCheckVecNTTTrans)
	linCheckVecNTTTransEcdNTT := p.ringQ.ToNTTPoly(linCheckVecNTTTransEcd)

	for _, nttConstraint := range p.ctx.nttConstraints {
		nttConstraintEvalNTT := p.ringQ.NewNTTPoly()

		wEcdIn := buf.witnessEncodings[nttConstraint[0]]
		wEcdOut := buf.witnessEncodings[nttConstraint[1]]

		p.ringQ.MulNTTAssign(wEcdIn, linCheckVecNTTTransEcdNTT, nttConstraintEvalNTT)
		p.ringQ.MulSubNTTAssign(wEcdOut, linCheckVecEcdNTT, nttConstraintEvalNTT)
		p.ringQ.ScalarMulAddNTTAssign(nttConstraintEvalNTT, batchConstPow, batchedNTT)

		batchConstPow.Mul(batchConstPow, batchConst)
		batchConstPow.Mod(batchConstPow, p.Parameters.Modulus())
	}

	for i := range p.ctx.autConstraints {
		autIdx := p.ctx.autConstraintsIdx[i]
		autIdxInv := int(num.ModInverse(uint64(autIdx), uint64(2*p.Parameters.Degree())))
		linCheckVecAutTrans := p.baseRingQ.AutomorphismNTT(bigring.BigNTTPoly{Coeffs: linCheckVec}, autIdxInv).Coeffs
		linCheckVecAutTransEcd := p.encoder.Encode(linCheckVecAutTrans)
		linCheckVecAutTransEcdNTT := p.ringQ.ToNTTPoly(linCheckVecAutTransEcd)

		for _, autConstraint := range p.ctx.autConstraints[i] {
			autConstraintEvalNTT := p.ringQ.NewNTTPoly()

			wEcdIn := buf.witnessEncodings[autConstraint[0]]
			wEcdOut := buf.witnessEncodings[autConstraint[1]]

			p.ringQ.MulNTTAssign(wEcdIn, linCheckVecAutTransEcdNTT, autConstraintEvalNTT)
			p.ringQ.MulSubNTTAssign(wEcdOut, linCheckVecEcdNTT, autConstraintEvalNTT)
			p.ringQ.ScalarMulAddNTTAssign(autConstraintEvalNTT, batchConstPow, batchedNTT)

			batchConstPow.Mul(batchConstPow, batchConst)
			batchConstPow.Mod(batchConstPow, p.Parameters.Modulus())
		}
	}

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
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}

func (p *Prover) sumCheck(batchConsts map[int]*big.Int, sumCheckMask sumCheckMask, buf proverBuffer) (SumCheckCommitment, sumCheckOpening) {
	batched := p.evaluateCircuit(batchConsts, p.ctx.sumCheckConstraints, buf)
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
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
