package buckler

import (
	"fmt"
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
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
		if !v.IsNil() {
			return w.walkForProve(prover, v.Elem(), pw, sw)
		}
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

	reducer *bigring.Reducer

	ringQ         *bigring.CyclicRing
	linCheckRingQ *bigring.CyclicRing

	encoder         *Encoder
	linCheckEncoder *Encoder

	polyProver *celpc.Prover

	oracle *celpc.RandomOracle

	ctx *Context

	buffer         proverBuffer
	rowCheckBuffer rowCheckBuffer
	linCheckBuffer linCheckBuffer
	sumCheckBuffer sumCheckBuffer
}

type proverBuffer struct {
	infDcmpBase map[int64][]*big.Int
	twoDcmpBase map[int64][]*big.Int

	infDcmp map[int64][]*big.Int
	twoDcmp map[int64][]*big.Int

	dcmpSigned *big.Int
	baseNeg    *big.Int
	qHalf      *big.Int

	sqNorm    *big.Int
	sqNormSum *big.Int

	pEcd    bigring.BigPoly
	pEcdNTT bigring.BigNTTPoly

	evalPoint *big.Int
}

type rowCheckBuffer struct {
	batchConstPow []*big.Int
	termNTT       bigring.BigNTTPoly
	evalNTT       bigring.BigNTTPoly
	batchedNTT    bigring.BigNTTPoly
	batched       bigring.BigPoly

	quo bigring.BigPoly
	rem bigring.BigPoly
}

type linCheckBuffer struct {
	pEcd bigring.BigPoly

	linCheckVec            []*big.Int
	linCheckVecTrans       []*big.Int
	linCheckVecEcdNTT      bigring.BigNTTPoly
	linCheckVecTransEcdNTT bigring.BigNTTPoly

	batchConstPow []*big.Int
	evalNTT       bigring.BigNTTPoly
	batchedNTT    bigring.BigNTTPoly
	batched       bigring.BigPoly

	quo      bigring.BigPoly
	rem      bigring.BigPoly
	remShift bigring.BigPoly
}

type sumCheckBuffer struct {
	batchConstPow []*big.Int
	termNTT       bigring.BigNTTPoly
	evalNTT       bigring.BigNTTPoly
	batchedNTT    bigring.BigNTTPoly
	batched       bigring.BigPoly

	quo      bigring.BigPoly
	rem      bigring.BigPoly
	remShift bigring.BigPoly
}

// newProverBuffer creates a new proverBuffer.
func newProverBuffer(params celpc.Parameters, ringQ *bigring.CyclicRing, ctx *Context) proverBuffer {
	infDcmpBase := make(map[int64][]*big.Int)
	infDcmp := make(map[int64][]*big.Int)
	for wID, dcmpBound := range ctx.InfDecomposeBound {
		infDcmpBase[wID] = getDecomposeBase(dcmpBound)
		infDcmp[wID] = make([]*big.Int, len(infDcmpBase[wID]))
		for i := 0; i < len(infDcmpBase[wID]); i++ {
			infDcmp[wID][i] = big.NewInt(0)
		}
	}

	twoDcmpBase := make(map[int64][]*big.Int)
	twoDcmp := make(map[int64][]*big.Int)
	for wID, dcmpBound := range ctx.TwoDecomposeBound {
		twoDcmpBase[wID] = getDecomposeBase(dcmpBound)
		twoDcmp[wID] = make([]*big.Int, len(twoDcmpBase[wID]))
		for i := 0; i < len(twoDcmpBase[wID]); i++ {
			twoDcmp[wID][i] = big.NewInt(0)
		}
	}

	return proverBuffer{
		infDcmpBase: infDcmpBase,
		twoDcmpBase: twoDcmpBase,

		infDcmp: infDcmp,
		twoDcmp: twoDcmp,

		dcmpSigned: big.NewInt(0),
		baseNeg:    big.NewInt(0),
		qHalf:      big.NewInt(0).Rsh(params.Modulus(), 1),

		sqNorm:    big.NewInt(0),
		sqNormSum: big.NewInt(0),

		pEcd:    ringQ.NewPoly(),
		pEcdNTT: ringQ.NewNTTPoly(),

		evalPoint: big.NewInt(0),
	}
}

// newRowCheckBuffer creates a new rowCheckBuffer.
func newRowCheckBuffer(params celpc.Parameters, ringQ *bigring.CyclicRing, ctx *Context) rowCheckBuffer {
	batchConstPow := make([]*big.Int, len(ctx.arithConstraints))
	for i := range batchConstPow {
		batchConstPow[i] = big.NewInt(0)
	}

	return rowCheckBuffer{
		batchConstPow: batchConstPow,
		termNTT:       ringQ.NewNTTPoly(),
		evalNTT:       ringQ.NewNTTPoly(),
		batchedNTT:    ringQ.NewNTTPoly(),
		batched:       ringQ.NewPoly(),

		quo: ringQ.NewPoly(),
		rem: ringQ.NewPoly(),
	}
}

// newLinCheckBuffer creates a new linCheckBuffer.
func newLinCheckBuffer(params celpc.Parameters, ringQ *bigring.CyclicRing, ctx *Context) linCheckBuffer {
	batchConstPow := make([]*big.Int, 0)
	for _, transformer := range ctx.linCheck {
		for range ctx.linCheckConstraints[transformer] {
			batchConstPow = append(batchConstPow, big.NewInt(0))
		}
	}

	linCheckVec := make([]*big.Int, params.Degree())
	linCheckVecTrans := make([]*big.Int, params.Degree())
	for i := 0; i < params.Degree(); i++ {
		linCheckVec[i] = big.NewInt(0)
		linCheckVecTrans[i] = big.NewInt(0)
	}

	return linCheckBuffer{
		pEcd: ringQ.NewPoly(),

		linCheckVec:            linCheckVec,
		linCheckVecTrans:       linCheckVecTrans,
		linCheckVecEcdNTT:      ringQ.NewNTTPoly(),
		linCheckVecTransEcdNTT: ringQ.NewNTTPoly(),

		batchConstPow: batchConstPow,
		evalNTT:       ringQ.NewNTTPoly(),
		batchedNTT:    ringQ.NewNTTPoly(),
		batched:       ringQ.NewPoly(),

		quo:      ringQ.NewPoly(),
		rem:      ringQ.NewPoly(),
		remShift: ringQ.NewPoly(),
	}
}

// newSumCheckBuffer creates a new sumCheckBuffer.
func newSumCheckBuffer(params celpc.Parameters, ringQ *bigring.CyclicRing, ctx *Context) sumCheckBuffer {
	batchConstPow := make([]*big.Int, len(ctx.sumCheckConstraints))
	for i := range batchConstPow {
		batchConstPow[i] = big.NewInt(0)
	}

	return sumCheckBuffer{
		batchConstPow: batchConstPow,
		termNTT:       ringQ.NewNTTPoly(),
		evalNTT:       ringQ.NewNTTPoly(),
		batchedNTT:    ringQ.NewNTTPoly(),
		batched:       ringQ.NewPoly(),

		quo:      ringQ.NewPoly(),
		rem:      ringQ.NewPoly(),
		remShift: ringQ.NewPoly(),
	}
}

type witnessData struct {
	publicWitnesses []PublicWitness
	witnesses       []Witness

	publicWitnessEncodings   []bigring.BigNTTPoly
	witnessEncodings         []bigring.BigNTTPoly
	linCheckWitnessEncodings map[int64]bigring.BigNTTPoly
}

func (p *Prover) newWitnessData() witnessData {
	publicWitnesses := make([]PublicWitness, p.ctx.publicWitnessCount)
	for i := int(p.ctx.prePublicWitnessCount); i < int(p.ctx.publicWitnessCount); i++ {
		publicWitnesses[i] = make(PublicWitness, p.Parameters.Degree())
		for j := 0; j < p.Parameters.Degree(); j++ {
			publicWitnesses[i][j] = big.NewInt(0)
		}
	}

	witnesses := make([]Witness, p.ctx.witnessCount)
	for i := int(p.ctx.preWitnessCount); i < int(p.ctx.witnessCount); i++ {
		witnesses[i] = make(Witness, p.Parameters.Degree())
		for j := 0; j < p.Parameters.Degree(); j++ {
			witnesses[i][j] = big.NewInt(0)
		}
	}

	publicWitnessEncodings := make([]bigring.BigNTTPoly, p.ctx.publicWitnessCount)
	for i := 0; i < int(p.ctx.publicWitnessCount); i++ {
		publicWitnessEncodings[i] = p.ringQ.NewNTTPoly()
	}

	witnessEncodings := make([]bigring.BigNTTPoly, p.ctx.witnessCount)
	for i := 0; i < int(p.ctx.witnessCount); i++ {
		witnessEncodings[i] = p.ringQ.NewNTTPoly()
	}

	linCheckWitnessEncodings := make(map[int64]bigring.BigNTTPoly)
	for _, transformer := range p.ctx.linCheck {
		for _, wIDs := range p.ctx.linCheckConstraints[transformer] {
			linCheckWitnessEncodings[wIDs[0]] = p.linCheckRingQ.NewNTTPoly()
			linCheckWitnessEncodings[wIDs[1]] = p.linCheckRingQ.NewNTTPoly()
		}
	}

	return witnessData{
		publicWitnesses:          publicWitnesses,
		witnesses:                witnesses,
		publicWitnessEncodings:   publicWitnessEncodings,
		witnessEncodings:         witnessEncodings,
		linCheckWitnessEncodings: linCheckWitnessEncodings,
	}
}

// ShallowCopy creates a shallow copy of the Prover.
func (p *Prover) ShallowCopy() *Prover {
	return &Prover{
		Parameters: p.Parameters,

		ringQ: p.ringQ.ShallowCopy(),

		encoder:    p.encoder.ShallowCopy(),
		polyProver: p.polyProver.ShallowCopy(),

		oracle: celpc.NewRandomOracle(p.Parameters),

		ctx: p.ctx,

		buffer: newProverBuffer(p.Parameters, p.ringQ, p.ctx),
	}
}

// Prove proves the circuit in given assignment.
func (p *Prover) Prove(ck celpc.AjtaiCommitKey, c Circuit) (Proof, error) {
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

	for i := range witnessData.publicWitnesses {
		p.encoder.EncodeAssign(witnessData.publicWitnesses[i], p.buffer.pEcd)
		p.ringQ.ToNTTPolyAssign(p.buffer.pEcd, witnessData.publicWitnessEncodings[i])
	}

	witnessCommitDeg := p.Parameters.Degree() + p.Parameters.BigIntCommitSize()
	commitments := make([]celpc.Commitment, p.ctx.witnessCount)
	openings := make([]celpc.Opening, p.ctx.witnessCount)
	for i := range witnessData.witnesses {
		p.encoder.RandomEncodeAssign(witnessData.witnesses[i], p.buffer.pEcd)
		p.ringQ.ToNTTPolyAssign(p.buffer.pEcd, witnessData.witnessEncodings[i])

		if _, ok := witnessData.linCheckWitnessEncodings[int64(i)]; ok {
			embedFactor := p.ringQ.Degree() / p.linCheckRingQ.Degree()
			for j := 0; j < p.linCheckRingQ.Degree(); j++ {
				witnessData.linCheckWitnessEncodings[int64(i)].Coeffs[j].Set(witnessData.witnessEncodings[i].Coeffs[j*embedFactor])
			}
		}

		commitments[i], openings[i] = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.buffer.pEcd.Coeffs[:witnessCommitDeg]})
	}
	openingProof := p.polyProver.ProveOpening(commitments, openings)

	for i := range commitments {
		p.oracle.WriteCommitment(commitments[i])
	}
	p.oracle.WriteOpeningProof(openingProof)

	var linCheckMaskCommit SumCheckMaskCommitment
	var linCheckMask sumCheckMask
	if p.ctx.hasLinCheck() {
		linCheckMaskCommit, linCheckMask = p.sumCheckMask(2 * p.Parameters.Degree())

		p.oracle.WriteCommitment(linCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(linCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(linCheckMaskCommit.MaskSum)
	}

	var sumCheckMaskCommit SumCheckMaskCommitment
	var sumCheckMask sumCheckMask
	if p.ctx.hasSumCheck() {
		sumCheckMaskCommit, sumCheckMask = p.sumCheckMask(p.ctx.maxDegree)

		p.oracle.WriteCommitment(sumCheckMaskCommit.MaskCommitment)
		p.oracle.WriteOpeningProof(sumCheckMaskCommit.OpeningProof)
		p.oracle.WriteBigInt(sumCheckMaskCommit.MaskSum)
	}

	p.oracle.Finalize()

	var rowCheckCommit RowCheckCommitment
	var rowCheckOpen rowCheckOpening
	if p.ctx.hasRowCheck() {
		p.oracle.SampleModAssign(p.rowCheckBuffer.batchConstPow[0])
		for i := 1; i < len(p.rowCheckBuffer.batchConstPow); i++ {
			p.rowCheckBuffer.batchConstPow[i].Mul(p.rowCheckBuffer.batchConstPow[i-1], p.rowCheckBuffer.batchConstPow[0])
			p.reducer.Reduce(p.rowCheckBuffer.batchConstPow[i])
		}
		rowCheckCommit, rowCheckOpen = p.rowCheck(p.rowCheckBuffer.batchConstPow, witnessData)
	}

	var linCheckCommit SumCheckCommitment
	var linCheckOpen sumCheckOpening
	if p.ctx.hasLinCheck() {
		p.oracle.SampleModAssign(p.linCheckBuffer.batchConstPow[0])
		for i := 1; i < len(p.linCheckBuffer.batchConstPow); i++ {
			p.linCheckBuffer.batchConstPow[i].Mul(p.linCheckBuffer.batchConstPow[i-1], p.linCheckBuffer.batchConstPow[0])
			p.reducer.Reduce(p.linCheckBuffer.batchConstPow[i])
		}

		p.oracle.SampleModAssign(p.linCheckBuffer.linCheckVec[0])
		for i := 1; i < p.Parameters.Degree(); i++ {
			p.linCheckBuffer.linCheckVec[i].Mul(p.linCheckBuffer.linCheckVec[i-1], p.linCheckBuffer.linCheckVec[0])
			p.reducer.Reduce(p.linCheckBuffer.linCheckVec[i])
		}

		linCheckCommit, linCheckOpen = p.linCheck(p.linCheckBuffer.batchConstPow, p.linCheckBuffer.linCheckVec, linCheckMask, witnessData)
	}

	var sumCheckCommit SumCheckCommitment
	var sumCheckOpen sumCheckOpening
	if p.ctx.hasSumCheck() {
		p.oracle.SampleModAssign(p.sumCheckBuffer.batchConstPow[0])
		for i := 1; i < len(p.sumCheckBuffer.batchConstPow); i++ {
			p.sumCheckBuffer.batchConstPow[i].Mul(p.sumCheckBuffer.batchConstPow[i-1], p.sumCheckBuffer.batchConstPow[0])
			p.reducer.Reduce(p.sumCheckBuffer.batchConstPow[i])
		}

		sumCheckCommit, sumCheckOpen = p.sumCheck(p.sumCheckBuffer.batchConstPow, sumCheckMask, witnessData)
	}

	if p.ctx.hasRowCheck() {
		p.oracle.WriteCommitment(rowCheckCommit.QuoCommitment)
		p.oracle.WriteOpeningProof(rowCheckCommit.OpeningProof)
	}

	if p.ctx.hasLinCheck() {
		p.oracle.WriteCommitment(linCheckCommit.QuoCommitment)
		p.oracle.WriteCommitment(linCheckCommit.RemCommitment)
		p.oracle.WriteCommitment(linCheckCommit.RemShiftCommitment)
		p.oracle.WriteOpeningProof(linCheckCommit.OpeningProof)
	}

	if p.ctx.hasSumCheck() {
		p.oracle.WriteCommitment(sumCheckCommit.QuoCommitment)
		p.oracle.WriteCommitment(sumCheckCommit.RemCommitment)
		p.oracle.WriteCommitment(sumCheckCommit.RemShiftCommitment)
		p.oracle.WriteOpeningProof(sumCheckCommit.OpeningProof)
	}

	p.oracle.Finalize()

	p.oracle.SampleModAssign(p.buffer.evalPoint)

	evalProofs := make([]celpc.EvaluationProof, len(commitments))
	for i := range evalProofs {
		evalProofs[i] = p.polyProver.Evaluate(p.buffer.evalPoint, openings[i])
	}

	var rowCheckEvalProof RowCheckEvaluationProof
	if p.ctx.hasRowCheck() {
		rowCheckEvalProof = RowCheckEvaluationProof{
			QuoEvalProof: p.polyProver.Evaluate(p.buffer.evalPoint, rowCheckOpen.QuoOpening),
		}
	}

	var linCheckEvalProof SumCheckEvaluationProof
	if p.ctx.hasLinCheck() {
		linCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.Evaluate(p.buffer.evalPoint, linCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.Evaluate(p.buffer.evalPoint, linCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.Evaluate(p.buffer.evalPoint, linCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.Evaluate(p.buffer.evalPoint, linCheckOpen.RemShiftOpening),
		}
	}

	var sumCheckEvalProof SumCheckEvaluationProof
	if p.ctx.hasSumCheck() {
		sumCheckEvalProof = SumCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.Evaluate(p.buffer.evalPoint, sumCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.Evaluate(p.buffer.evalPoint, sumCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.Evaluate(p.buffer.evalPoint, sumCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.Evaluate(p.buffer.evalPoint, sumCheckOpen.RemShiftOpening),
		}
	}

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

func (p *Prover) evaluateCircuitAssign(batchConstPow []*big.Int, constraints []ArithmeticConstraint, witnessData witnessData, termNTT, evalNTT, batchedNTT bigring.BigNTTPoly, batchedOut bigring.BigPoly) {
	batchedNTT.Clear()

	for c, constraint := range constraints {
		evalNTT.Clear()
		for i := range constraint.witness {
			for j := 0; j < p.ringQ.Degree(); j++ {
				termNTT.Coeffs[j].Set(constraint.coeffsBig[i])
			}

			if constraint.coeffsPublicWitness[i] != -1 {
				p.ringQ.MulNTTAssign(termNTT, witnessData.publicWitnessEncodings[constraint.coeffsPublicWitness[i]], termNTT)
			}

			for j := range constraint.witness[i] {
				p.ringQ.MulNTTAssign(termNTT, witnessData.witnessEncodings[constraint.witness[i][j]], termNTT)
			}

			p.ringQ.AddNTTAssign(evalNTT, termNTT, evalNTT)
		}
		p.ringQ.ScalarMulAddNTTAssign(evalNTT, batchConstPow[c], batchedNTT)
	}

	p.ringQ.ToPolyAssign(batchedNTT, batchedOut)
}

func (p *Prover) rowCheck(batchConstPow []*big.Int, witnessData witnessData) (RowCheckCommitment, rowCheckOpening) {
	p.evaluateCircuitAssign(
		batchConstPow, p.ctx.arithConstraints, witnessData,
		p.rowCheckBuffer.termNTT, p.rowCheckBuffer.evalNTT, p.rowCheckBuffer.batchedNTT, p.rowCheckBuffer.batched)
	p.ringQ.QuoRemByVanishingAssign(p.rowCheckBuffer.batched, p.Parameters.Degree(), p.rowCheckBuffer.quo, p.rowCheckBuffer.rem)

	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.rowCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening([]celpc.Commitment{com.QuoCommitment}, []celpc.Opening{open.QuoOpening})

	return com, open
}

func (p *Prover) sumCheckMask(maskDeg int) (SumCheckMaskCommitment, sumCheckMask) {
	var com SumCheckMaskCommitment
	var open sumCheckMask

	open.Mask = p.ringQ.NewPoly()
	for i := 0; i < p.Parameters.Degree(); i++ {
		p.encoder.StreamSampler.SampleModAssign(open.Mask.Coeffs[i])
	}
	com.MaskSum = big.NewInt(0).Set(open.Mask.Coeffs[0])
	for i := p.Parameters.Degree(); i < maskDeg; i++ {
		p.encoder.StreamSampler.SampleModAssign(open.Mask.Coeffs[i])
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

func (p *Prover) linCheck(batchConstPow []*big.Int, linCheckVec []*big.Int, linCheckMask sumCheckMask, witnessData witnessData) (SumCheckCommitment, sumCheckOpening) {
	p.linCheckEncoder.EncodeAssign(linCheckVec, p.linCheckBuffer.pEcd)
	p.linCheckRingQ.ToNTTPolyAssign(p.linCheckBuffer.pEcd, p.linCheckBuffer.linCheckVecEcdNTT)

	p.linCheckBuffer.batchedNTT.Clear()
	powIdx := 0
	for _, transformer := range p.ctx.linCheck {
		transformer.TransformAssign(linCheckVec, p.linCheckBuffer.linCheckVecTrans)
		p.linCheckEncoder.EncodeAssign(p.linCheckBuffer.linCheckVecTrans, p.linCheckBuffer.pEcd)
		p.linCheckRingQ.ToNTTPolyAssign(p.linCheckBuffer.pEcd, p.linCheckBuffer.linCheckVecTransEcdNTT)
		for i := range p.ctx.linCheckConstraints[transformer] {
			wEcdIn := witnessData.linCheckWitnessEncodings[p.ctx.linCheckConstraints[transformer][i][0]]
			wEcdOut := witnessData.linCheckWitnessEncodings[p.ctx.linCheckConstraints[transformer][i][1]]

			p.linCheckRingQ.MulNTTAssign(wEcdIn, p.linCheckBuffer.linCheckVecTransEcdNTT, p.linCheckBuffer.evalNTT)
			p.linCheckRingQ.MulSubNTTAssign(wEcdOut, p.linCheckBuffer.linCheckVecEcdNTT, p.linCheckBuffer.evalNTT)
			p.linCheckRingQ.ScalarMulAddNTTAssign(p.linCheckBuffer.evalNTT, batchConstPow[powIdx], p.linCheckBuffer.batchedNTT)

			powIdx++
		}
	}
	p.linCheckRingQ.ToPolyAssign(p.linCheckBuffer.batchedNTT, p.linCheckBuffer.batched)
	p.linCheckRingQ.AddAssign(p.linCheckBuffer.batched, linCheckMask.Mask, p.linCheckBuffer.batched)

	p.linCheckRingQ.QuoRemByVanishingAssign(p.linCheckBuffer.batched, p.Parameters.Degree(), p.linCheckBuffer.quo, p.linCheckBuffer.remShift)
	p.linCheckBuffer.remShift.Coeffs[0].SetInt64(0)

	quoCommitDeg := p.Parameters.Degree()
	remCommitDeg := p.Parameters.Degree()

	for i, ii := 0, 1; ii < remCommitDeg; i, ii = i+1, ii+1 {
		p.linCheckBuffer.rem.Coeffs[i].Set(p.linCheckBuffer.remShift.Coeffs[ii])
	}
	p.linCheckBuffer.rem.Coeffs[remCommitDeg-1].SetInt64(0)

	var com SumCheckCommitment
	var open sumCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.linCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.linCheckBuffer.rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.linCheckBuffer.remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}

func (p *Prover) sumCheck(batchConstPow []*big.Int, sumCheckMask sumCheckMask, witnessData witnessData) (SumCheckCommitment, sumCheckOpening) {
	p.evaluateCircuitAssign(
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
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.sumCheckBuffer.quo.Coeffs[:quoCommitDeg]})
	com.RemCommitment, open.RemOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.sumCheckBuffer.rem.Coeffs[:remCommitDeg]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: p.sumCheckBuffer.remShift.Coeffs[:remCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}

// CommitDegree returns the full degree of the committed polynomials.
func (p *Prover) CommitDegree() int {
	deg := int(p.ctx.witnessCount) * p.Parameters.Degree()

	if p.ctx.hasRowCheck() {
		quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
		quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
		deg += quoCommitDeg
	}

	if p.ctx.hasLinCheck() {
		maskDeg := 2 * p.Parameters.Degree()
		quoDeg := p.Parameters.Degree()
		remDeg := p.Parameters.Degree()
		deg += maskDeg + quoDeg + 2*remDeg
	}

	if p.ctx.hasSumCheck() {
		maskDeg := p.ctx.maxDegree
		quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
		quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()
		remDeg := p.Parameters.Degree()
		deg += maskDeg + quoCommitDeg + 2*remDeg
	}

	return deg
}
