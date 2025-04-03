package buckler

import (
	"math"
	"math/big"
	"reflect"

	"github.com/sp301415/rlwe-piop/bigring"
	"github.com/sp301415/rlwe-piop/celpc"
	"github.com/sp301415/rlwe-piop/num"
)

func (w *walker) walkForProve(prover *Prover, v reflect.Value, pw []PublicWitness, sw []Witness) {
	switch v.Type() {
	case reflect.TypeOf(PublicWitness{}):
		pw[w.publicWitnessCount] = v.Interface().(PublicWitness)
		w.publicWitnessCount++
	case reflect.TypeOf(Witness{}):
		sw[w.witnessCount] = v.Interface().(Witness)
		w.witnessCount++
	}

	switch v.Kind() {
	case reflect.Ptr, reflect.Interface:
		w.walkForProve(prover, v.Elem(), pw, sw)
	case reflect.Invalid:
		panic("invalid type")
	case reflect.Struct:
		for i := 0; i < v.NumField(); i++ {
			w.walkForProve(prover, v.Field(i), pw, sw)
		}
	case reflect.Slice, reflect.Array:
		for i := 0; i < v.Len(); i++ {
			w.walkForProve(prover, v.Index(i), pw, sw)
		}
	}
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

	// Only for Debugging
	tw []*big.Int
}

type proverBuffer struct {
	publicWitnesses []PublicWitness
	witnesses       []Witness

	publicWitnessEncodings []bigring.BigNTTPoly
	witnessEncodings       []bigring.BigNTTPoly

	commitments []celpc.Commitment
	openings    []celpc.Opening
}

func newProver(params celpc.Parameters, ctx *Context) *Prover {
	logEmbedDegree := int(math.Ceil(math.Log2(float64(ctx.maxDegree))))
	embedDegree := 1 << logEmbedDegree

	// Only for debugging
	exp1 := big.NewInt(0).Sub(params.Modulus(), big.NewInt(1))
	exp1.Div(exp1, big.NewInt(int64(params.Degree())))
	exp2 := big.NewInt(int64(params.Degree()) / 2)
	g := big.NewInt(0)
	for x := big.NewInt(2); x.Cmp(params.Modulus()) < 0; x.Add(x, big.NewInt(1)) {
		g.Exp(x, exp1, params.Modulus())
		gPow := big.NewInt(0).Exp(g, exp2, params.Modulus())
		if gPow.Cmp(big.NewInt(1)) != 0 {
			break
		}
	}

	tw := make([]*big.Int, params.Degree())
	for i := 0; i < params.Degree(); i++ {
		tw[i] = big.NewInt(0).Exp(g, big.NewInt(int64(i)), params.Modulus())
	}

	return &Prover{
		Parameters: params,

		ringQ:     bigring.NewBigRing(embedDegree, params.Modulus()),
		baseRingQ: bigring.NewBigRing(params.Degree(), params.Modulus()),

		encoder:    NewEncoder(params, embedDegree),
		polyProver: celpc.NewProver(params, celpc.AjtaiCommitKey{}),

		oracle: celpc.NewRandomOracle(params),

		ctx: ctx,

		tw: tw,
	}
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

// Prove proves the circuit in given assignment.
func (p *Prover) Prove(ck celpc.AjtaiCommitKey, c Circuit) Proof {
	p.oracle.Reset()
	p.polyProver.Commiter = celpc.NewAjtaiCommiter(p.Parameters, ck)
	buf := p.newBuffer()

	walker := &walker{}
	walker.walkForProve(p, reflect.ValueOf(c), buf.publicWitnesses, buf.witnesses)

	for i := 0; i < len(buf.publicWitnesses); i++ {
		pwEcd := p.encoder.Encode(buf.publicWitnesses[i])
		buf.publicWitnessEncodings[i] = p.ringQ.ToNTTPoly(pwEcd)
	}

	for wID, wDcmpIDs := range p.ctx.decomposedWitness {
		w := buf.witnesses[wID]
		logBound := len(wDcmpIDs) - 1

		wDcmp := make([]Witness, logBound+1)
		for i := 0; i < logBound+1; i++ {
			wDcmp[i] = make(Witness, p.Parameters.Degree())
		}

		for i := 0; i < p.Parameters.Degree(); i++ {
			coeffDcmp := bigSignedDecompose(w[i], p.Parameters.Modulus(), logBound)
			for j := 0; j < logBound+1; j++ {
				wDcmp[j][i] = coeffDcmp[j]
			}
		}

		for i, wDcmpID := range wDcmpIDs {
			buf.witnesses[wDcmpID[0].Int64()] = wDcmp[i]
		}
	}

	for i := 0; i < len(buf.witnesses); i++ {
		wEcd := p.encoder.RandomEncode(buf.witnesses[i])
		wEcdNTT := p.ringQ.ToNTTPoly(wEcd)
		buf.witnessEncodings[i] = wEcdNTT

		wCommit := bigring.BigPoly{Coeffs: wEcd.Coeffs[:2*p.Parameters.Degree()]}
		buf.commitments[i], buf.openings[i] = p.polyProver.Commit(wCommit)
	}
	openingProof := p.polyProver.ProveOpening(buf.commitments, buf.openings)

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

		rowCheckCommit, rowCheckOpening = p.rowCheck(batchArithConsts, buf)
	}

	var linCheckCommit LinCheckCommitment
	var linCheckOpen linCheckOpening
	var batchLinConst *big.Int
	var batchLinVec []*big.Int
	if p.ctx.HasLinearCheck() {
		batchLinConst = p.oracle.SampleMod()

		batchLinVec = make([]*big.Int, p.Parameters.Degree())
		batchLinVec[0] = p.oracle.SampleMod()
		for i := 1; i < p.Parameters.Degree(); i++ {
			batchLinVec[i] = big.NewInt(0).Mul(batchLinVec[i-1], batchLinVec[0])
			batchLinVec[i].Mod(batchLinVec[i], p.Parameters.Modulus())
		}

		linCheckCommit, linCheckOpen = p.linCheck(batchLinConst, batchLinVec, linCheckMask, buf)
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

	evalProofs := make([]celpc.EvaluationProof, len(buf.commitments))
	for i := 0; i < len(buf.commitments); i++ {
		evalProofs[i] = p.polyProver.Evaluate(evaluatePoint, buf.openings[i])
	}

	var rowCheckEvalProof RowCheckEvaluationProof
	if p.ctx.HasRowCheck() {
		rowCheckEvalProof = RowCheckEvaluationProof{
			QuoEvalProof: p.polyProver.Evaluate(evaluatePoint, rowCheckOpening.QuoOpening),
		}
	}

	var linCheckEvalProof LinCheckEvaluationProof
	if p.ctx.HasLinearCheck() {
		linCheckEvalProof = LinCheckEvaluationProof{
			MaskEvalProof:     p.polyProver.Evaluate(evaluatePoint, linCheckMask.MaskOpening),
			QuoEvalProof:      p.polyProver.Evaluate(evaluatePoint, linCheckOpen.QuoOpening),
			RemEvalProof:      p.polyProver.Evaluate(evaluatePoint, linCheckOpen.RemOpening),
			RemShiftEvalProof: p.polyProver.Evaluate(evaluatePoint, linCheckOpen.RemShiftOpening),
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
	}
}

func (p *Prover) rowCheck(batchConsts map[int]*big.Int, buf proverBuffer) (RowCheckCommitment, rowCheckOpening) {
	batchConstsPow := make(map[int]*big.Int, len(batchConsts))
	for k, v := range batchConsts {
		batchConstsPow[k] = big.NewInt(0).Set(v)
	}

	batchedNTT := p.ringQ.NewNTTPoly()
	for _, constraint := range p.ctx.arithConstraints {
		constraintEvalNTT := p.ringQ.NewNTTPoly()
		termNTT := p.ringQ.NewNTTPoly()
		for i := 0; i < len(constraint.witness); i++ {
			for j := 0; j < p.ringQ.N(); j++ {
				termNTT.Coeffs[j].SetInt64(constraint.coeffsInt64[i])
			}

			if constraint.coeffsBig[i] != nil {
				for j := 0; j < p.ringQ.N(); j++ {
					termNTT.Coeffs[j].Mul(termNTT.Coeffs[j], constraint.coeffsBig[i])
					termNTT.Coeffs[j].Mod(termNTT.Coeffs[j], p.Parameters.Modulus())
				}
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

	quo, _ := p.ringQ.QuoRemByVanishing(batched, p.Parameters.Degree())
	quoDeg := p.ctx.maxDegree - p.Parameters.Degree()
	quoCommitDeg := int(math.Ceil(float64(quoDeg)/float64(p.Parameters.BigIntCommitSize()))) * p.Parameters.BigIntCommitSize()

	var com RowCheckCommitment
	var open rowCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDeg]})
	com.OpeningProof = p.polyProver.ProveOpening([]celpc.Commitment{com.QuoCommitment}, []celpc.Opening{open.QuoOpening})

	return com, open
}

func (p *Prover) linCheckMask() (LinCheckMaskCommitment, linCheckMask) {
	var com LinCheckMaskCommitment
	var open linCheckMask

	open.Mask = p.ringQ.NewPoly()
	maskDegree := 3*p.Parameters.Degree() - 2
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

	maskCommitDegree := 3 * p.Parameters.Degree()
	com.MaskCommitment, open.MaskOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: open.Mask.Coeffs[:maskCommitDegree]})
	com.OpeningProof = p.polyProver.ProveOpening([]celpc.Commitment{com.MaskCommitment}, []celpc.Opening{open.MaskOpening})

	return com, open
}

func (p *Prover) linCheck(batchConst *big.Int, linCheckVec []*big.Int, linCheckMask linCheckMask, buf proverBuffer) (LinCheckCommitment, linCheckOpening) {
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

	quoCommitDegree := 3 * p.Parameters.Degree()
	remCommitDegree := p.Parameters.Degree()

	rem := p.ringQ.NewPoly()
	for i, ii := 0, 1; ii < remCommitDegree; i, ii = i+1, ii+1 {
		rem.Coeffs[i].Set(remShift.Coeffs[ii])
	}

	var com LinCheckCommitment
	var open linCheckOpening
	com.QuoCommitment, open.QuoOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: quo.Coeffs[:quoCommitDegree]})
	com.RemCommitment, open.RemOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: rem.Coeffs[:remCommitDegree]})
	com.RemShiftCommitment, open.RemShiftOpening = p.polyProver.Commit(bigring.BigPoly{Coeffs: remShift.Coeffs[:remCommitDegree]})
	com.OpeningProof = p.polyProver.ProveOpening(
		[]celpc.Commitment{com.QuoCommitment, com.RemCommitment, com.RemShiftCommitment},
		[]celpc.Opening{open.QuoOpening, open.RemOpening, open.RemShiftOpening},
	)

	return com, open
}
