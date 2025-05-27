package buckler_test

import (
	"math"
	"math/big"
	"testing"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/buckler"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/stretchr/testify/assert"
)

var (
	params = celpc.ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 1,

		Degree:           1 << 12,
		BigIntCommitSize: 1 << 12,

		ModulusBase: 65340,
		Digits:      8,

		RingDegree:     1 << 12,
		LogRingModulus: []int{53, 53},

		CommitStdDev:       10,
		OpeningProofStdDev: 32,
		BlindStdDev:        math.Exp2(21),

		CommitRandStdDev:       20,
		OpeningProofRandStdDev: 64,
		BlindRandStdDev:        math.Exp2(22),

		OpenProofBound: math.Exp2(34.60),
		EvalProofBound: math.Exp2(52.28),
	}.Compile()
)

type TestCircuit struct {
	XNTT buckler.PublicWitness

	Y    buckler.Witness
	YNTT buckler.Witness

	YSum *big.Int

	AutIdx  int
	YAutNTT buckler.Witness

	YBound uint64

	ZNTT buckler.Witness
}

func (c *TestCircuit) Define(ctx *buckler.Context) {
	ctx.AddInfNormConstraint(c.Y, c.YBound)
	ctx.AddNTTConstraint(c.Y, c.YNTT)
	ctx.AddAutomorphismNTTConstraint(c.YNTT, c.AutIdx, c.YAutNTT)

	var multConstraint buckler.ArithmeticConstraint
	multConstraint.AddTerm(big.NewInt(1), c.XNTT, c.YNTT)
	multConstraint.AddTerm(big.NewInt(-1), nil, c.ZNTT)
	ctx.AddArithmeticConstraint(multConstraint)

	var sumConstraint buckler.ArithmeticConstraint
	sumConstraint.AddTerm(big.NewInt(1), nil, c.Y)
	ctx.AddSumCheckConstraintBig(sumConstraint, c.YSum)
}

func TestBuckler(t *testing.T) {
	us := celpc.NewUniformSamplerWithSeed(params, nil)
	ringQ := bigring.NewBigRing(params.Degree(), params.Modulus())
	bound := uint64(4)

	XNTT := ringQ.NewNTTPoly()
	Y := ringQ.NewPoly()
	YSum := big.NewInt(0)
	for i := 0; i < ringQ.Degree(); i++ {
		us.SampleModAssign(XNTT.Coeffs[i])
		Y.Coeffs[i].SetUint64(us.SampleN(bound))
		YSum.Add(YSum, Y.Coeffs[i])
	}
	YNTT := ringQ.ToNTTPoly(Y)
	ZNTT := ringQ.MulNTT(XNTT, YNTT)

	autIdx := 5
	YAutNTT := ringQ.AutomorphismNTT(YNTT, autIdx)

	ck := celpc.GenAjtaiCommitKey(params)
	c := TestCircuit{
		YSum:   YSum,
		YBound: bound,
		AutIdx: autIdx,
	}
	prover, verifier, err := buckler.Compile(params, &c)
	assert.NoError(t, err)

	assignment := TestCircuit{
		XNTT: XNTT.Coeffs,

		Y:    Y.Coeffs,
		YNTT: YNTT.Coeffs,

		YSum: YSum,

		AutIdx:  autIdx,
		YAutNTT: YAutNTT.Coeffs,

		YBound: bound,

		ZNTT: ZNTT.Coeffs,
	}

	pf, err := prover.Prove(ck, &assignment)
	assert.NoError(t, err)

	vf := verifier.Verify(ck, pf)
	assert.True(t, vf)

	// pfParallel, err := prover.ProveParallel(ck, &assignment)
	// assert.NoError(t, err)

	// vfParallel := verifier.Verify(ck, pfParallel)
	// assert.True(t, vfParallel)
}
