package buckler

import (
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/math/num"
)

// Context is a context for compiling a circuit.
// It runs through the circuit and collects the information needed to compile it.
type Context[E num.Uint[E]] struct {
	rank int

	// pwCnt is the number of public witnesses.
	pwCnt uint64
	// wCnt is the number of witnesses.
	wCnt uint64

	// circType is the [reflect.Type] of the underlying circuit.
	circType reflect.Type
	// maxRank is the maximum rank during proof generation.
	maxRank int

	arithConstraints []ArithmeticConstraint[E]

	sumCheckConstraints []ArithmeticConstraint[E]
	sumCheckSums        []*big.Int

	linTransformers     []LinearTransformer[E]
	linCheckConstraints map[LinearTransformer[E]][][2]uint64

	infDcmpBound   map[uint64]*big.Int
	infDcmpWitness map[uint64][]Witness[E]
}

// newContext creates a new [Context].
func newContext[E num.Uint[E]](rank int, walker *walker[E]) *Context[E] {
	return &Context[E]{
		rank: rank,

		pwCnt: walker.pwCnt,
		wCnt:  walker.wCnt,

		circType: walker.circuitType,
		maxRank:  rank,

		linCheckConstraints: make(map[LinearTransformer[E]][][2]uint64),

		infDcmpBound:   make(map[uint64]*big.Int),
		infDcmpWitness: make(map[uint64][]Witness[E]),
	}
}

// AddArithmeticConstraint adds an arithmetic constraint to the context.
func (ctx *Context[E]) AddArithmeticConstraint(c ArithmeticConstraint[E]) {
	ctx.arithConstraints = append(ctx.arithConstraints, c)
	for i := range c.witness {
		deg := 0
		if c.coeffsPublicWitness[i] > 0 {
			deg += ctx.rank - 1
		}
		deg += len(c.witness[i]) * ctx.rank
		if deg+1 > ctx.maxRank {
			ctx.maxRank = deg + 1
		}
	}
}

// AddSumCheckConstraint adds a sumcheck constraint to the context.
func (ctx *Context[E]) AddSumCheckConstraint(c ArithmeticConstraint[E], sum uint64) {
	ctx.AddSumCheckConstraintBig(c, new(big.Int).SetUint64(sum))
}

// AddSumCheckConstraintBig adds a sumcheck constraint to the context.
func (ctx *Context[E]) AddSumCheckConstraintBig(c ArithmeticConstraint[E], sum *big.Int) {
	ctx.sumCheckConstraints = append(ctx.sumCheckConstraints, c)
	ctx.sumCheckSums = append(ctx.sumCheckSums, sum)
}

// AddLinearConstraint adds a linear constraint to the context.
func (ctx *Context[E]) AddLinearConstraint(transformer LinearTransformer[E], wOut, wIn Witness[E]) {
	if ctx.maxRank < 2*ctx.rank-1 {
		ctx.maxRank = 2*ctx.rank - 1
	}

	if _, ok := ctx.linCheckConstraints[transformer]; !ok {
		ctx.linTransformers = append(ctx.linTransformers, transformer)
	}

	digits := make([]uint64, wIn[0].Limb())
	wIn[0].Slice(digits)
	wInID := digits[0]
	wOut[0].Slice(digits)
	wOutID := digits[0]
	ctx.linCheckConstraints[transformer] = append(ctx.linCheckConstraints[transformer], [2]uint64{wOutID, wInID})
}

// AddInfNormConstraint adds an infinity-norm constraint to the context.
func (ctx *Context[E]) AddInfNormConstraint(w Witness[E], bound uint64) {
	ctx.AddInfNormConstraintBig(w, big.NewInt(0).SetUint64(bound))
}

// AddInfNormConstraintBig adds an infinity-norm constraint to the context.
func (ctx *Context[E]) AddInfNormConstraintBig(w Witness[E], bound *big.Int) {
	var z E

	switch {
	case bound.Sign() < 0:
		return
	case bound.Sign() == 0:
		var zeroConstraint ArithmeticConstraint[E]
		zeroConstraint.AddTerm(z.New().SetInt64(1), nil, w)
		ctx.AddArithmeticConstraint(zeroConstraint)
		return
	case bound.Cmp(big.NewInt(1)) == 0:
		var ternaryConstraint ArithmeticConstraint[E]
		ternaryConstraint.AddTerm(z.New().SetInt64(1), nil, w, w, w)
		ternaryConstraint.AddTerm(z.New().SetInt64(-1), nil, w)
		ctx.AddArithmeticConstraint(ternaryConstraint)
		return
	}

	dcmpBase := decomposeBase(bound)

	digits := make([]uint64, z.Limb())
	w[0].Slice(digits)
	id := digits[0]
	wDcmp := make([]Witness[E], 0, len(dcmpBase))
	for i := ctx.wCnt; i < ctx.wCnt+uint64(len(dcmpBase)); i++ {
		wDcmp = append(wDcmp, Witness[E]{z.New().SetUint64((i + 1) << 1)})
	}
	ctx.infDcmpWitness[id] = wDcmp
	ctx.infDcmpBound[id] = bound
	ctx.wCnt += uint64(len(dcmpBase))

	for i := range wDcmp {
		var ternaryConstraint ArithmeticConstraint[E]
		ternaryConstraint.AddTerm(z.New().SetInt64(1), nil, wDcmp[i], wDcmp[i], wDcmp[i])
		ternaryConstraint.AddTerm(z.New().SetInt64(-1), nil, wDcmp[i])
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	var dcmpConstraint ArithmeticConstraint[E]
	dcmpConstraint.AddTerm(z.New().SetInt64(1), nil, w)
	for i := range dcmpBase {
		negBase := z.New().SetBigInt(dcmpBase[i])
		dcmpConstraint.AddTerm(negBase.Neg(negBase), nil, wDcmp[i])
	}
	ctx.AddArithmeticConstraint(dcmpConstraint)
}

// AddSqTwoNormConstraint adds a squared two-norm constraint to the context.
// Note that this only proves the constraint over modulo witness modulus.
func (ctx *Context[E]) AddSqTwoNormConstraint(w Witness[E], bound uint64) {
	ctx.AddSqNormConstraintBig(w, big.NewInt(0).SetUint64(bound))
}

// AddSqTwoNormConstraintBig adds a squared two-norm constraint to the context.
// Note that this only proves the constraint over modulo witness modulus.
func (ctx *Context[E]) AddSqNormConstraintBig(w Witness[E], bound *big.Int) {
}
