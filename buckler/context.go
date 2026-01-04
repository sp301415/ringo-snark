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
	// arithMaxRank is the maximum rank of arithmetic constraints.
	arithCheckMaxRank int
	// sumCheckMaxRank is the maximum rank of sumcheck constraints.
	sumCheckMaxRank int

	arithConstraints []ArithmeticConstraint[E]

	sumCheckConstraints []ArithmeticConstraint[E]
	sumCheckSums        []*big.Int

	linTransformers     []LinearTransformer[E]
	linCheckConstraints map[LinearTransformer[E]][][2]uint64

	infDcmpBound   map[uint64]*big.Int
	infDcmpWitness map[uint64][]Witness[E]

	twoDcmpBound   map[uint64]*big.Int
	twoDcmpBase    map[uint64]PublicWitness[E]
	twoDcmpMask    map[uint64]PublicWitness[E]
	twoDcmpWitness map[uint64]Witness[E]
}

// newContext creates a new [Context].
func newContext[E num.Uint[E]](rank int, walker *walker[E]) *Context[E] {
	return &Context[E]{
		rank: rank,

		pwCnt: walker.pwCnt,
		wCnt:  walker.wCnt,

		circType: walker.circuitType,

		linCheckConstraints: make(map[LinearTransformer[E]][][2]uint64),

		infDcmpBound:   make(map[uint64]*big.Int),
		infDcmpWitness: make(map[uint64][]Witness[E]),

		twoDcmpBound:   make(map[uint64]*big.Int),
		twoDcmpBase:    make(map[uint64]PublicWitness[E]),
		twoDcmpMask:    make(map[uint64]PublicWitness[E]),
		twoDcmpWitness: make(map[uint64]Witness[E]),
	}
}

// AddArithmeticConstraint adds an arithmetic constraint to the context.
func (ctx *Context[E]) AddArithmeticConstraint(c ArithmeticConstraint[E]) {
	ctx.arithConstraints = append(ctx.arithConstraints, c)
	ctx.arithCheckMaxRank = max(ctx.arithCheckMaxRank, c.maxRank(ctx.rank))
}

// AddSumCheckConstraint adds a sumcheck constraint to the context.
func (ctx *Context[E]) AddSumCheckConstraint(c ArithmeticConstraint[E], sum uint64) {
	ctx.AddSumCheckConstraintBig(c, new(big.Int).SetUint64(sum))
}

// AddSumCheckConstraintBig adds a sumcheck constraint to the context.
func (ctx *Context[E]) AddSumCheckConstraintBig(c ArithmeticConstraint[E], sum *big.Int) {
	ctx.sumCheckConstraints = append(ctx.sumCheckConstraints, c)
	ctx.sumCheckSums = append(ctx.sumCheckSums, sum)
	ctx.sumCheckMaxRank = max(ctx.sumCheckMaxRank, c.maxRank(ctx.rank))
}

// AddLinearConstraint adds a linear constraint to the context.
func (ctx *Context[E]) AddLinearConstraint(wOut, wIn Witness[E], transformer LinearTransformer[E]) {
	if ctx.arithCheckMaxRank < 2*ctx.rank-1 {
		ctx.arithCheckMaxRank = 2*ctx.rank - 1
	}

	if _, ok := ctx.linCheckConstraints[transformer]; !ok {
		ctx.linTransformers = append(ctx.linTransformers, transformer)
	}

	wInID := witnessToID(wIn)
	wOutID := witnessToID(wOut)
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

	id := witnessToID(w)
	wDcmp := make([]Witness[E], 0, len(dcmpBase))
	for i := ctx.wCnt; i < ctx.wCnt+uint64(len(dcmpBase)); i++ {
		wDcmp = append(wDcmp, idToWitness[E, Witness[E]](i))
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
	var z E

	id := witnessToID(w)
	wDcmp := idToWitness[E, Witness[E]](ctx.wCnt)
	ctx.wCnt += 1

	pwBase := idToWitness[E, PublicWitness[E]](ctx.pwCnt)
	pwMask := idToWitness[E, PublicWitness[E]](ctx.pwCnt + 1)
	ctx.pwCnt += 2

	ctx.twoDcmpBound[id] = bound
	ctx.twoDcmpBase[id] = pwBase
	ctx.twoDcmpMask[id] = pwMask
	ctx.twoDcmpWitness[id] = wDcmp

	var binConstraint ArithmeticConstraint[E]
	binConstraint.AddTerm(z.New().SetInt64(1), nil, wDcmp, wDcmp)
	binConstraint.AddTerm(z.New().SetInt64(-1), pwMask, wDcmp)
	ctx.AddArithmeticConstraint(binConstraint)

	var dcmpConstraint ArithmeticConstraint[E]
	dcmpConstraint.AddTerm(z.New().SetInt64(1), nil, w, w)
	dcmpConstraint.AddTerm(z.New().SetInt64(-1), pwBase, wDcmp)
	ctx.AddSumCheckConstraint(dcmpConstraint, 0)
}

// batch returns the number of polynomials to commit.
func (ctx *Context[E]) batch() int {
	batch := int(ctx.wCnt)

	if len(ctx.arithConstraints) > 0 {
		batch += 1
	}
	if len(ctx.linCheckConstraints) > 0 {
		batch += 4
	}
	if len(ctx.sumCheckConstraints) > 0 {
		batch += 4
	}

	return batch
}

// commitRank returns the maximum rank of committed polynomials.
func (ctx *Context[E]) commitRank() int {
	rank := 0
	if ctx.wCnt > 0 {
		rank = ctx.rank + 1
	}

	for i := range ctx.arithConstraints {
		quoRank := ctx.arithConstraints[i].maxRank(ctx.rank) - ctx.rank
		rank = max(rank, quoRank)
	}

	if len(ctx.linCheckConstraints) > 0 {
		maskRank := 2 * ctx.rank
		rank = max(rank, maskRank)
	}

	for i := range ctx.sumCheckConstraints {
		maskRank := ctx.sumCheckConstraints[i].maxRank(ctx.rank) + ctx.rank + 1
		rank = max(rank, maskRank)
	}

	return rank
}

// HasArithmeticCheck returns if there is any arithmetic constraint.
func (ctx *Context[E]) HasArithmeticCheck() bool {
	return len(ctx.arithConstraints) > 0
}

// HasLinearCheck returns if there is any linear constraint.
func (ctx *Context[E]) HasLinearCheck() bool {
	return len(ctx.linCheckConstraints) > 0
}

// HasSumCheck returns if there is any sumcheck constraint.
func (ctx *Context[E]) HasSumCheck() bool {
	return len(ctx.sumCheckConstraints) > 0
}
