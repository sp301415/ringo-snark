package buckler

import (
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/math/bignum"
)

// Context is a context for compiling a circuit.
// It runs through the circuit and collects the information needed to compile it.
type Context[E bignum.Uint[E]] struct {
	rank int

	// pwCnt is the number of public witnesses.
	pwCnt uint64
	// wCnt is the number of witnesses.
	wCnt uint64

	// wSecond are the witnesses in the second round.
	wSecond []Witness[E]

	// circType is the [reflect.Type] of the underlying circuit.
	circType reflect.Type
	// arithMaxRank is the maximum rank of arithmetic constraints.
	arithCheckMaxRank int
	// sumCheckMaxRank is the maximum rank of sumcheck constraints.
	sumCheckMaxRank int

	arithConstraints []ArithmeticConstraint[E]

	sumCheckConstraints []ArithmeticConstraint[E]
	sumCheckSums        []*big.Int

	linCheckers         []LinearChecker[E]
	linCheckConstraints map[LinearChecker[E]][][2]uint64

	infDcmpBound   map[uint64]*big.Int
	infDcmpWitness map[uint64][]Witness[E]

	twoDcmpBound   map[uint64]*big.Int
	twoDcmpBase    map[uint64]PublicWitness[E]
	twoDcmpMask    map[uint64]PublicWitness[E]
	twoDcmpWitness map[uint64]Witness[E]

	projChecker        LinearChecker[E]
	projWitness        map[uint64]Witness[E]
	projInfDcmpBound   map[uint64]*big.Int
	projInfDcmpWitness map[uint64]Witness[E]
}

// newContext creates a new [Context].
func newContext[E bignum.Uint[E]](rank int, walker *walker[E]) *Context[E] {
	return &Context[E]{
		rank: rank,

		pwCnt: walker.pwCnt,
		wCnt:  walker.wCnt,

		circType: walker.circuitType,

		linCheckConstraints: make(map[LinearChecker[E]][][2]uint64),

		infDcmpBound:   make(map[uint64]*big.Int),
		infDcmpWitness: make(map[uint64][]Witness[E]),

		twoDcmpBound:   make(map[uint64]*big.Int),
		twoDcmpBase:    make(map[uint64]PublicWitness[E]),
		twoDcmpMask:    make(map[uint64]PublicWitness[E]),
		twoDcmpWitness: make(map[uint64]Witness[E]),

		projWitness:        make(map[uint64]Witness[E]),
		projInfDcmpBound:   make(map[uint64]*big.Int),
		projInfDcmpWitness: make(map[uint64]Witness[E]),
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
func (ctx *Context[E]) AddLinearConstraint(wOut, wIn Witness[E], chker LinearChecker[E]) {
	if ctx.arithCheckMaxRank < 2*ctx.rank-1 {
		ctx.arithCheckMaxRank = 2*ctx.rank - 1
	}

	if _, ok := ctx.linCheckConstraints[chker]; !ok {
		ctx.linCheckers = append(ctx.linCheckers, chker)
	}

	wInID := witnessToID(wIn)
	wOutID := witnessToID(wOut)
	ctx.linCheckConstraints[chker] = append(ctx.linCheckConstraints[chker], [2]uint64{wOutID, wInID})
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
		zeroConstraint.AddTermWithConst(z.New().SetInt64(1), nil, w)
		ctx.AddArithmeticConstraint(zeroConstraint)
		return
	case bound.Cmp(big.NewInt(1)) == 0:
		var ternaryConstraint ArithmeticConstraint[E]
		ternaryConstraint.AddTermWithConst(z.New().SetInt64(1), nil, w, w, w)
		ternaryConstraint.AddTermWithConst(z.New().SetInt64(-1), nil, w)
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
		ternaryConstraint.AddTermWithConst(z.New().SetInt64(1), nil, wDcmp[i], wDcmp[i], wDcmp[i])
		ternaryConstraint.AddTermWithConst(z.New().SetInt64(-1), nil, wDcmp[i])
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	var dcmpConstraint ArithmeticConstraint[E]
	dcmpConstraint.AddTermWithConst(z.New().SetInt64(1), nil, w)
	for i := range dcmpBase {
		negBase := z.New().SetBigInt(dcmpBase[i])
		dcmpConstraint.AddTermWithConst(negBase.Neg(negBase), nil, wDcmp[i])
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
	binConstraint.AddTermWithConst(z.New().SetInt64(1), nil, wDcmp, wDcmp)
	binConstraint.AddTermWithConst(z.New().SetInt64(-1), pwMask, wDcmp)
	ctx.AddArithmeticConstraint(binConstraint)

	var dcmpConstraint ArithmeticConstraint[E]
	dcmpConstraint.AddTermWithConst(z.New().SetInt64(1), nil, w, w)
	dcmpConstraint.AddTermWithConst(z.New().SetInt64(-1), pwBase, wDcmp)
	ctx.AddSumCheckConstraint(dcmpConstraint, 0)
}

// AddApproxInfNormConstraint adds a approximate inf-norm constraint to the context.
// The slack is around 19.5 * sqrt(rank).
func (ctx *Context[E]) AddApproxInfNormConstraint(w Witness[E], bound uint64) {
	ctx.AddApproxInfNormConstraintBig(w, big.NewInt(0).SetUint64(bound))
}

// AddApproxInfNormConstraint adds a approximate inf-norm constraint to the context.
// The slack is around 19.5 * sqrt(rank).
func (ctx *Context[E]) AddApproxInfNormConstraintBig(w Witness[E], bound *big.Int) {
	if ctx.projChecker == nil {
		ctx.projChecker = newProjChecker[E](ctx.rank)
	}

	wProj := idToWitness[E, Witness[E]](ctx.wCnt)
	ctx.wCnt++

	ctx.AddLinearConstraint(wProj, w, ctx.projChecker)
	ctx.projWitness[witnessToID(w)] = wProj

	wProjDcmp := idToWitness[E, Witness[E]](ctx.wCnt)
	ctx.wCnt++

	slackBound := new(big.Int).SetUint64(uint64(ctx.rank))
	slackBound.Mul(slackBound, bound)
	ctx.projInfDcmpBound[witnessToID(wProj)] = slackBound
	ctx.projInfDcmpWitness[witnessToID(wProj)] = wProjDcmp
	ctx.AddLinearConstraint(wProj, wProjDcmp, newProjRecomposeChecker[E](slackBound))
	// ctx.AddInfNormConstraint(wProjDcmp, 1)

	ctx.wSecond = append(ctx.wSecond, wProj, wProjDcmp)
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
