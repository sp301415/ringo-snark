package buckler

import (
	"math/big"
	"reflect"

	"github.com/sp301415/ringo-snark/celpc"
)

// Context is a context for compiling a circuit.
// It runs through the circuit and collects the information needed to compile it.
type Context struct {
	ringDegree int

	publicWitnessCount int64
	witnessCount       int64

	prePublicWitnessCount int64
	preWitnessCount       int64

	circuitType reflect.Type
	maxDegree   int

	arithConstraints    []ArithmeticConstraint
	sumCheckConstraints []ArithmeticConstraint
	sumCheckSums        []*big.Int

	linTransformers     []TransposeTransformer
	linCheckConstraints map[TransposeTransformer][][2]int64

	InfDecomposeBound    map[int64]*big.Int
	InfDecomposedWitness map[int64][]Witness

	TwoDecomposeBound    map[int64]*big.Int
	TwoDecomposeBase     map[int64]PublicWitness
	TwoDecomposeMask     map[int64]PublicWitness
	TwoDecomposedWitness map[int64]Witness
}

func newContext(params celpc.Parameters, walker *walker) *Context {
	return &Context{
		ringDegree: params.Degree(),

		publicWitnessCount: walker.publicWitnessCount,
		witnessCount:       walker.witnessCount,

		circuitType: walker.circuitType,
		maxDegree:   params.Degree() + 1,

		linCheckConstraints: make(map[TransposeTransformer][][2]int64),

		InfDecomposeBound:    make(map[int64]*big.Int),
		InfDecomposedWitness: make(map[int64][]Witness),

		TwoDecomposeBound:    make(map[int64]*big.Int),
		TwoDecomposeBase:     make(map[int64]PublicWitness),
		TwoDecomposeMask:     make(map[int64]PublicWitness),
		TwoDecomposedWitness: make(map[int64]Witness),
	}
}

// NewArithmeticConstraint creates a new arithmetic constraint.
func NewArithmeticConstraint() *ArithmeticConstraint {
	return &ArithmeticConstraint{}
}

// AddArithmeticConstraint adds an arithmetic constraint to the context.
func (ctx *Context) AddArithmeticConstraint(c ArithmeticConstraint) {
	ctx.arithConstraints = append(ctx.arithConstraints, c)

	for i := 0; i < len(c.witness); i++ {
		degree := 0
		if c.coeffsPublicWitness[i] == -1 {
			degree += ctx.ringDegree - 1
		}
		degree += len(c.witness[i]) * ctx.ringDegree
		degree += 1

		if degree > ctx.maxDegree {
			ctx.maxDegree = degree
		}
	}
}

// AddSumCheckConstraint add a sumcheck constraint to the context,
// where it checks if the sum of the witness is equal to bigint value.
func (ctx *Context) AddSumCheckConstraintBig(c ArithmeticConstraint, sum *big.Int) {
	ctx.sumCheckConstraints = append(ctx.sumCheckConstraints, c)
	ctx.sumCheckSums = append(ctx.sumCheckSums, sum)
}

// AddSumCheckConstraint add a sumcheck constraint to the context,
// where it checks if the sum of the witness is equal to uint64 value.
func (ctx *Context) AddSumCheckConstraint(c ArithmeticConstraint, sum uint64) {
	ctx.AddSumCheckConstraintBig(c, big.NewInt(0).SetUint64(sum))
}

// AddLinearConstrait adds a linear constraint to the context.
func (ctx *Context) AddLinearConstraint(transformer TransposeTransformer, wIn, wOut Witness) {
	linCheckDeg := 2 * ctx.ringDegree
	if ctx.maxDegree < linCheckDeg {
		ctx.maxDegree = linCheckDeg
	}

	if _, ok := ctx.linCheckConstraints[transformer]; !ok {
		ctx.linTransformers = append(ctx.linTransformers, transformer)
	}
	ctx.linCheckConstraints[transformer] = append(ctx.linCheckConstraints[transformer], [2]int64{wIn[0].Int64(), wOut[0].Int64()})
}

// AddInfNormConstraintBig adds an infinity-norm constraint to the context.
func (ctx *Context) AddInfNormConstraintBig(w Witness, bound *big.Int) {
	switch {
	case bound.Sign() < 0:
		return
	case bound.Sign() == 0:
		var zeroConstraint ArithmeticConstraint
		zeroConstraint.AddTerm(big.NewInt(1), nil, w)
		ctx.AddArithmeticConstraint(zeroConstraint)
		return
	case bound.Cmp(big.NewInt(1)) == 0:
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(big.NewInt(1), nil, w, w, w)
		ternaryConstraint.AddTerm(big.NewInt(-1), nil, w)
		ctx.AddArithmeticConstraint(ternaryConstraint)
		return
	}

	dcmpBase := getDecomposeBase(bound)

	id := w[0].Int64()
	wDcmp := make([]Witness, 0, len(dcmpBase))
	for i := ctx.witnessCount; i < ctx.witnessCount+int64(len(dcmpBase)); i++ {
		wDcmp = append(wDcmp, Witness{big.NewInt(i)})
	}
	ctx.InfDecomposedWitness[id] = wDcmp
	ctx.InfDecomposeBound[id] = bound
	ctx.witnessCount += int64(len(dcmpBase))

	for i := 0; i < len(dcmpBase); i++ {
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(big.NewInt(1), nil, wDcmp[i], wDcmp[i], wDcmp[i])
		ternaryConstraint.AddTerm(big.NewInt(-1), nil, wDcmp[i])
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	var decomposeConstraint ArithmeticConstraint
	decomposeConstraint.AddTerm(big.NewInt(1), nil, w)
	for i := 0; i < len(dcmpBase); i++ {
		decomposeConstraint.AddTerm(big.NewInt(0).Neg(dcmpBase[i]), nil, wDcmp[i])
	}
	ctx.AddArithmeticConstraint(decomposeConstraint)
}

// AddInfNormConstraint adds an infinity-norm constraint to the context.
func (ctx *Context) AddInfNormConstraint(w Witness, bound uint64) {
	ctx.AddInfNormConstraintBig(w, big.NewInt(0).SetUint64(bound))
}

// AddSqTwoNormConstraintBig adds a squared two-norm constraint to the context.
func (ctx *Context) AddSqTwoNormConstraintBig(w Witness, bound *big.Int) {
	id := w[0].Int64()
	wDcmp := Witness{big.NewInt(ctx.witnessCount)}
	ctx.witnessCount++

	pwBase := PublicWitness{big.NewInt(ctx.publicWitnessCount)}
	pwMask := PublicWitness{big.NewInt(ctx.publicWitnessCount + 1)}
	ctx.publicWitnessCount += 2

	ctx.TwoDecomposeBound[id] = bound
	ctx.TwoDecomposedWitness[id] = wDcmp
	ctx.TwoDecomposeBase[id] = pwBase
	ctx.TwoDecomposeMask[id] = pwMask

	var binaryConstraint ArithmeticConstraint
	binaryConstraint.AddTerm(big.NewInt(1), nil, wDcmp, wDcmp)
	binaryConstraint.AddTerm(big.NewInt(-1), pwMask, wDcmp)
	ctx.AddArithmeticConstraint(binaryConstraint)

	var decomposeConstraint ArithmeticConstraint
	decomposeConstraint.AddTerm(big.NewInt(1), nil, w, w)
	decomposeConstraint.AddTerm(big.NewInt(-1), pwBase, wDcmp)
	ctx.AddSumCheckConstraint(decomposeConstraint, 0)
}

// AddSqTwoNormConstraint adds a squared two-norm constraint to the context.
func (ctx *Context) AddSqTwoNormConstraint(w Witness, bound uint64) {
	ctx.AddSqTwoNormConstraintBig(w, big.NewInt(0).SetUint64(bound))
}

// HasRowCheck returns true if the row check is needed.
func (ctx *Context) HasRowCheck() bool {
	return len(ctx.arithConstraints) > 0
}

// HasSumCheck returns true if the sum check is needed.
func (ctx *Context) HasSumCheck() bool {
	return len(ctx.sumCheckConstraints) > 0
}

// HasLinCheck returns true if the linear check is needed.
func (ctx *Context) HasLinCheck() bool {
	return len(ctx.linTransformers) > 0
}
