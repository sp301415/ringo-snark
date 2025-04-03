package buckler

import (
	"math/big"
	"slices"

	"github.com/sp301415/rlwe-piop/celpc"
)

// Context is a context for compiling a circuit.
// It runs through the circuit and collects the information needed to compile it.
type Context struct {
	Parameters celpc.Parameters

	publicWitnessCount int64
	witnessCount       int64

	maxDegree int

	arithConstraints []ArithmeticConstraint

	decomposedWitness map[int64][]Witness

	nttConstraints    [][2]int64
	autConstraintsIdx []int
	autConstraints    [][][2]int64
}

func newContext(params celpc.Parameters, walker *walker) *Context {
	return &Context{
		Parameters: params,

		publicWitnessCount: walker.publicWitnessCount,
		witnessCount:       walker.witnessCount,

		maxDegree: 2 * params.Degree(),

		decomposedWitness: make(map[int64][]Witness),
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
			degree += ctx.Parameters.Degree() - 1
		}
		degree += len(c.witness[i]) * (2*ctx.Parameters.Degree() - 1)
		degree += 1

		if degree > ctx.maxDegree {
			ctx.maxDegree = degree
		}
	}
}

// AddNormConstraint adds an two-norm constraint to the context.
func (ctx *Context) AddNormConstraint(w Witness, logBound uint64) {
	if logBound == 0 {
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(1, nil, nil, w, w, w)
		ternaryConstraint.AddTerm(-1, nil, nil, w)
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	id := w[0].Int64()
	wDecomposed := make([]Witness, 0, logBound+1)
	for i := ctx.witnessCount; i < ctx.witnessCount+int64(logBound+1); i++ {
		wDecomposed = append(wDecomposed, Witness{big.NewInt(i)})
	}
	ctx.decomposedWitness[id] = wDecomposed
	ctx.witnessCount += int64(logBound + 1)

	for i := 0; i < len(wDecomposed); i++ {
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(1, nil, nil, wDecomposed[i], wDecomposed[i], wDecomposed[i])
		ternaryConstraint.AddTerm(-1, nil, nil, wDecomposed[i])
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	var decomposeConstraint ArithmeticConstraint
	decomposeConstraint.AddTerm(1, nil, nil, w)
	decomposeConstraint.AddTerm(-1, nil, nil, wDecomposed[0])
	for i := 1; i < len(wDecomposed); i++ {
		decomposeConstraint.AddTerm(-(1 << (i - 1)), nil, nil, wDecomposed[i])
	}
	ctx.AddArithmeticConstraint(decomposeConstraint)
}

// AddNTTConstraint adds an NTT constraint to the context.
func (ctx *Context) AddNTTConstraint(w, wNTT Witness) {
	linCheckDeg := 3*ctx.Parameters.Degree() - 2
	if ctx.maxDegree < linCheckDeg {
		ctx.maxDegree = linCheckDeg
	}

	ctx.nttConstraints = append(ctx.nttConstraints, [2]int64{w[0].Int64(), wNTT[0].Int64()})
}

// AddAutomorphismNTTConstraint adds an automorphism X -> X^d over NTT constraint to the context.
func (ctx *Context) AddAutomorphismNTTConstraint(wNTT Witness, d int, wAutNTT Witness) {
	linCheckDeg := 3*ctx.Parameters.Degree() - 2
	if ctx.maxDegree < linCheckDeg {
		ctx.maxDegree = linCheckDeg
	}

	d %= 2 * ctx.Parameters.Degree()
	idx := slices.Index(ctx.autConstraintsIdx, d)
	if idx == -1 {
		ctx.autConstraintsIdx = append(ctx.autConstraintsIdx, d)
		ctx.autConstraints = append(ctx.autConstraints, [][2]int64{{wNTT[0].Int64(), wAutNTT[0].Int64()}})
	} else {
		ctx.autConstraints[idx] = append(ctx.autConstraints[idx], [2]int64{wNTT[0].Int64(), wAutNTT[0].Int64()})
	}
}

// HasRowCheck returns true if the row check is needed.
func (ctx *Context) HasRowCheck() bool {
	return len(ctx.arithConstraints) > 0
}

// HasLinearCheck returns true if the linear check is needed.
func (ctx *Context) HasLinearCheck() bool {
	return len(ctx.nttConstraints) > 0 || len(ctx.autConstraints) > 0
}
