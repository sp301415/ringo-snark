package buckler

import (
	"math/big"
	"reflect"
	"slices"

	"github.com/sp301415/cyclone/celpc"
)

// Context is a context for compiling a circuit.
// It runs through the circuit and collects the information needed to compile it.
type Context struct {
	Parameters celpc.Parameters

	publicWitnessCount int64
	witnessCount       int64

	circuitType reflect.Type
	maxDegree   int

	arithConstraints []ArithmeticConstraint

	decomposeBound    map[int64]uint64
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

		circuitType: walker.circuitType,
		maxDegree:   params.Degree() + 1,

		decomposeBound:    make(map[int64]uint64),
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
		degree += len(c.witness[i]) * ctx.Parameters.Degree()
		degree += 1

		if degree > ctx.maxDegree {
			ctx.maxDegree = degree
		}
	}
}

// AddInfNormConstraint adds an infinity-norm constraint to the context.
func (ctx *Context) AddInfNormConstraint(w Witness, bound uint64) {
	switch bound {
	case 0:
		var zeroConstraint ArithmeticConstraint
		zeroConstraint.AddTerm(1, nil, nil, w)
		ctx.AddArithmeticConstraint(zeroConstraint)
		return

	case 1:
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(1, nil, nil, w, w, w)
		ternaryConstraint.AddTerm(-1, nil, nil, w)
		ctx.AddArithmeticConstraint(ternaryConstraint)
		return
	}

	dcmpBase := getDcmpBase(bound)

	id := w[0].Int64()
	wDcmp := make([]Witness, 0, len(dcmpBase))
	for i := ctx.witnessCount; i < ctx.witnessCount+int64(len(dcmpBase)); i++ {
		wDcmp = append(wDcmp, Witness{big.NewInt(i)})
	}
	ctx.decomposedWitness[id] = wDcmp
	ctx.decomposeBound[id] = bound
	ctx.witnessCount += int64(len(dcmpBase))

	for i := 0; i < len(dcmpBase); i++ {
		var ternaryConstraint ArithmeticConstraint
		ternaryConstraint.AddTerm(1, nil, nil, wDcmp[i], wDcmp[i], wDcmp[i])
		ternaryConstraint.AddTerm(-1, nil, nil, wDcmp[i])
		ctx.AddArithmeticConstraint(ternaryConstraint)
	}

	var decomposeConstraint ArithmeticConstraint
	decomposeConstraint.AddTerm(1, nil, nil, w)
	for i := 0; i < len(dcmpBase); i++ {
		decomposeConstraint.AddTerm(-int64(dcmpBase[i]), nil, nil, wDcmp[i])
	}
	ctx.AddArithmeticConstraint(decomposeConstraint)
}

// AddNTTConstraint adds an NTT constraint to the context.
func (ctx *Context) AddNTTConstraint(w, wNTT Witness) {
	linCheckDeg := 2 * ctx.Parameters.Degree()
	if ctx.maxDegree < linCheckDeg {
		ctx.maxDegree = linCheckDeg
	}

	ctx.nttConstraints = append(ctx.nttConstraints, [2]int64{w[0].Int64(), wNTT[0].Int64()})
}

// AddAutomorphismNTTConstraint adds an automorphism X -> X^d over NTT constraint to the context.
func (ctx *Context) AddAutomorphismNTTConstraint(wNTT Witness, d int, wAutNTT Witness) {
	linCheckDeg := 2 * ctx.Parameters.Degree()
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
