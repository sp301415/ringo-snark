package bigring

import (
	"math/big"
)

// Reducer computes the barrett reduction.
// It assumes that the inputs are between -2q^2 and 2q^2.
type Reducer struct {
	Q *big.Int

	rBound   *big.Int
	qBitLen  uint
	barConst *big.Int

	quo  *big.Int
	quoQ *big.Int
}

// NewReducer creates a new Reducer for the given modulus q.
func NewReducer(q *big.Int) *Reducer {
	if q.Sign() <= 0 {
		panic("modulus must be positive")
	}

	qBitLen := uint(q.BitLen())
	exp := big.NewInt(0).Lsh(big.NewInt(1), (qBitLen<<1)+1)
	barConst := big.NewInt(0).Div(exp, q)

	rBound := big.NewInt(0).Mul(q, q)
	rBound.Lsh(rBound, 1)

	return &Reducer{
		Q: q,

		rBound:   rBound,
		qBitLen:  qBitLen,
		barConst: barConst,

		quo:  big.NewInt(0),
		quoQ: big.NewInt(0),
	}
}

// Shallowcopy creates a copy of Reducer that is thread-safe.
func (r *Reducer) ShallowCopy() *Reducer {
	return &Reducer{
		Q: r.Q,

		rBound:   r.rBound,
		qBitLen:  r.qBitLen,
		barConst: r.barConst,

		quo:  big.NewInt(0),
		quoQ: big.NewInt(0),
	}
}

// Reduce performs the Barrett reduction on the input x.
func (r *Reducer) Reduce(x *big.Int) {
	if x.Sign() < 0 {
		x.Add(x, r.rBound)
	}

	if x.Sign() < 0 || x.Cmp(r.rBound) >= 0 {
		panic("input must be in the range [0, 2q^2)")
	}

	r.quo.Mul(x, r.barConst)
	r.quo.Rsh(r.quo, (r.qBitLen<<1)+1)
	r.quoQ.Mul(r.quo, r.Q)
	x.Sub(x, r.quoQ)
	if x.Cmp(r.Q) >= 0 {
		x.Sub(x, r.Q)
	}
}
