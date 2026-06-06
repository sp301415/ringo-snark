package bigpoly

import (
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/vec"
)

// CyclotomicOperator evaluates polynomial over power-of-two cyclotomic ring.
type CyclotomicOperator[E bignum.Uint[E]] struct {
	*baseOperator[E]
}

// NewCyclotomicEvaluator creates a new [CyclotomicOperator].
func NewCyclotomicEvaluator[E bignum.Uint[E]](rank int) *CyclotomicOperator[E] {
	return &CyclotomicOperator[E]{
		baseOperator: newBaseOperator(rank, NewCyclotomicTransformer[E](rank)),
	}
}

// Aut returns Aut(p, idx).
func (op *CyclotomicOperator[E]) Aut(p *Poly[E], idx int) *Poly[E] {
	pOut := op.NewPoly(p.IsNTT)
	op.AutTo(pOut, p, idx)
	return pOut
}

// AutTo computes pOut = Aut(p, idx).
func (op *CyclotomicOperator[E]) AutTo(pOut, p *Poly[E], idx int) {
	checkUnaryOperable(op.rank, pOut, p)

	if idx%2 == 0 {
		panic("AutTo: idx must be odd")
	}

	idx %= 2 * op.rank
	if idx < 0 {
		idx += 2 * op.rank
	}

	if p.IsNTT {
		op.autNTTTo(pOut, p, idx)
	} else {
		op.autTo(pOut, p, idx)
	}
}

// autTo computes pOut = Aut(p, idx).
func (op *CyclotomicOperator[E]) autTo(pOut, p *Poly[E], idx int) {
	pBuf := op.baseOperator.pool.Get().(*Poly[E])
	defer op.baseOperator.pool.Put(pBuf)

	for i := 0; i < op.rank; i++ {
		j := (i * idx) % (2 * op.rank)
		if j < op.rank {
			pBuf.Coeffs[j].Set(p.Coeffs[i])
		} else {
			pBuf.Coeffs[j-op.rank].Neg(p.Coeffs[i])
		}
	}

	pOut.CopyFrom(pBuf)
	pOut.IsNTT = false
}

// autNTTTo computes pOut = Aut(p, idx).
func (op *CyclotomicOperator[E]) autNTTTo(pOut, p *Poly[E], idx int) {
	pBuf := op.baseOperator.pool.Get().(*Poly[E])
	defer op.baseOperator.pool.Put(pBuf)

	pBuf.CopyFrom(p)
	vec.BitReverseInPlace(pBuf.Coeffs)

	for i := 0; i < op.rank; i++ {
		j := ((2*i + 1) * idx) % (2 * op.rank)
		j = (j - 1) >> 1
		pOut.Coeffs[i].Set(pBuf.Coeffs[j])
	}

	vec.BitReverseInPlace(pOut.Coeffs)
	pOut.IsNTT = true
}

// FwdNTT returns FwdNTT(p).
func (op *CyclotomicOperator[E]) FwdNTT(p *Poly[E]) *Poly[E] {
	pOut := op.NewPoly(true)
	op.FwdNTTTo(pOut, p)
	return pOut
}

// ModSwitch switches the modulus of pBig of modulus qBig.
func (op *CyclotomicOperator[E]) ModSwitch(pBig []*big.Int, qBig *big.Int) *Poly[E] {
	pOut := op.NewPoly(false)
	op.ModSwitchTo(pOut, pBig, qBig)
	return pOut
}

// ModSwitchTo switches the modulus of pBig of modulus q and writes to pOut.
func (op *CyclotomicOperator[E]) ModSwitchTo(pOut *Poly[E], pBig []*big.Int, qBig *big.Int) {
	if len(pBig) != op.rank {
		panic("input size not consistent")
	}

	var z E

	q := z.New().SetInt64(-1).BigInt(new(big.Int))
	q.Add(q, big.NewInt(1))
	qBigHalf := new(big.Int).Rsh(qBig, 1)

	c, cRem := new(big.Int), new(big.Int)
	for i := range op.rank {
		c.Mul(pBig[i], q)
		cRem.Mod(c, qBig)
		if cRem.Cmp(qBigHalf) > 0 {
			cRem.Sub(cRem, qBig)
		}
		c.Sub(c, cRem)
		c.Div(c, qBig)
		c.Mod(c, q)
		pOut.Coeffs[i].SetBigInt(c)
	}

	pOut.IsNTT = false
}
