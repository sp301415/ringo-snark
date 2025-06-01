package buckler

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/celpc"
	"github.com/sp301415/ringo-snark/num"
)

// Encoder computes the encoding of a vector to a polynomial.
type Encoder struct {
	Parameters  celpc.Parameters
	EmbedDegree int

	StreamSampler *celpc.StreamSampler

	twInv       []*big.Int
	degreeInv   *big.Int
	barretConst *big.Int
	qBitLen     uint

	buffer encoderBuffer
}

type encoderBuffer struct {
	quo *big.Int
	u   *big.Int
	v   *big.Int
}

// NewEncoder creates a new Encoder.
func NewEncoder(params celpc.Parameters, embedDegree int) *Encoder {
	QSubOne := big.NewInt(0).Sub(params.Modulus(), big.NewInt(1))
	if big.NewInt(0).Mod(QSubOne, big.NewInt(int64(params.Degree()))).Sign() != 0 {
		panic("no Nth root of unity")
	}

	twInv := make([]*big.Int, params.Degree()/2)

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

	for i := 0; i < params.Degree()/2; i++ {
		twInv[i] = big.NewInt(0).Exp(g, big.NewInt(int64(params.Degree()-i)), params.Modulus())
	}
	num.BitReverseInPlace(twInv)

	degreeInv := big.NewInt(0).ModInverse(big.NewInt(int64(params.Degree())), params.Modulus())

	barretExp := big.NewInt(0).Lsh(big.NewInt(1), uint((params.Modulus().BitLen()<<1)+1))
	barretConst := big.NewInt(0).Div(barretExp, params.Modulus())

	return &Encoder{
		Parameters:  params,
		EmbedDegree: embedDegree,

		StreamSampler: celpc.NewStreamSampler(params),

		twInv:       twInv,
		degreeInv:   degreeInv,
		barretConst: barretConst,
		qBitLen:     uint(params.Modulus().BitLen()),

		buffer: newEncoderBuffer(params),
	}
}

// newEncoderBuffer creates a new encoderBuffer.
func newEncoderBuffer(params celpc.Parameters) encoderBuffer {
	return encoderBuffer{
		quo: big.NewInt(0).Set(params.Modulus()),
		u:   big.NewInt(0).Set(params.Modulus()),
		v:   big.NewInt(0).Set(params.Modulus()),
	}
}

// ShallowCopy creates a copy of Encoder that is thread-safe.
func (e *Encoder) ShallowCopy() *Encoder {
	return &Encoder{
		Parameters:  e.Parameters,
		EmbedDegree: e.EmbedDegree,

		StreamSampler: celpc.NewStreamSampler(e.Parameters),

		twInv:       e.twInv,
		degreeInv:   e.degreeInv,
		barretConst: e.barretConst,
		qBitLen:     e.qBitLen,

		buffer: newEncoderBuffer(e.Parameters),
	}
}

// Encode encodes a bigint vector to a polynomial.
// v should have length Parameters.Degree.
func (e *Encoder) Encode(x []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.EncodeAssign(x, pOut)
	return pOut
}

// EncodeAssign encodes a bigint vector to a polynomial and writes it to pOut.
// x should have length Parameters.Degree.
func (e *Encoder) EncodeAssign(x []*big.Int, pOut bigring.BigPoly) {
	for i := 0; i < e.Parameters.Degree(); i++ {
		pOut.Coeffs[i].Set(x[i])
	}
	for i := e.Parameters.Degree(); i < e.EmbedDegree; i++ {
		pOut.Coeffs[i].SetInt64(0)
	}

	t := 1
	for m := e.Parameters.Degree() >> 1; m >= 1; m >>= 1 {
		for i := 0; i < m; i++ {
			j1 := 2 * i * t
			j2 := j1 + t
			for j := j1; j < j2; j++ {
				e.buffer.u.Set(pOut.Coeffs[j])
				e.buffer.v.Set(pOut.Coeffs[j+t])

				pOut.Coeffs[j].Add(e.buffer.u, e.buffer.v)
				if pOut.Coeffs[j].Cmp(e.Parameters.Modulus()) >= 0 {
					pOut.Coeffs[j].Sub(pOut.Coeffs[j], e.Parameters.Modulus())
				}

				pOut.Coeffs[j+t].Sub(e.buffer.u, e.buffer.v)
				pOut.Coeffs[j+t].Mul(pOut.Coeffs[j+t], e.twInv[i])

				if pOut.Coeffs[j+t].Sign() < 0 {
					pOut.Coeffs[j+t].Mod(pOut.Coeffs[j+t], e.Parameters.Modulus())
				} else {
					e.buffer.quo.Mul(pOut.Coeffs[j+t], e.barretConst)
					e.buffer.quo.Rsh(e.buffer.quo, (e.qBitLen<<1)+1)
					e.buffer.quo.Mul(e.buffer.quo, e.Parameters.Modulus())
					pOut.Coeffs[j+t].Sub(pOut.Coeffs[j+t], e.buffer.quo)
					if pOut.Coeffs[j+t].Cmp(e.Parameters.Modulus()) >= 0 {
						pOut.Coeffs[j+t].Sub(pOut.Coeffs[j+t], e.Parameters.Modulus())
					}
				}
			}
		}
		t <<= 1
	}

	for i := 0; i < e.Parameters.Degree(); i++ {
		pOut.Coeffs[i].Mul(pOut.Coeffs[i], e.degreeInv)

		if pOut.Coeffs[i].Sign() < 0 {
			pOut.Coeffs[i].Mod(pOut.Coeffs[i], e.Parameters.Modulus())
		} else {
			e.buffer.quo.Mul(pOut.Coeffs[i], e.barretConst)
			e.buffer.quo.Rsh(e.buffer.quo, (e.qBitLen<<1)+1)
			e.buffer.quo.Mul(e.buffer.quo, e.Parameters.Modulus())
			pOut.Coeffs[i].Sub(pOut.Coeffs[i], e.buffer.quo)
			if pOut.Coeffs[i].Cmp(e.Parameters.Modulus()) >= 0 {
				pOut.Coeffs[i].Sub(pOut.Coeffs[i], e.Parameters.Modulus())
			}
		}
	}
}

// RandomEncode encodes a bigint vector to a polynomial with randomization.
// v should have length Parameters.Degree.
func (e *Encoder) RandomEncode(x []*big.Int) bigring.BigPoly {
	pOut := bigring.NewBigPoly(e.EmbedDegree)
	e.RandomEncodeAssign(x, pOut)
	return pOut
}

// RandomEncodeAssign encodes a bigint vector to a polynomial with randomization and writes it to pOut.
// v should have length Parameters.Degree.
func (e *Encoder) RandomEncodeAssign(x []*big.Int, pOut bigring.BigPoly) {
	e.EncodeAssign(x, pOut)

	e.StreamSampler.SampleModAssign(pOut.Coeffs[e.Parameters.Degree()])
	pOut.Coeffs[0].Sub(pOut.Coeffs[0], pOut.Coeffs[e.Parameters.Degree()])
	if pOut.Coeffs[0].Sign() < 0 {
		pOut.Coeffs[0].Add(pOut.Coeffs[0], e.Parameters.Modulus())
	}
}
