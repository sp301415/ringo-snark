package celpc

import (
	"math/big"

	"github.com/tuneinsight/lattigo/v6/ring"
)

// RandomOracle is a random oracle.
type RandomOracle struct {
	*UniformSampler
}

// NewRandomOracle creates a new RandomOracle.
func NewRandomOracle(params Parameters) *RandomOracle {
	return &RandomOracle{
		UniformSampler: NewUniformSamplerWithSeed(params, nil),
	}
}

// WriteBigInt writes a big.Int to the random oracle.
func (o *RandomOracle) WriteBigInt(x *big.Int) {
	_, err := o.Write(x.Bytes())
	if err != nil {
		panic(err)
	}
}

// WritePoly writes a polynomial to the random oracle.
func (o *RandomOracle) WritePoly(p ring.Poly) {
	_, err := p.WriteTo(o)
	if err != nil {
		panic(err)
	}
}

// WriteAjtaiCommitment writes an Ajtai commitment to the random oracle.
func (o *RandomOracle) WriteAjtaiCommitment(com AjtaiCommitment) {
	for i := 0; i < len(com.Value); i++ {
		o.WritePoly(com.Value[i])
	}
}

// SampleMonomialAssign uniformly samples a monomial and writes it to monoOut.
func (o *RandomOracle) SampleMonomialAssign(monoOut ring.Poly) {
	monoOut.Zero()

	d := o.SampleN(uint64(2 * o.Parameters.ringQ.N()))

	for i := 0; i <= o.Parameters.ringQ.Level(); i++ {
		if d&1 == 0 {
			monoOut.Coeffs[i][d>>1] = 1
		} else {
			monoOut.Coeffs[i][d>>1] = o.Parameters.ringQ.SubRings[i].Modulus - 1
		}
	}

	o.Parameters.ringQ.NTT(monoOut, monoOut)
	o.Parameters.ringQ.MForm(monoOut, monoOut)
}
