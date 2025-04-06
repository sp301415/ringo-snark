package celpc

import (
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
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

// WriteBigPoly writes a big polynomial to the random oracle.
func (o *RandomOracle) WriteBigPoly(p bigring.BigPoly) {
	for i := 0; i < len(p.Coeffs); i++ {
		o.WriteBigInt(p.Coeffs[i])
	}
}

// WriteBigNTTPoly writes a big NTT polynomial to the random oracle.
func (o *RandomOracle) WriteBigNTTPoly(p bigring.BigNTTPoly) {
	for i := 0; i < len(p.Coeffs); i++ {
		o.WriteBigInt(p.Coeffs[i])
	}
}

// WriteCommitment writes a commitment to the random oracle.
func (o *RandomOracle) WriteCommitment(com Commitment) {
	for i := 0; i < len(com.Value); i++ {
		o.WriteAjtaiCommitment(com.Value[i])
	}
}

// WriteOpeningProof writes an opening proof to the random oracle.
func (o *RandomOracle) WriteOpeningProof(op OpeningProof) {
	for i := 0; i < len(op.Commitment); i++ {
		o.WriteAjtaiCommitment(op.Commitment[i])
	}
	for i := 0; i < len(op.ResponseMask); i++ {
		for j := 0; j < len(op.ResponseMask[i]); j++ {
			o.WritePoly(op.ResponseMask[i][j])
		}
	}
	for i := 0; i < len(op.ResponseRand); i++ {
		for j := 0; j < len(op.ResponseRand[i]); j++ {
			o.WritePoly(op.ResponseRand[i][j])
		}
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
