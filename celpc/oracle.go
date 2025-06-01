package celpc

import (
	"io"
	"math/big"

	"github.com/sp301415/ringo-snark/bigring"
	"github.com/sp301415/ringo-snark/csprng"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// RandomOracle is a random oracle.
type RandomOracle struct {
	Parameters Parameters

	*csprng.UniformSampler

	modBuf  []byte
	msbMask byte
}

// NewRandomOracle creates a new RandomOracle.
func NewRandomOracle(params Parameters) *RandomOracle {
	k := (params.modulus.BitLen() + 7) / 8
	b := uint(params.modulus.BitLen() % 8)
	if b == 0 {
		b = 8
	}

	modBuf := make([]byte, k)
	msbMask := byte((1 << b) - 1)

	return &RandomOracle{
		Parameters: params,

		UniformSampler: csprng.NewUniformSampler(),

		modBuf:  modBuf,
		msbMask: msbMask,
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

// SampleMod samples a uniformly random value modulo modulus.
func (s *RandomOracle) SampleMod() *big.Int {
	r := big.NewInt(0)
	s.SampleModAssign(r)
	return r
}

// SampleModAssign samples a uniformly random value modulo modulus.
func (s *RandomOracle) SampleModAssign(xOut *big.Int) {
	for {
		_, err := io.ReadFull(s, s.modBuf)
		if err != nil {
			panic(err)
		}

		s.modBuf[0] &= s.msbMask

		xOut.SetBytes(s.modBuf)
		if xOut.Cmp(s.Parameters.modulus) < 0 {
			return
		}
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
