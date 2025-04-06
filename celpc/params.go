package celpc

import (
	"math"
	"math/big"

	"github.com/tuneinsight/lattigo/v6/core/rlwe"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// ParametersLiteral is a structure for CELPC parameters.
type ParametersLiteral struct {
	// AjtaiSize is the size of the Ajtai Commitment.
	// Denoted as mu in the paper.
	AjtaiSize int
	// AjtaiRandSize is the size of the randomness used in Ajtai Commitment.
	// Denoted as mu + nu in the paper.
	AjtaiRandSize int

	// Degree is the degree of the committing polynomial.
	// Denoted as N in the paper.
	// Note that we can commit to a larger degree polynomial, and this value is just a recommendation.
	// This is usful for batch commitments.
	Degree int
	// BigIntCommitSize is the input length of the bigint vector for Ajtai Commitment.
	// Denoted as n in the paper.
	BigIntCommitSize int

	// ModulusBase is the base of the modulus of the committing polynomial.
	// Denoted as b in the paper.
	ModulusBase int
	// Digits is the exponent of the modulus of the committing polynomial.
	// Denoted as r in the paper.
	Digits int

	// RingDegree is the degree of the internal ring R_q.
	// Denoted as d in the paper.
	RingDegree int
	// LogRingModulus is the (log2 value of) modulus of the internal ring R_q.
	// Denoted as q in the paper.
	LogRingModulus []int

	// CommitStdDev is the standard deviation of randomized encoding used in Ajtai Commitment.
	// Denoted as s1 in the paper.
	CommitStdDev float64
	// OpeningProofStdDev is the standard deviation used in opening proof of Ajtai Commitment.
	// Denoted as s2 in the paper.
	OpeningProofStdDev float64
	// BlindStdDev is the standard deviation of blinding polynomial used in evaluation.
	// Denoted as s3 in the paper.
	BlindStdDev float64

	// CommitRandStdDev is the standard deviation of error polynomial used in Ajtai Commitment.
	// Denoted as sigma1 in the paper.
	CommitRandStdDev float64
	// OpeningProofRandStdDev is the standard deviation used in opening proof of Ajtai Commitment.
	// Denoted as sigma2 in the paper.
	OpeningProofRandStdDev float64
	// BlindRandStdDev is the standard deviation of blinding error polynomial used in evaluation.
	// Denoted as sigma3 in the paper.
	BlindRandStdDev float64

	// OpenProofBound is the bound of opening verification.
	OpenProofBound float64
	// EvalProofBound is the bound of evaluation verification.
	EvalProofBound float64
}

// Compile transforms ParametersLiteral to read-only Parameters.
// If there is any invalid parameter in the literal, it panics.
// Default parameters are guaranteed to be compiled without panics.
func (p ParametersLiteral) Compile() Parameters {
	switch {
	case p.Degree%p.BigIntCommitSize != 0:
		panic("Degree must divide BigIntCommitSize")
	}

	logRingDegree := int(math.Log2(float64(p.RingDegree)))
	q, _, err := rlwe.GenModuli(logRingDegree+1, p.LogRingModulus, nil)
	if err != nil {
		panic(err)
	}

	ringQ, err := ring.NewRing(p.RingDegree, q)
	if err != nil {
		panic(err)
	}

	rnsGadget := make([]*big.Int, ringQ.ModuliChainLength())
	qFull := ringQ.Modulus()
	for i := 0; i <= ringQ.Level(); i++ {
		qi := big.NewInt(0).SetUint64(ringQ.SubRings[i].Modulus)
		qDiv := big.NewInt(0).Div(qFull, qi)
		qInv := big.NewInt(0).ModInverse(qDiv, qi)
		rnsGadget[i] = big.NewInt(0).Mul(qDiv, qInv)
	}

	prime := big.NewInt(0).Exp(big.NewInt(int64(p.ModulusBase)), big.NewInt(int64(p.Digits)), nil)
	prime.Add(prime, big.NewInt(1))
	if !prime.ProbablyPrime(0) {
		panic("Modulus is not a prime")
	}

	return Parameters{
		ajtaiSize:     p.AjtaiSize,
		ajtaiRandSize: p.AjtaiRandSize,

		degree:           p.Degree,
		bigIntCommitSize: p.BigIntCommitSize,
		polyCommitSize:   p.BigIntCommitSize * p.Digits / p.RingDegree,

		modulusBase: p.ModulusBase,
		digits:      p.Digits,
		modulus:     prime,
		slots:       p.RingDegree / p.Digits,

		ringQ:     ringQ,
		rnsGadget: rnsGadget,

		commitStdDev:       p.CommitStdDev,
		openingProofStdDev: p.OpeningProofStdDev,
		blindStdDev:        p.BlindStdDev,

		commitRandStdDev:       p.CommitRandStdDev,
		openingProofRandStdDev: p.OpeningProofRandStdDev,
		blindRandStdDev:        p.BlindRandStdDev,

		openProofBound: p.OpenProofBound,
		evalProofBound: p.EvalProofBound,
	}
}

// Parameters is a read-only structure for CELPC parameters.
type Parameters struct {
	// ajtaiSize is the size of the Ajtai Commitment.
	// Denoted as mu in the paper.
	ajtaiSize int
	// ajtaiRandSize is the size of the randomness used in Ajtai Commitment.
	// Denoted as mu + nu in the paper.
	ajtaiRandSize int
	// ajtaiCommitSize

	// degree is the degree of the committing polynomial.
	// Denoted as N in the paper.
	// Note that we can commit to a larger degree polynomial, and this value is just a recommendation.
	// This is usful for batch commitments.
	degree int
	// bigIntCommitLength is the input length of the bigint vector for Ajtai Commitment.
	// Denoted as n in the paper.
	bigIntCommitSize int
	// polyVecCommitLength is the input length of the polynomial vector for Ajtai Commitment.
	// Denoted as l in the paper.
	// Equals to n / s = n * r / d.
	polyCommitSize int

	// modulusBase is the base of the modulus of the committing polynomial.
	// Denoted as b in the paper.
	modulusBase int
	// digits is the exponent of the modulus of the committing polynomial.
	// Denoted as r in the paper.
	digits int
	// modulus is the modulus of the committing polynomial.
	// Denoted as p in the paper.
	// Equals to b^r + 1.
	modulus *big.Int
	// slots is the number of "slots" used in high-precision encoding.
	// Denoted as s in the paper.
	slots int

	// ringQ is the internal ring R_q.
	ringQ *ring.Ring
	// rnsGadget is a gadget vector used for reconstructing the polynomial to bigint.
	rnsGadget []*big.Int

	// commitStdDev is the standard deviation of randomized encoding used in Ajtai Commitment.
	// Denoted as s1 in the paper.
	commitStdDev float64
	// openingProofStdDev is the standard deviation used in opening proof of Ajtai Commitment.
	// Denoted as s2 in the paper.
	openingProofStdDev float64
	// blindStdDev is the standard deviation of blinding polynomial used in evaluation.
	// Denoted as s3 in the paper.
	blindStdDev float64

	// commitRandStdDev is the standard deviation of error polynomial used in Ajtai Commitment.
	// Denoted as sigma1 in the paper.
	commitRandStdDev float64
	// openingProofRandStdDev is the standard deviation used in opening proof of Ajtai Commitment.
	// Denoted as sigma2 in the paper.
	openingProofRandStdDev float64
	// blindRandStdDev is the standard deviation of blinding error polynomial used in evaluation.
	// Denoted as sigma3 in the paper.
	blindRandStdDev float64

	// openProofBound is the bound of opening verification.
	openProofBound float64
	// evalProofBound is the bound of evaluation verification.
	evalProofBound float64
}

// AjtaiSize returns the size of the Ajtai Commitment.
func (p Parameters) AjtaiSize() int {
	return p.ajtaiSize
}

// AjtaiRandSize returns the size of the randomness used in Ajtai Commitment.
func (p Parameters) AjtaiRandSize() int {
	return p.ajtaiRandSize
}

// Degree returns the degree of the committing polynomial.
func (p Parameters) Degree() int {
	return p.degree
}

// BigIntCommitSize returns the input length of the bigint vector for Ajtai Commitment.
func (p Parameters) BigIntCommitSize() int {
	return p.bigIntCommitSize
}

// PolyCommitSize returns the input length of the polynomial vector for Ajtai Commitment.
func (p Parameters) PolyCommitSize() int {
	return p.polyCommitSize
}

// ModulusBase returns the base of the modulus of the committing polynomial.
func (p Parameters) ModulusBase() int {
	return p.modulusBase
}

// Digits returns the exponent of the modulus of the committing polynomial.
func (p Parameters) Digits() int {
	return p.digits
}

// Modulus returns the modulus of the committing polynomial.
func (p Parameters) Modulus() *big.Int {
	return p.modulus
}

// Slots returns the number of "slots" used in high-precision encoding.
func (p Parameters) Slots() int {
	return p.slots
}

// RingQ returns the internal ring R_q.
func (p Parameters) RingQ() *ring.Ring {
	return p.ringQ
}

// RNSGadget returns a gadget vector used for reconstructing the polynomial to bigint.
func (p Parameters) RNSGadget() []*big.Int {
	return p.rnsGadget
}

// Repetition returns the repetition count for Proof Of Knowledge protocol.
func (p Parameters) Repetition() int {
	return int(math.Ceil(128 / (1 + float64(p.ringQ.LogN()))))
}

// CommitStdDev returns the standard deviation of randomized encoding used in Ajtai Commitment.
func (p Parameters) CommitStdDev() float64 {
	return p.commitStdDev
}

// OpeningProofStdDev returns the standard deviation used in opening proof of Ajtai Commitment.
func (p Parameters) OpeningProofStdDev() float64 {
	return p.openingProofStdDev
}

// BlindStdDev returns the standard deviation of blinding polynomial used in evaluation.
func (p Parameters) BlindStdDev() float64 {
	return p.blindStdDev
}

// CommitRandStdDev returns the standard deviation of error polynomial used in Ajtai Commitment.
func (p Parameters) CommitRandStdDev() float64 {
	return p.commitRandStdDev
}

// OpeningProofRandStdDev returns the standard deviation used in opening proof of Ajtai Commitment.
func (p Parameters) OpeningProofRandStdDev() float64 {
	return p.openingProofRandStdDev
}

// BlindRandStdDev returns the standard deviation of blinding error polynomial used in evaluation.
func (p Parameters) BlindRandStdDev() float64 {
	return p.blindRandStdDev
}

// OpenProofBound returns the bound of opening verification.
func (p Parameters) OpenProofBound() float64 {
	return p.openProofBound
}

// EvalProofBound returns the bound of evaluation verification.
func (p Parameters) EvalProofBound() float64 {
	return p.evalProofBound
}
