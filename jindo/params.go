package jindo

import (
	"math"
	"math/big"

	"github.com/sp301415/ringo-snark/math/num"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// encodeParameters is the parameters of input modulus.
type encodeParameters struct {
	base uint64
	exp  int
}

// newEncodeParameters creates a new [encodeParameters].
func newEncodeParameters[E num.Uint[E]]() encodeParameters {
	var z E

	logExp := 0
	baseBig := z.New().SetBigInt(big.NewInt(-1)).BigInt(new(big.Int))
	for ; ; logExp++ {
		sqrtBig := new(big.Int).Sqrt(baseBig)
		testBig := new(big.Int).Mul(sqrtBig, sqrtBig)
		if testBig.Cmp(baseBig) != 0 {
			break
		}
		baseBig.Set(sqrtBig)
	}

	if !baseBig.IsUint64() {
		panic("newEncodeParameters: modulus not jindo-friendly")
	}

	return encodeParameters{
		base: baseBig.Uint64(),
		exp:  1 << logExp,
	}
}

const (
	// rlweRank is secure for stdDev = 2sqrt(2)eta.
	rlweRank = 1 << 13
	// maxLogQ is secure for stdDev = 2sqrt(2)eta.
	maxLogQ = 240
	// eta is the smoothing parameter.
	eta = 6
	// tailCut is the tail cut bound for Gaussian distribution.
	tailCut = 5
)

func findMSISRank(d, q, beta float64) int {
	if beta > q {
		panic("findMSISRank: beta > q")
	}
	logBeta := math.Log2(beta)
	logQ := math.Log2(q)
	logDelta := math.Log2(1.005)
	return int(math.Ceil((logBeta * logBeta) / (4 * d * logQ * logDelta)))
}

// Parameters is the parameters for the Jindo polynomial commitment scheme.
type Parameters struct {
	// batch is the number of polynomials to be committed.
	batch int

	// rank is the number of cofficients in the committing polynomial.
	rank int
	// rows are the number of rows in the matrix form of polynomial.
	rows int
	// cols are the number of columns in the matrix form of polynomial.
	cols int

	// ecd is the encoding parameters.
	ecd encodeParameters
	// slots is the number of slots.
	slots int

	// inMSISRank is the rank of the inner MSIS commitment.
	inMSISRank int
	// outMSISRank is the rank of the outer MSIS commitment.
	outMSISRank int
	// mlweRank is the rank of the MLWE hiding term.
	mlweRank int

	// inComDcmpLen is the length of the decomposed inner commitment.
	inComDcmpLen int

	// ringQ is the commitment ring.
	ringQ *ring.Ring

	// ecdStdDev is the standard deviation for encoding.
	ecdStdDev float64
	// ecdBlindStdDev is the standard deviation for encoding blinding terms.
	ecdBlindStdDev float64
	// maskStdDev is the standard deviation for masking.
	maskStdDev float64
	// maskBlindStdDev is the standard deviation for masking blinding terms.
	maskBlindStdDev float64

	// mlweStdDev is the standard deviation for MLWE.
	mlweStdDev float64
	// maskMLWEStdDev is the standard deviation for MLWE masking.
	maskMLWEStdDev float64

	// resTwoNm is the two-norm bound of the response.
	resTwoNm float64
	// prTwoNm is the two-norm bound of the partial evaluation.
	prTwoNm float64
	// inComDcmpTwoNm is the two-norm bound of the decomposed inner commitment.
	inComDcmpTwoNm float64

	// comSize is the size of outer commitment.
	comSize float64
	// pfSize is the estimated size for proofs.
	pfSize float64
}

// NewParameters creates a new [Parameters].
func NewParameters[E num.Uint[E]](targetN, batch int) Parameters {
	switch {
	case targetN < 1:
		panic("NewParameters: targetN must be >= 1")
	case batch < 1:
		panic("NewParameters: batch must be >= 1")
	}

	params := Parameters{}
	ecd := newEncodeParameters[E]()

	t := float64(batch)
	b := float64(ecd.base)
	k := float64(ecd.exp)
	d := float64(max(k, 256))
	l := d / k

	nu := rlweRank / d

	maxCols := int(math.Ceil(float64(targetN) / l))
	minSize := math.Inf(1)
	for nn := 1; nn <= maxCols; nn <<= 1 {
		n := float64(nn)
		m := math.Ceil(float64(targetN) / (n * l))

		xOne := k * b
		cOne := k * min(b, math.Exp2(128/k))

		ecdStdDev := 2 / (b - 1) * (b + 1) * eta
		ecdBlindStdDev := 2 * xOne / (b - 1) * (b + 1) * eta
		maskStdDev := 2 * cOne / (b - 1) * (b + 1) * eta
		maskBlindStdDev := 2 * cOne * xOne / (b - 1) * (b + 1) * eta

		mlweStdDev := 2 * math.Sqrt2 * eta
		maskMLWEStdDev := 2 * cOne * math.Sqrt2 * eta

		cijTwo := (b + 1) * ecdStdDev * math.Sqrt(d)
		c0jTwo := (b + 1) * math.Sqrt(m+1) * ecdBlindStdDev * math.Sqrt(d)
		cinTwo := (b + 1) * math.Sqrt(n+1) * maskStdDev * math.Sqrt(d)
		c0nTwo := (b + 1) * math.Sqrt((m+1)*n+1) * maskBlindStdDev * math.Sqrt(d)

		cjTwo := math.Sqrt((m-1)*cijTwo*cijTwo + c0jTwo*c0jTwo)
		cnTwo := math.Sqrt((m-1)*cinTwo*cinTwo + c0nTwo*c0nTwo)

		resEcdTwo := n*cOne*cjTwo + cnTwo
		prTwo := math.Sqrt(n) * (m*xOne*cijTwo + c0jTwo)
		if batch > 1 {
			resEcdTwo *= t * cOne
			prTwo *= t * cOne
		}

		cijInf := (b + 1) * ecdStdDev
		c0jInf := (b + 1) * math.Sqrt(m+1) * ecdBlindStdDev
		cinInf := (b + 1) * math.Sqrt(n+1) * maskStdDev
		c0nInf := (b + 1) * math.Sqrt((m+1)*n+1) * maskBlindStdDev

		resEcdiInf := n*cOne*cijInf + cinInf
		resEcd0Inf := n*cOne*c0jInf + c0nInf
		prInf := m*xOne*cijInf + c0jInf
		if batch > 1 {
			resEcdiInf *= t * cOne
			resEcd0Inf *= t * cOne
			prInf *= t * cOne
		}

		var qBits, qLimbs int
		var q, mu, kap float64
		var inDcmpTwo, resExtTwo, resMLWETwo, cExtTwo, dExtTwo float64
		for logQ := 1; logQ <= maxLogQ; logQ++ {
			q = math.Exp2(float64(logQ))

			if batch == 1 {
				resExtTwo = 2 * resEcdTwo
				cExtTwo = 2 * cOne
				dExtTwo = 1.0
			} else {
				resExtTwo = 2 * (2 * cOne) * (2 * resEcdTwo)
				cExtTwo = (2 * cOne) * (2 * cOne)
				dExtTwo = 2 * cOne
			}

			inMSISBeta := 2 * dExtTwo * cExtTwo * resExtTwo
			if inMSISBeta > q {
				continue
			}
			mu = float64(findMSISRank(d, q, inMSISBeta))

			mlweTwo := mlweStdDev * math.Sqrt((nu+mu)*d)
			mlweMaskTwo := maskMLWEStdDev * math.Sqrt((n+1)*(nu+mu)*d)

			resMLWETwo = n*cOne*mlweTwo + mlweMaskTwo
			if batch > 1 {
				resMLWETwo *= t * cOne
			}

			qLimbs = int(math.Ceil(math.Log2(q) / 60))
			qBits = int(math.Ceil(math.Log2(q) / float64(qLimbs)))

			inDcmpTwo = math.Sqrt(mu*n*d*float64(qLimbs)) * math.Exp2(float64(qBits))
			if batch > 1 {
				inDcmpTwo *= t * cOne
			}

			outMSISBeta := 2 * dExtTwo * (2 * inDcmpTwo)
			if outMSISBeta > q {
				continue
			}
			kap = float64(findMSISRank(d, q, outMSISBeta))

			break
		}

		mlweInf := mlweStdDev
		mlweMaskInf := maskMLWEStdDev * math.Sqrt(n+1)

		resMLWEInf := n*cOne*mlweInf + mlweMaskInf
		if batch > 1 {
			resMLWEInf *= t * cOne
		}

		outInf := math.Exp2(float64(qBits))
		if batch > 1 {
			outInf *= t * cOne
		}

		outComSize := kap * d * math.Log2(q)
		inComSize := mu * d * math.Log2(q)

		var size float64
		size += t * outComSize                                     // Outer Commitments
		size += inComSize                                          // Mask
		size += d * math.Log2(q)                                   // Partial * Mask
		size += math.Log2(tailCut*prInf) * (n * d)                 // Partial
		size += math.Log2(tailCut*resEcdiInf) * (m * d)            // Response 1 ~ m + 1
		size += math.Log2(tailCut*resEcd0Inf) * (d)                // Response 0
		size += math.Log2(tailCut*resMLWEInf) * ((mu + nu) * d)    // Response MLWE
		size += (n * mu * d * float64(qLimbs)) * math.Log2(outInf) // Inner Commitments

		if size < minSize {
			minSize = size

			params.batch = batch

			params.rank = int(n) * int(m) * int(l)
			params.rows = int(m) + 1
			params.cols = int(n)

			params.ecd = ecd
			params.slots = int(d) / ecd.exp

			params.inMSISRank = int(mu)
			params.outMSISRank = int(kap)
			params.mlweRank = int(nu)

			params.inComDcmpLen = int(n * mu * float64(qLimbs))

			nttGen := ring.NewNTTFriendlyPrimesGenerator(uint64(qBits), 2*uint64(d))
			q, err := nttGen.NextUpstreamPrimes(qLimbs)
			if err != nil {
				continue
			}
			params.ringQ, err = ring.NewRing(int(d), q)
			if err != nil {
				panic(err)
			}

			params.ecdStdDev = ecdStdDev / math.Sqrt(2*math.Pi)
			params.ecdBlindStdDev = ecdBlindStdDev / math.Sqrt(2*math.Pi)
			params.maskStdDev = maskStdDev / math.Sqrt(2*math.Pi)
			params.maskBlindStdDev = maskBlindStdDev / math.Sqrt(2*math.Pi)

			params.mlweStdDev = mlweStdDev / math.Sqrt(2*math.Pi)
			params.maskMLWEStdDev = maskMLWEStdDev / math.Sqrt(2*math.Pi)

			params.resTwoNm = math.Sqrt(resEcdTwo*resEcdTwo + resMLWETwo*resMLWETwo)
			params.prTwoNm = prTwo
			params.inComDcmpTwoNm = inDcmpTwo

			params.comSize = t * outComSize
			params.pfSize = size - params.comSize
		}
	}

	return params
}

// Batch is the number of polynomials to be committed.
func (p Parameters) Batch() int {
	return p.batch
}

// Rank is the number of cofficients in the committing polynomial.
func (p Parameters) Rank() int {
	return p.rank
}

// Rows are the number of rows in the matrix form of polynomial.
func (p Parameters) Rows() int {
	return p.rows
}

// Cols are the number of columns in the matrix form of polynomial.
func (p Parameters) Cols() int {
	return p.cols
}

// Base is the base for encoding.
func (p Parameters) Base() uint64 {
	return p.ecd.base
}

// Exp is the exponent for encoding.
func (p Parameters) Exp() int {
	return p.ecd.exp
}

// Slots is the number of slots.
func (p Parameters) Slots() int {
	return p.slots
}

// ChallengeBound is the challenge bound.
func (p Parameters) ChallengeBound() uint64 {
	return min(p.ecd.base, 1<<(128/p.ecd.exp))
}

// InMSISRank is the rank of the inner MSIS commitment.
func (p Parameters) InMSISRank() int {
	return p.inMSISRank
}

// OutMSISRank is the rank of the outer MSIS commitment.
func (p Parameters) OutMSISRank() int {
	return p.outMSISRank
}

// MLWERank is the rank of the MLWE hiding term.
func (p Parameters) MLWERank() int {
	return p.mlweRank
}

// InCommitDecomposeLen is the length of the decomposed inner commitment.
func (p Parameters) InCommitDecomposeLen() int {
	return p.inComDcmpLen
}

// RingQ is the commitment ring.
func (p Parameters) RingQ() *ring.Ring {
	return p.ringQ
}

// EcdStdDev is the standard deviation for encoding.
func (p Parameters) EcdStdDev() float64 {
	return p.ecdStdDev
}

// EcdBlindStdDev is the standard deviation for encoding blinding terms.
func (p Parameters) EcdBlindStdDev() float64 {
	return p.ecdBlindStdDev
}

// MaskStdDev is the standard deviation for masking.
func (p Parameters) MaskStdDev() float64 {
	return p.maskStdDev
}

// MaskBlindStdDev is the standard deviation for masking blinding terms.
func (p Parameters) MaskBlindStdDev() float64 {
	return p.maskBlindStdDev
}

// MLWEStdDev is the standard deviation for MLWE.
func (p Parameters) MLWEStdDev() float64 {
	return p.mlweStdDev
}

// MaskMLWEStdDev is the standard deviation for MLWE masking.
func (p Parameters) MaskMLWEStdDev() float64 {
	return p.maskMLWEStdDev
}

// ResTwoNm is the two-norm bound of the response.
func (p Parameters) ResTwoNm() float64 {
	return p.resTwoNm
}

// PrTwoNm is the two-norm bound of the partial evaluation.
func (p Parameters) PrTwoNm() float64 {
	return p.prTwoNm
}

// InComDcmpTwoNm is the two-norm bound of the decomposed inner commitment.
func (p Parameters) InComDcmpTwoNm() float64 {
	return p.inComDcmpTwoNm
}

// CommitmentSize is the size of outer commitment.
func (p Parameters) CommitmentSize() float64 {
	return p.comSize
}

// ProofSize is the estimated size for proof.
func (p Parameters) ProofSize() float64 {
	return p.pfSize
}
