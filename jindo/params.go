package jindo

import (
	"math"
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/tuneinsight/lattigo/v6/ring"
)

// encodeParameters is the parameters of input modulus.
type encodeParameters struct {
	base uint64
	exp  int
}

// newEncodeParameters creates a new [encodeParameters].
func newEncodeParameters[E bignum.Uint[E]]() encodeParameters {
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

	// logInCutOff is the cutoff for the inner commitment.
	logInCutOff uint64
	// logOutCutOff is the cutoff for the outer commitment.
	logOutCutOff uint64

	// inComDcmpLen is the length of the decomposed inner commitment.
	inComDcmpLen int

	// ringQ is the commitment ring.
	ringQ *ring.Ring
	// ringQOut is the outer commitment ring.
	ringQOut *ring.Ring

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
	// inComDcmpTwoNm is the two-norm bound of the decomposed inner commitment.
	inComDcmpTwoNm float64

	// comSize is the size of outer commitment.
	comSize float64
	// pfSize is the estimated size for proofs.
	pfSize float64
}

// NewParameters creates a new [Parameters].
func NewParameters[E bignum.Uint[E]](targetN, batch int) Parameters {
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
	d := float64(max(k, 1024))
	l := d / k

	nu := rlweRank / d

	maxCols := int(math.Ceil(float64(targetN) / l))
	minSize := math.Inf(1)
	for nn := 1; nn <= maxCols; nn <<= 1 {
		n := float64(nn)
		m := math.Ceil(float64(targetN) / (n * l))

		xOne := math.Sqrt(k) * b
		cOne := math.Sqrt(k) * min(b, math.Exp2(120/k)) / 2

		ecdStdDev := 2 / (b - 1) * (b + 1) * eta
		ecdBlindStdDev := 2 * xOne / (b - 1) * (b + 1) * eta
		maskStdDev := 2 * cOne / (b - 1) * (b + 1) * eta
		maskBlindStdDev := 2 * cOne * xOne / (b - 1) * (b + 1) * eta

		mlweStdDev := 2 * math.Sqrt2 * eta
		maskMLWEStdDev := 2 * cOne * math.Sqrt2 * eta

		fijInf := tailCut * (b + 1) * ecdStdDev
		f0jInf := tailCut * (b + 1) * math.Sqrt(m+1) * ecdBlindStdDev
		finInf := tailCut * (b + 1) * math.Sqrt(n+1) * maskStdDev
		f0nInf := tailCut * (b + 1) * math.Sqrt((m+1)*n+1) * maskBlindStdDev

		resEcdiInf := math.Sqrt(n)*cOne*fijInf + finInf
		resEcd0Inf := math.Sqrt(n)*cOne*f0jInf + f0nInf
		prInf := math.Sqrt(m)*xOne*fijInf + f0jInf
		if t > 1 {
			resEcdiInf *= math.Sqrt(t) * cOne
			resEcd0Inf *= math.Sqrt(t) * cOne
			prInf *= math.Sqrt(t) * cOne
		}

		resEcdTwo := math.Sqrt(d * (m*resEcdiInf*resEcdiInf + resEcd0Inf*resEcd0Inf))

		mlweInf := tailCut * mlweStdDev
		maskMLWEInf := tailCut * math.Sqrt(n+1) * maskMLWEStdDev
		resMLWEInf := math.Sqrt(n)*cOne*mlweInf + maskMLWEInf
		if t > 1 {
			resMLWEInf *= math.Sqrt(t) * cOne
		}

		var q, inMSISRank, inCutOffTwo float64
		var resTwo, dExtOne float64
		for mu := 1; ; mu++ {
			resMLWETwo := math.Sqrt(d*(float64(mu)+nu)) * resMLWEInf
			resTwo = math.Sqrt(resEcdTwo*resEcdTwo + resMLWETwo*resMLWETwo)
			inCutOffTwo = resTwo

			var extBeta, cExtOne float64
			if t == 1 {
				extBeta = 2 * (resTwo + inCutOffTwo)
				cExtOne = 2 * cOne
				dExtOne = 1
			} else {
				extBeta = 2 * (2 * cOne) * (resTwo + inCutOffTwo)
				cExtOne = (2 * cOne) * (2 * cOne)
				dExtOne = 2 * cOne
			}

			inMSISBeta := 2 * dExtOne * cExtOne * extBeta
			logQ := math.Ceil(math.Log2(inMSISBeta))
			qLimbs := int(math.Ceil(logQ / 60.0))
			qBits := int(math.Ceil(logQ / float64(qLimbs)))
			q = math.Exp2(float64(qBits * qLimbs))

			if math.Log2(q) > maxLogQ {
				continue
			}

			if findMSISRank(d, q, inMSISBeta) == mu {
				inMSISRank = float64(mu)
				break
			}
		}

		inCutOffInf := inCutOffTwo / ((1 + math.Sqrt(n)*cOne) * math.Sqrt(inMSISRank*d))
		if t > 1 {
			inCutOffInf /= math.Sqrt(t) * cOne
		}

		inDcmpInf := q / inCutOffInf
		if t > 1 {
			inDcmpInf *= math.Sqrt(t) * cOne
		}

		inDcmpTwo := math.Sqrt((n+1)*inMSISRank*d) * inDcmpInf
		outCutOffTwo := inDcmpTwo

		outMSISBeta := 2 * dExtOne * (2 * (inDcmpTwo + outCutOffTwo))

		logQQ := math.Ceil(math.Log2(outMSISBeta))
		qqLimbs := int(math.Ceil(logQQ / 60.0))
		qqBits := int(math.Ceil(logQQ / float64(qqLimbs)))
		qq := math.Exp2(float64(qqBits * qqLimbs))
		if math.Log2(qq) > maxLogQ {
			continue
		}
		outMSISRank := float64(findMSISRank(d, qq, outMSISBeta))

		outCutOffInf := outCutOffTwo / (math.Sqrt(outMSISRank * d))
		if t > 1 {
			outCutOffInf /= math.Sqrt(t) * cOne
		}

		comSize := t * outMSISRank * d * math.Log2(qq/outCutOffInf)

		var pfSize float64
		pfSize += n * d * math.Log2(prInf)                          // Partial
		pfSize += d * math.Log2(q)                                  // Partial * Mask
		pfSize += m * d * math.Log2(resEcdiInf)                     // Response 1 ~ m
		pfSize += d * math.Log2(resEcd0Inf)                         // Response 0
		pfSize += (inMSISRank + nu) * d * math.Log2(resMLWEInf)     // Response MLWE
		pfSize += ((n + 1) * inMSISRank * d) * math.Log2(inDcmpInf) // Inner Commitments

		if comSize+pfSize < minSize {
			minSize = comSize + pfSize

			params.batch = batch

			params.rank = int(n) * int(m) * int(l)
			params.rows = int(m) + 1
			params.cols = int(n)

			params.ecd = ecd
			params.slots = int(d) / ecd.exp

			params.inMSISRank = int(inMSISRank)
			params.outMSISRank = int(outMSISRank)
			params.mlweRank = int(nu)

			params.logInCutOff = uint64(math.Floor(math.Log2(inCutOffInf)))
			params.logOutCutOff = uint64(math.Floor(math.Log2(outCutOffInf)))

			params.inComDcmpLen = int((n + 1) * inMSISRank)

			qLimbs := int(math.Ceil(math.Log2(q) / 60))
			qBits := int(math.Ceil(math.Log2(q) / float64(qLimbs)))
			qGen := ring.NewNTTFriendlyPrimesGenerator(uint64(qBits), 2*uint64(d))
			q, err := qGen.NextUpstreamPrimes(qLimbs)
			if err != nil {
				continue
			}
			params.ringQ, err = ring.NewRing(int(d), q)
			if err != nil {
				panic(err)
			}

			qqLimbs := int(math.Ceil(math.Log2(qq) / 60))
			qqBits := int(math.Ceil(math.Log2(qq) / float64(qqLimbs)))
			qqGen := ring.NewNTTFriendlyPrimesGenerator(uint64(qqBits), 2*uint64(d))
			qq, err := qqGen.NextUpstreamPrimes(qqLimbs)
			if err != nil {
				continue
			}
			params.ringQOut, err = ring.NewRing(int(d), qq)
			if err != nil {
				panic(err)
			}

			params.ecdStdDev = ecdStdDev / math.Sqrt(2*math.Pi)
			params.ecdBlindStdDev = ecdBlindStdDev / math.Sqrt(2*math.Pi)
			params.maskStdDev = maskStdDev / math.Sqrt(2*math.Pi)
			params.maskBlindStdDev = maskBlindStdDev / math.Sqrt(2*math.Pi)

			params.mlweStdDev = mlweStdDev / math.Sqrt(2*math.Pi)
			params.maskMLWEStdDev = maskMLWEStdDev / math.Sqrt(2*math.Pi)

			params.resTwoNm = resTwo + inCutOffTwo
			params.inComDcmpTwoNm = inDcmpTwo + outCutOffTwo

			params.comSize = comSize
			params.pfSize = pfSize
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
	return min(p.ecd.base, 1<<(120/p.ecd.exp)) / 2
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

// LogInCutOff is the cutoff for the inner commitment.
func (p Parameters) LogInCutOff() uint64 {
	return p.logInCutOff
}

// LogOutCutOff is the cutoff for the outer commitment.
func (p Parameters) OutCutOff() uint64 {
	return p.logOutCutOff
}

// InCommitDecomposeLen is the length of the decomposed inner commitment.
func (p Parameters) InCommitDecomposeLen() int {
	return p.inComDcmpLen
}

// RingQ is the commitment ring.
func (p Parameters) RingQ() *ring.Ring {
	return p.ringQ
}

// RingQOut is the outer commitment ring.
func (p Parameters) RingQOut() *ring.Ring {
	return p.ringQOut
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

// Size is the estimated size for commitment and proof.
func (p Parameters) Size() float64 {
	return p.comSize + p.pfSize
}
