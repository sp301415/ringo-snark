package jindo

import (
	"math"
	"math/big"

	"github.com/sp301415/ringo-snark/math/bignum"
	"github.com/sp301415/ringo-snark/math/crt"
	"github.com/sp301415/ringo-snark/math/num"
)

// EncodeParameters is the parameters of input modulus.
type EncodeParameters[E bignum.Uint[E]] struct {
	base uint64
	exp  int
}

// NewEncodeParameters creates a new [encodeParameters].
func NewEncodeParameters[E bignum.Uint[E]]() EncodeParameters[E] {
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

	return EncodeParameters[E]{
		base: baseBig.Uint64(),
		exp:  1 << logExp,
	}
}

// Base is the base for encoding.
func (p EncodeParameters[E]) Base() uint64 {
	return p.base
}

// Exp is the exponent for encoding.
func (p EncodeParameters[E]) Exp() int {
	return p.exp
}

const (
	// rlweRank is secure for stdDev = ~ b with q = maxLogQ.
	rlweRank = 1 << 12
	// maxMSISRank is the maximum mlwe rank possible.
	maxMSISRank = 1 << 12
	// maxLogQ is the maximum possible q.
	maxLogQ = 150
	// tailCut is the tail cut bound for Gaussian distribution.
	tailCut = 5
	// rejRate is the rate for rejection sampling
	rejRate = 1.2
	// chalWeight is the hamming weight of the challenge.
	chalWeight = 35
	// maxCutOff is the maximum possible cutoff.
	maxCutOff = 1 << (num.MaxModulusBits - 1)
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
type Parameters[E bignum.Uint[E]] struct {
	// batch is the number of polynomials to be committed.
	batch int
	// split is the number of sub-polynomials.
	split int

	// rank is the number of cofficients in the committing polynomial.
	rank int
	// rows are the number of rows in the matrix form of polynomial.
	rows int
	// cols are the number of columns in the matrix form of polynomial.
	cols int

	// ecd is the encoding parameters.
	ecd EncodeParameters[E]
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

	// op is the commitment operator.
	op *crt.Operator
	// opOut is the outer commitment operator.
	opOut *crt.Operator
	// opAmb is the ambient commitment operator.
	opAmb *crt.Operator

	// maskStdDev is the standard deviation for masking.
	maskStdDev float64

	// resTwoNm is the two-norm bound of the response.
	resTwoNm float64
	// outOpenTwoNm is the two-norm bound of the outer commitment.
	outOpenTwoNm float64

	// comSize is the size of outer commitment.
	comSize float64
	// pfSize is the estimated size for proofs.
	pfSize float64
}

// NewParameters creates a new [Parameters].
func NewParameters[E bignum.Uint[E]](targetN, batch int) Parameters[E] {
	switch {
	case targetN < 1:
		panic("NewParameters: targetN must be >= 1")
	case batch < 1:
		panic("NewParameters: batch must be >= 1")
	}

	params := Parameters[E]{}
	ecd := NewEncodeParameters[E]()

	rejSlack := 14 / math.Log(rejRate)

	b := float64(ecd.base)
	k := float64(ecd.exp)
	d := float64(max(k, 1024))
	l := d / k

	nu := rlweRank / d

	xOp := k * b
	cOp := float64(chalWeight)
	dOp := float64(chalWeight)

	maxSplit := int(math.Ceil(float64(targetN) / l))
	minSize := math.Inf(1)
	for ss := 1; ss <= maxSplit; ss <<= 1 {
		split := float64(ss)
		maxCols := int(math.Ceil(float64(targetN) / (split * l)))
		t := split * float64(batch)
		for nn := 1; nn <= maxCols; nn <<= 1 {
			n := float64(nn)
			m := math.Ceil(float64(targetN) / (split * n * l))

			ecdInf := b

			var inMSISRank, maskStdDev, batchInf, resTwo, inCutOffTwo, logQ float64
			for mu := 1; mu < maxMSISRank; mu++ {
				inMSISRank = float64(mu)

				numu := nu + inMSISRank
				batchInf = t * dOp * ecdInf

				ecdTwo := math.Sqrt(d*((m+1)+numu)*n) * batchInf
				maskStdDev = rejSlack * ecdTwo
				batchInf = tailCut * maskStdDev
				batchTwo := math.Sqrt(d*((m+1)+numu)) * math.Sqrt2 * maskStdDev

				if batchInf > math.Exp2(63) {
					continue
				}

				resTwo = n * cOp * batchTwo
				inCutOffTwo = min(resTwo, math.Sqrt(inMSISRank*d)*(1+t*dOp)*maxCutOff)

				extBeta := (2 * cOp) * (2 * (resTwo + inCutOffTwo))
				cExt := (2 * cOp) * (2 * cOp)
				dExt := 2 * dOp

				inMSISBeta := 2 * dExt * cExt * extBeta
				logQ = math.Ceil(math.Log2(inMSISBeta))
				if logQ > maxLogQ {
					continue
				}

				if findMSISRank(d, math.Exp2(logQ), inMSISBeta) == mu {
					break
				}
			}

			logInCutOffInf := math.Floor(math.Log2(inCutOffTwo / (math.Sqrt(inMSISRank*d) * (1 + t*dOp) * (n * cOp))))
			inCutOffInf := math.Exp2(logInCutOffInf)

			var outMSISRank, outBeta, outCutOffTwo, logQOut float64
			for muOut := 1; muOut < maxMSISRank; muOut++ {
				outMSISRank = float64(muOut)

				outBetaInf := (1 + t*dOp) * (math.Exp2(logQ) / inCutOffInf)
				outBeta = math.Sqrt(n*inMSISRank*d) * outBetaInf
				outCutOffTwo = min(outBeta, math.Sqrt(outMSISRank*d)*(1+t*dOp)*maxCutOff)

				dExt := 2 * dOp

				outExtBeta := (2 * dExt) * (2 * (outBeta + outCutOffTwo))
				logQOut = math.Ceil(math.Log2(outExtBeta))
				if logQOut > maxLogQ {
					continue
				}

				if findMSISRank(d, math.Exp2(logQOut), outExtBeta) == muOut {
					break
				}
			}

			logOutCutOffInf := math.Floor(math.Log2(outCutOffTwo / (math.Sqrt(outMSISRank*d) * (1 + t*dOp))))
			outCutOffInf := math.Exp2(logOutCutOffInf)

			comSize := t * outMSISRank * d * math.Log2(math.Exp2(logQOut)/outCutOffInf)

			var pfSize float64
			pfSize += outMSISRank * d * math.Log2(math.Exp2(logQOut)/outCutOffInf)            // Mask Commitment
			pfSize += n * d * math.Log2((m+1)*xOp*batchInf)                                   // Partial Evaluation
			pfSize += ((m + 1) + nu + inMSISRank) * d * math.Log2(n*cOp*batchInf)             // Response
			pfSize += n * inMSISRank * d * math.Log2((1+t*dOp)*(math.Exp2(logQ)/inCutOffInf)) // Inner Commitment
			pfSize += (l + (1+split*l)*float64(batch)) * (k * math.Log2(b))                   // Evaluation Point

			if comSize+pfSize < minSize {
				minSize = comSize + pfSize

				params.batch = batch
				params.split = int(split)

				params.rank = int(split) * int(n) * int(m) * int(l)
				params.rows = int(m)
				params.cols = int(n)

				params.ecd = ecd
				params.slots = int(l)

				params.inMSISRank = int(inMSISRank)
				params.outMSISRank = int(outMSISRank)
				params.mlweRank = int(nu)

				params.logInCutOff = uint64(math.Floor(math.Log2(inCutOffInf)))
				params.logOutCutOff = uint64(math.Floor(math.Log2(outCutOffInf)))

				qLimbs := int(math.Ceil(logQ / num.MaxModulusBits))
				q := crt.MustFindNearestNTTPrimes(int(d), logQ/float64(qLimbs), qLimbs)
				params.op = crt.NewOperator(int(d), q)

				qOutLimbs := int(math.Ceil(logQOut / num.MaxModulusBits))
				qOut := crt.MustFindNearestNTTPrimes(int(d), logQOut/float64(qOutLimbs), qOutLimbs)
				params.opOut = crt.NewOperator(int(d), qOut)

				qAmbFullBits := math.Log2(n) + math.Log2(m+1) + 2*math.Log2(k) + 2*math.Log2(b) + math.Log2(maskStdDev)
				qAmbFullBits = max(qAmbFullBits, 1+2*math.Log2(maskStdDev))
				qAmbBits := max(qAmbFullBits-logQ, 1+math.Log2(b))

				if qAmbBits <= 0 {
					params.opAmb = params.op
				} else {
					qAmbLimbs := int(math.Ceil(qAmbBits / num.MaxModulusBits))
					var qAmb []*num.Modulus
					for {
						qAmb = crt.MustFindNearestNTTPrimes(int(d), qAmbBits/float64(qAmbLimbs), qAmbLimbs)
						isEq := false
						for i := range qAmb {
							for j := range q {
								if qAmb[i].Value() == q[j].Value() {
									isEq = true
								}
							}
						}

						if !isEq {
							break
						}
						qAmbBits += 1
					}
					params.opAmb = crt.NewOperator(int(d), append(q, qAmb...))
				}

				params.maskStdDev = maskStdDev

				params.resTwoNm = resTwo + inCutOffTwo
				params.outOpenTwoNm = outBeta + outCutOffTwo

				params.comSize = comSize
				params.pfSize = pfSize
			}
		}
	}

	return params
}

// Batch is the number of polynomials to be committed.
func (p Parameters[E]) Batch() int {
	return p.batch
}

// Split is the number of sub-polynomials.
func (p Parameters[E]) Split() int {
	return p.split
}

// Rank is the number of cofficients in the committing polynomial.
func (p Parameters[E]) Rank() int {
	return p.rank
}

// Rows are the number of rows in the matrix form of polynomial.
func (p Parameters[E]) Rows() int {
	return p.rows
}

// Cols are the number of columns in the matrix form of polynomial.
func (p Parameters[E]) Cols() int {
	return p.cols
}

// EncodeParameters is the encoding parameters.
func (p Parameters[E]) EncodeParameters() EncodeParameters[E] {
	return p.ecd
}

// Base is the base for encoding.
func (p Parameters[E]) Base() uint64 {
	return p.ecd.base
}

// Exp is the exponent for encoding.
func (p Parameters[E]) Exp() int {
	return p.ecd.exp
}

// Slots is the number of slots.
func (p Parameters[E]) Slots() int {
	return p.slots
}

// InMSISRank is the rank of the inner MSIS commitment.
func (p Parameters[E]) InMSISRank() int {
	return p.inMSISRank
}

// OutMSISRank is the rank of the outer MSIS commitment.
func (p Parameters[E]) OutMSISRank() int {
	return p.outMSISRank
}

// MLWERank is the rank of the MLWE hiding term.
func (p Parameters[E]) MLWERank() int {
	return p.mlweRank
}

// LogInCutOff is the cutoff for the inner commitment.
func (p Parameters[E]) LogInCutOff() uint64 {
	return p.logInCutOff
}

// LogOutCutOff is the cutoff for the outer commitment.
func (p Parameters[E]) OutCutOff() uint64 {
	return p.logOutCutOff
}

// Operator is the commitment [crt.Operator].
func (p Parameters[E]) Operator() *crt.Operator {
	return p.op
}

// OutOperator is the outer commitment [crt.Operator].
func (p Parameters[E]) OutOperator() *crt.Operator {
	return p.opOut
}

// AmbOperator is the ambient commitment [crt.Operator].
func (p Parameters[E]) AmbOperator() *crt.Operator {
	return p.opAmb
}

// MaskStdDev is the standard deviation for masking.
func (p Parameters[E]) MaskStdDev() float64 {
	return p.maskStdDev
}

// ResTwoNm is the two-norm bound of the response.
func (p Parameters[E]) ResTwoNm() float64 {
	return p.resTwoNm
}

// OutOpenTwoNm is the two-norm bound of the outer commitment.
func (p Parameters[E]) OutOpenTwoNm() float64 {
	return p.outOpenTwoNm
}

// CommitmentSize is the size of outer commitment.
func (p Parameters[E]) CommitmentSize() float64 {
	return p.comSize
}

// ProofSize is the estimated size for proof.
func (p Parameters[E]) ProofSize() float64 {
	return p.pfSize
}

// Size is the estimated size for commitment and proof.
func (p Parameters[E]) Size() float64 {
	return p.comSize + p.pfSize
}
