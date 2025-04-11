package celpc

import "math"

var (
	// ParametersLogN19LogP256 is a parameters set for commiting 2^19 degree polynomial over 256-bit prime field.
	ParamsLogN19LogP256 = ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 2,

		Degree:           1 << 19,
		BigIntCommitSize: 1 << 12,

		ModulusBase: 63388,
		Digits:      16,

		RingDegree:     1 << 11,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10.0,
		OpeningProofStdDev: 34.0,
		BlindStdDev:        5202283.0,

		CommitRandStdDev:       20.0,
		OpeningProofRandStdDev: 68.0,
		BlindRandStdDev:        10404567.0,

		OpenProofBound: math.Exp2(35.7),
		EvalProofBound: math.Exp2(54.6),
	}

	// ParametersLogN21LogP256 is a parameters set for commiting 2^21 degree polynomial over 256-bit prime field.
	ParamsLogN21LogP256 = ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 2,

		Degree:           1 << 21,
		BigIntCommitSize: 1 << 13,

		ModulusBase: 63388,
		Digits:      16,

		RingDegree:     1 << 11,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10.0,
		OpeningProofStdDev: 34.0,
		BlindStdDev:        5202283.0,

		CommitRandStdDev:       20.0,
		OpeningProofRandStdDev: 68.0,
		BlindRandStdDev:        10404567.0,

		OpenProofBound: math.Exp2(36.8),
		EvalProofBound: math.Exp2(55.7),
	}

	// ParametersLogN23LogP256 is a parameters set for commiting 2^23 degree polynomial over 256-bit prime field.
	ParamsLogN23LogP256 = ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 2,

		Degree:           1 << 23,
		BigIntCommitSize: 1 << 14,

		ModulusBase: 63388,
		Digits:      16,

		RingDegree:     1 << 11,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10.0,
		OpeningProofStdDev: 34.0,
		BlindStdDev:        5202283.0,

		CommitRandStdDev:       20.0,
		OpeningProofRandStdDev: 68.0,
		BlindRandStdDev:        10404567.0,

		OpenProofBound: math.Exp2(38.0),
		EvalProofBound: math.Exp2(56.9),
	}

	// ParametersLogN25LogP256 is a parameters set for commiting 2^25 degree polynomial over 256-bit prime field.
	ParamsLogN25LogP256 = ParametersLiteral{
		AjtaiSize:     1,
		AjtaiRandSize: 1 + 2,

		Degree:           1 << 25,
		BigIntCommitSize: 1 << 15,

		ModulusBase: 63388,
		Digits:      16,

		RingDegree:     1 << 11,
		LogRingModulus: []int{55, 55},

		CommitStdDev:       10.0,
		OpeningProofStdDev: 34.0,
		BlindStdDev:        5202283.0,

		CommitRandStdDev:       20.0,
		OpeningProofRandStdDev: 68.0,
		BlindRandStdDev:        10404567.0,

		OpenProofBound: math.Exp2(39.2),
		EvalProofBound: math.Exp2(58.1),
	}
)
