//go:generate go run . -vec -out ../../math/vec/asm_mod_amd64.s -stubs ../../math/vec/asm_mod_stub_amd64.go -pkg=vec
//go:generate go run . -ntt -out ../../math/crt/asm_ntt_amd64.s -stubs ../../math/crt/asm_ntt_stub_amd64.go -pkg=crt
package main

import (
	"flag"

	. "github.com/mmcloughlin/avo/build"
	"github.com/mmcloughlin/avo/buildtags"
)

type OpType int

const (
	OpPure OpType = iota
	OpAdd
	OpSub
)

var (
	vec = flag.Bool("vec", false, "asm_mod_amd64.s")
	ntt = flag.Bool("ntt", false, "asm_ntt_pow2.s")
)

func main() {
	flag.Parse()

	Constraint(buildtags.Term("amd64"))
	Constraint(buildtags.Not("purego"))

	if *vec {
		VecConstants()

		VecAddSubToAVX512(OpAdd, false)
		VecAddSubToAVX512(OpAdd, true)
		VecAddSubToAVX512(OpSub, false)
		VecAddSubToAVX512(OpSub, true)

		VecAddSubScalarToAVX512(OpAdd, false)
		VecAddSubScalarToAVX512(OpAdd, true)
		VecAddSubScalarToAVX512(OpSub, false)
		VecAddSubScalarToAVX512(OpSub, true)

		VecNegToAVX512(false)
		VecNegToAVX512(true)

		VecMulScalarWordToAVX512(OpPure)
		VecMulScalarWordToAVX512(OpAdd)
		VecMulScalarWordToAVX512(OpSub)

		VecSMulScalarToAVX512(OpPure, false, true)
		VecSMulScalarToAVX512(OpAdd, false, true)
		VecSMulScalarToAVX512(OpSub, false, true)

		VecSMulScalarToAVX512(OpPure, true, true)
		VecSMulScalarToAVX512(OpAdd, true, true)
		VecSMulScalarToAVX512(OpSub, true, true)

		VecSMulScalarToAVX512(OpPure, false, false)
		VecSMulScalarToAVX512(OpAdd, false, false)
		VecSMulScalarToAVX512(OpSub, false, false)

		VecSMulScalarToAVX512(OpPure, true, false)
		VecSMulScalarToAVX512(OpAdd, true, false)
		VecSMulScalarToAVX512(OpSub, true, false)

		VecMulWordToAVX512(OpPure)
		VecMulWordToAVX512(OpAdd)
		VecMulWordToAVX512(OpSub)

		VecSMulToAVX512(OpPure, false, true)
		VecSMulToAVX512(OpAdd, false, true)
		VecSMulToAVX512(OpSub, false, true)

		VecSMulToAVX512(OpPure, true, true)
		VecSMulToAVX512(OpAdd, true, true)
		VecSMulToAVX512(OpSub, true, true)

		VecSMulToAVX512(OpPure, false, false)
		VecSMulToAVX512(OpAdd, false, false)
		VecSMulToAVX512(OpSub, false, false)

		VecSMulToAVX512(OpPure, true, false)
		VecSMulToAVX512(OpAdd, true, false)
		VecSMulToAVX512(OpSub, true, false)

		VecFMulToAVX512(OpPure)
		VecFMulToAVX512(OpAdd)
		VecFMulToAVX512(OpSub)
	}

	if *ntt {
		NTTConstants()

		FwdNTTInPlacePow2BaseUnrollAVX512()
		FwdNTTInPlacePow2StrideUnrollAVX512()

		InvNTTInPlacePow2BaseUnrollAVX512()
		InvNTTInPlacePow2StrideUnrollAVX512()

		FwdNTTInPlacePow2UnrollAVX512()
		InvNTTInPlacePow2UnrollAVX512()

		Reduce4Q()
	}

	Generate()
}
