package main

import (
	. "github.com/mmcloughlin/avo/build"
	. "github.com/mmcloughlin/avo/operand"
	"github.com/mmcloughlin/avo/reg"
)

func Mul64HiAVX512(x0, x0Hi, x1, x1Hi, maskLo, xOut reg.VecVirtual) {
	xLoLo, xLoHi, xHiLo := ZMM(), ZMM(), ZMM()
	VPMULUDQ(x1, x0, xLoLo)
	VPMULUDQ(x1Hi, x0, xLoHi)
	VPMULUDQ(x1, x0Hi, xHiLo)
	VPMULUDQ(x1Hi, x0Hi, xOut)

	VPSRLQ(Imm(32), xLoLo, xLoLo)

	xMidHi, xMidLo := ZMM(), ZMM()
	VPADDQ(xLoLo, xLoHi, xMidHi)
	VPANDQ(maskLo, xMidHi, xMidLo)
	VPSRLQ(Imm(32), xMidHi, xMidHi)
	VPADDQ(xOut, xMidHi, xOut)

	VPADDQ(xMidLo, xHiLo, xMidHi)
	VPSRLQ(Imm(32), xMidHi, xMidHi)
	VPADDQ(xOut, xMidHi, xOut)
}
