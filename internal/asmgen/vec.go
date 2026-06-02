package main

import (
	. "github.com/mmcloughlin/avo/build"
	. "github.com/mmcloughlin/avo/operand"
	"github.com/mmcloughlin/avo/reg"
)

func VecConstants() {
	ConstData("MASK_LO", U64(1<<32-1))
	ConstData("MASK_52", U64(1<<52-1))
}

func VecAddSubToAVX512(opType OpType, isWordOp bool) {
	switch opType {
	case OpAdd:
		if isWordOp {
			TEXT("addWordToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64)")
		} else {
			TEXT("addToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64, q uint64)")
		}
	case OpSub:
		if isWordOp {
			TEXT("subWordToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64)")
		} else {
			TEXT("subToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64, q uint64)")
		}
	}
	Pragma("noescape")

	q64, q := GP64(), ZMM()
	if !isWordOp {
		Load(Param("q"), q64)
		VPBROADCASTQ(NewParamAddr("q", 72), q)
	}

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v0 := Load(Param("v0").Base(), GP64())
	v1 := Load(Param("v1").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x0, x1 := ZMM(), ZMM()
	VMOVDQU64(Mem{Base: v0, Index: i, Scale: 8}, x0)
	VMOVDQU64(Mem{Base: v1, Index: i, Scale: 8}, x1)

	xOut := ZMM()
	switch opType {
	case OpAdd:
		VPADDQ(x1, x0, xOut)
		if !isWordOp {
			xSubQ := ZMM()
			VPSUBQ(q, xOut, xSubQ)
			VPMINUQ(xSubQ, xOut, xOut)
		}
	case OpSub:
		VPSUBQ(x1, x0, xOut)
		if !isWordOp {
			xAddQ := ZMM()
			VPADDQ(q, xOut, xAddQ)
			VPMINUQ(xAddQ, xOut, xOut)
		}
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y0, y1 := GP64(), GP64()
	MOVQ(Mem{Base: v0, Index: i, Scale: 8}, y0)
	MOVQ(Mem{Base: v1, Index: i, Scale: 8}, y1)

	switch opType {
	case OpAdd:
		ADDQ(y1, y0)
		if !isWordOp {
			subQ := GP64()
			MOVQ(y0, subQ)
			SUBQ(q64, subQ)
			CMPQ(q64, y0)
			CMOVQLS(subQ, y0)
		}
	case OpSub:
		SUBQ(y1, y0)
		if !isWordOp {
			subQ := GP64()
			MOVQ(y0, subQ)
			ADDQ(q64, subQ)
			CMPQ(q64, y0)
			CMOVQLS(subQ, y0)
		}
	}

	MOVQ(y0, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecAddSubScalarToAVX512(opType OpType, isWordOp bool) {
	switch opType {
	case OpAdd:
		if isWordOp {
			TEXT("addScalarWordToAVX512", NOSPLIT, "func(vOut, v []uint64, c uint64)")
		} else {
			TEXT("addScalarToAVX512", NOSPLIT, "func(vOut, v []uint64, c, q uint64)")
		}
	case OpSub:
		if isWordOp {
			TEXT("subScalarWordToAVX512", NOSPLIT, "func(vOut, v []uint64, c uint64)")
		} else {
			TEXT("subScalarToAVX512", NOSPLIT, "func(vOut, v []uint64, c, q uint64)")
		}
	}
	Pragma("noescape")

	q64, q := GP64(), ZMM()
	if !isWordOp {
		Load(Param("q"), q64)
		VPBROADCASTQ(NewParamAddr("q", 56), q)
	}

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v := Load(Param("v").Base(), GP64())

	c64 := Load(Param("c"), GP64())
	c := ZMM()
	VPBROADCASTQ(NewParamAddr("c", 48), c)

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x := ZMM()
	VMOVDQU64(Mem{Base: v, Index: i, Scale: 8}, x)

	xOut := ZMM()
	switch opType {
	case OpAdd:
		VPADDQ(c, x, xOut)
		if !isWordOp {
			xSubQ := ZMM()
			VPSUBQ(q, xOut, xSubQ)
			VPMINUQ(xSubQ, xOut, xOut)
		}
	case OpSub:
		VPSUBQ(c, x, xOut)
		if !isWordOp {
			xAddQ := ZMM()
			VPADDQ(q, xOut, xAddQ)
			VPMINUQ(xAddQ, xOut, xOut)
		}
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y := GP64()
	MOVQ(Mem{Base: v, Index: i, Scale: 8}, y)

	switch opType {
	case OpAdd:
		ADDQ(c64, y)
		if !isWordOp {
			subQ := GP64()
			MOVQ(y, subQ)
			SUBQ(q64, subQ)
			CMPQ(q64, y)
			CMOVQLS(subQ, y)
		}
	case OpSub:
		SUBQ(c64, y)
		if !isWordOp {
			subQ := GP64()
			MOVQ(y, subQ)
			ADDQ(q64, subQ)
			CMPQ(q64, y)
			CMOVQLS(subQ, y)
		}
	}

	MOVQ(y, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecNegToAVX512(isWordOp bool) {
	if isWordOp {
		TEXT("negWordToAVX512", NOSPLIT, "func(vOut, v []uint64)")
	} else {
		TEXT("negToAVX512", NOSPLIT, "func(vOut, v []uint64, q uint64)")
	}
	Pragma("noescape")

	zero := ZMM()
	if isWordOp {
		VPXORQ(zero, zero, zero)
	}

	q64, q := GP64(), ZMM()
	if !isWordOp {
		Load(Param("q"), q64)
		VPBROADCASTQ(NewParamAddr("q", 48), q)
	}

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v := Load(Param("v").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x := ZMM()
	VMOVDQU64(Mem{Base: v, Index: i, Scale: 8}, x)

	xOut := ZMM()
	if isWordOp {
		VPSUBQ(x, zero, xOut)
	} else {
		VPSUBQ(x, q, x)
		eqMask := K()
		VPCMPQ(Imm(0o4), x, q, eqMask)
		VMOVAPD_Z(x, eqMask, xOut)
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y := GP64()
	MOVQ(Mem{Base: v, Index: i, Scale: 8}, y)

	if isWordOp {
		NEGQ(y)
	} else {
		CMPQ(y, Imm(0))
		CMOVQEQ(q64, y)
		NEGQ(y)
		ADDQ(q64, y)
	}

	MOVQ(y, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecMulScalarWordToAVX512(opType OpType) {
	switch opType {
	case OpPure:
		TEXT("mulScalarWordToAVX512", NOSPLIT, "func(vOut, v []uint64, c uint64)")
	case OpAdd:
		TEXT("mulAddScalarWordToAVX512", NOSPLIT, "func(vOut, v []uint64, c uint64)")
	case OpSub:
		TEXT("mulSubScalarWordToAVX512", NOSPLIT, "func(vOut, v []uint64, c uint64)")
	}
	Pragma("noescape")

	c64 := Load(Param("c"), GP64())
	c := ZMM()
	VPBROADCASTQ(NewParamAddr("c", 48), c)

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v := Load(Param("v").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x := ZMM()
	VMOVDQU64(Mem{Base: v, Index: i, Scale: 8}, x)

	xOut, xMul := ZMM(), ZMM()
	VPMULLQ(x, c, xMul)

	switch opType {
	case OpPure:
		xOut = xMul
	case OpAdd:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPADDQ(xMul, xOut, xOut)
	case OpSub:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPSUBQ(xMul, xOut, xOut)
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y := GP64()
	MOVQ(Mem{Base: v, Index: i, Scale: 8}, y)

	yOut := GP64()
	IMULQ(c64, y)

	switch opType {
	case OpPure:
		yOut = y
	case OpAdd:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		ADDQ(y, yOut)
	case OpSub:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		SUBQ(y, yOut)
	}

	MOVQ(yOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecSMulScalarToAVX512(opType OpType, isLazy, isIFMA bool) {
	if !isIFMA {
		if !isLazy {
			switch opType {
			case OpPure:
				TEXT("sMulScalarToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpAdd:
				TEXT("sMulAddScalarToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpSub:
				TEXT("sMulSubScalarToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			}
		} else {
			switch opType {
			case OpPure:
				TEXT("sMulScalarLazyToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpAdd:
				TEXT("sMulAddScalarLazyToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpSub:
				TEXT("sMulSubScalarLazyToAVX512", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			}
		}
	} else {
		if !isLazy {
			switch opType {
			case OpPure:
				TEXT("sMulScalarToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpAdd:
				TEXT("sMulAddScalarToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpSub:
				TEXT("sMulSubScalarToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			}
		} else {
			switch opType {
			case OpPure:
				TEXT("sMulScalarLazyToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpAdd:
				TEXT("sMulAddScalarLazyToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			case OpSub:
				TEXT("sMulSubScalarLazyToAVX512IFMA", NOSPLIT, "func(vOut, v []uint64, c, cS, q uint64)")
			}
		}
	}
	Pragma("noescape")

	var maskLo, mask52 reg.VecVirtual
	if isIFMA {
		mask52 = ZMM()
		VPBROADCASTQ(NewDataAddr(NewStaticSymbol("MASK_52"), 0), mask52)
	} else {
		maskLo = ZMM()
		VPBROADCASTQ(NewDataAddr(NewStaticSymbol("MASK_LO"), 0), maskLo)
	}
	zero := ZMM()
	VPXORQ(zero, zero, zero)

	q64 := Load(Param("q"), GP64())
	q := ZMM()
	VPBROADCASTQ(NewParamAddr("q", 64), q)

	c64 := Load(Param("c"), GP64())
	cS64 := Load(Param("cS"), GP64())
	c, cS := ZMM(), ZMM()
	VPBROADCASTQ(NewParamAddr("c", 48), c)
	VPBROADCASTQ(NewParamAddr("cS", 56), cS)

	var cSHi reg.VecVirtual
	if !isIFMA {
		cSHi = ZMM()
		VPSRLQ(Imm(32), cS, cSHi)
	}

	if isIFMA {
		VPSRLQ(Imm(12), cS, cS)
	}

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v := Load(Param("v").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x := ZMM()
	VMOVDQU64(Mem{Base: v, Index: i, Scale: 8}, x)

	xOut, xMul := ZMM(), ZMM()

	quo := ZMM()

	if !isIFMA {
		xHi := ZMM()
		VPSRLQ(Imm(32), x, xHi)

		Mul64HiAVX512(x, xHi, cS, cSHi, maskLo, quo)
		VPMULLQ(quo, q, quo)

		VPMULLQ(x, c, xMul)
		VPSUBQ(quo, xMul, xMul)
	} else {
		VPXORQ(quo, quo, quo)
		VPMADD52HUQ(x, cS, quo)

		VPXORQ(xMul, xMul, xMul)
		VPMADD52LUQ(q, quo, xMul)
		VPSUBQ(xMul, zero, xMul)
		VPMADD52LUQ(x, c, xMul)
		VPANDQ(xMul, mask52, xMul)
	}

	if !isLazy {
		xSubQ := ZMM()
		VPSUBQ(q, xMul, xSubQ)
		VPMINUQ(xSubQ, xMul, xMul)
	}

	switch opType {
	case OpPure:
		xOut = xMul
	case OpAdd:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPADDQ(xMul, xOut, xOut)
		if !isLazy {
			xSubQ := ZMM()
			VPSUBQ(q, xOut, xSubQ)
			VPMINUQ(xSubQ, xOut, xOut)
		}
	case OpSub:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		if !isLazy {
			VPSUBQ(xMul, xOut, xOut)
			xAddQ := ZMM()
			VPADDQ(q, xOut, xAddQ)
			VPMINUQ(xAddQ, xOut, xOut)
		} else {
			VPADDQ(xMul, xOut, xOut)
		}
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y := GP64()
	MOVQ(Mem{Base: v, Index: i, Scale: 8}, y)

	yOut := GP64()

	quo64 := GP64()
	MOVQ(cS64, reg.RDX)
	MULXQ(y, yOut, quo64)
	IMULQ(q64, quo64)

	IMULQ(c64, y)
	SUBQ(quo64, y)

	if !isLazy {
		subQ := GP64()
		MOVQ(y, subQ)
		SUBQ(q64, subQ)
		CMPQ(q64, y)
		CMOVQLS(subQ, y)
	}

	switch opType {
	case OpPure:
		yOut = y
	case OpAdd:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		ADDQ(y, yOut)
		if !isLazy {
			subQ := GP64()
			MOVQ(yOut, subQ)
			SUBQ(q64, subQ)
			CMPQ(q64, yOut)
			CMOVQLS(subQ, yOut)
		}
	case OpSub:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		if !isLazy {
			SUBQ(y, yOut)
			subQ := GP64()
			MOVQ(yOut, subQ)
			ADDQ(q64, subQ)
			CMPQ(q64, yOut)
			CMOVQLS(subQ, yOut)
		} else {
			ADDQ(y, yOut)
		}
	}

	MOVQ(yOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecMulWordToAVX512(opType OpType) {
	switch opType {
	case OpPure:
		TEXT("mulWordToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64)")
	case OpAdd:
		TEXT("mulAddWordToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64)")
	case OpSub:
		TEXT("mulSubWordToAVX512", NOSPLIT, "func(vOut, v0, v1 []uint64)")
	}
	Pragma("noescape")

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v0 := Load(Param("v0").Base(), GP64())
	v1 := Load(Param("v1").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x0, x1 := ZMM(), ZMM()
	VMOVDQU64(Mem{Base: v0, Index: i, Scale: 8}, x0)
	VMOVDQU64(Mem{Base: v1, Index: i, Scale: 8}, x1)

	xOut, xMul := ZMM(), ZMM()
	VPMULLQ(x0, x1, xMul)

	switch opType {
	case OpPure:
		xOut = xMul
	case OpAdd:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPADDQ(xMul, xOut, xOut)
	case OpSub:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPSUBQ(xMul, xOut, xOut)
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y0, y1 := GP64(), GP64()
	MOVQ(Mem{Base: v0, Index: i, Scale: 8}, y0)
	MOVQ(Mem{Base: v1, Index: i, Scale: 8}, y1)

	yOut := GP64()
	IMULQ(y1, y0)

	switch opType {
	case OpPure:
		yOut = y0
	case OpAdd:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		ADDQ(y0, yOut)
	case OpSub:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		SUBQ(y0, yOut)
	}

	MOVQ(yOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecSMulToAVX512(opType OpType, isLazy, isIFMA bool) {
	if !isIFMA {
		if !isLazy {
			switch opType {
			case OpPure:
				TEXT("sMulToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpAdd:
				TEXT("sMulAddToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpSub:
				TEXT("sMulSubToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			}
		} else {
			switch opType {
			case OpPure:
				TEXT("sMulLazyToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpAdd:
				TEXT("sMulAddLazyToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpSub:
				TEXT("sMulSubLazyToAVX512", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			}
		}
	} else {
		if !isLazy {
			switch opType {
			case OpPure:
				TEXT("sMulToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpAdd:
				TEXT("sMulAddToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpSub:
				TEXT("sMulSubToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			}
		} else {
			switch opType {
			case OpPure:
				TEXT("sMulLazyToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpAdd:
				TEXT("sMulAddLazyToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			case OpSub:
				TEXT("sMulSubLazyToAVX512IFMA", NOSPLIT, "func(vOut, v0, v1, v1S []uint64, q uint64)")
			}
		}
	}
	Pragma("noescape")

	var maskLo, mask52 reg.VecVirtual
	if isIFMA {
		mask52 = ZMM()
		VPBROADCASTQ(NewDataAddr(NewStaticSymbol("MASK_52"), 0), mask52)
	} else {
		maskLo = ZMM()
		VPBROADCASTQ(NewDataAddr(NewStaticSymbol("MASK_LO"), 0), maskLo)
	}
	zero := ZMM()
	VPXORQ(zero, zero, zero)

	q64 := Load(Param("q"), GP64())
	q := ZMM()
	VPBROADCASTQ(NewParamAddr("q", 96), q)

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v0 := Load(Param("v0").Base(), GP64())
	v1 := Load(Param("v1").Base(), GP64())
	v1S := Load(Param("v1S").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x0, x1, x1S := ZMM(), ZMM(), ZMM()
	VMOVDQU64(Mem{Base: v0, Index: i, Scale: 8}, x0)
	VMOVDQU64(Mem{Base: v1, Index: i, Scale: 8}, x1)
	VMOVDQU64(Mem{Base: v1S, Index: i, Scale: 8}, x1S)

	if opType == OpSub && isLazy {
		VPSUBQ(x0, q, x0)
	}

	xOut, xMul := ZMM(), ZMM()

	quo := ZMM()

	if !isIFMA {
		x0Hi, x1SHi := ZMM(), ZMM()
		VPSRLQ(Imm(32), x0, x0Hi)
		VPSRLQ(Imm(32), x1S, x1SHi)

		Mul64HiAVX512(x0, x0Hi, x1S, x1SHi, maskLo, quo)
		VPMULLQ(quo, q, quo)

		VPMULLQ(x0, x1, xMul)
		VPSUBQ(quo, xMul, xMul)
	} else {
		VPSRLQ(Imm(12), x1S, x1S)
		VPXORQ(quo, quo, quo)
		VPMADD52HUQ(x0, x1S, quo)

		VPXORQ(xMul, xMul, xMul)
		VPMADD52LUQ(q, quo, xMul)
		VPSUBQ(xMul, zero, xMul)
		VPMADD52LUQ(x1, x0, xMul)
		VPANDQ(xMul, mask52, xMul)

	}

	if !isLazy {
		xSubQ := ZMM()
		VPSUBQ(q, xMul, xSubQ)
		VPMINUQ(xSubQ, xMul, xMul)
	}

	switch opType {
	case OpPure:
		xOut = xMul
	case OpAdd:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		VPADDQ(xMul, xOut, xOut)
		if !isLazy {
			xSubQ := ZMM()
			VPSUBQ(q, xOut, xSubQ)
			VPMINUQ(xSubQ, xOut, xOut)
		}
	case OpSub:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)
		if !isLazy {
			VPSUBQ(xMul, xOut, xOut)
			xAddQ := ZMM()
			VPADDQ(q, xOut, xAddQ)
			VPMINUQ(xAddQ, xOut, xOut)
		} else {
			VPADDQ(xMul, xOut, xOut)
		}
	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	JMP(LabelRef("leftover_loop_end"))
	Label("leftover_loop_body")

	y0, y1, y1S := GP64(), GP64(), GP64()
	MOVQ(Mem{Base: v0, Index: i, Scale: 8}, y0)
	MOVQ(Mem{Base: v1, Index: i, Scale: 8}, y1)
	MOVQ(Mem{Base: v1S, Index: i, Scale: 8}, y1S)

	if opType == OpSub && isLazy {
		SUBQ(q64, y0)
		NEGQ(y0)
	}

	yOut := GP64()

	quo64 := GP64()
	MOVQ(y1S, reg.RDX)
	MULXQ(y0, y1S, quo64)
	IMULQ(q64, quo64)

	IMULQ(y1, y0)
	SUBQ(quo64, y0)

	if !isLazy {
		subQ := GP64()
		MOVQ(y0, subQ)
		SUBQ(q64, subQ)
		CMPQ(q64, y0)
		CMOVQLS(subQ, y0)
	}

	switch opType {
	case OpPure:
		yOut = y0
	case OpAdd:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		ADDQ(y0, yOut)
		if !isLazy {
			subQ := GP64()
			MOVQ(yOut, subQ)
			SUBQ(q64, subQ)
			CMPQ(q64, yOut)
			CMOVQLS(subQ, yOut)
		}
	case OpSub:
		MOVQ(Mem{Base: vOut, Index: i, Scale: 8}, yOut)
		if !isLazy {
			SUBQ(y0, yOut)
			subQ := GP64()
			MOVQ(yOut, subQ)
			ADDQ(q64, subQ)
			CMPQ(q64, yOut)
			CMOVQLS(subQ, yOut)
		} else {
			ADDQ(y0, yOut)
		}
	}

	MOVQ(yOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(1), i)

	Label("leftover_loop_end")
	CMPQ(i, N)
	JL(LabelRef("leftover_loop_body"))

	RET()
}

func VecFMulToAVX512(opType OpType) {
	switch opType {
	case OpPure:
		TEXT("fMulToAVX512F", NOSPLIT, "func(vOut, v0, v1 []uint64, q uint64, qf, qfInv float64)")
	case OpAdd:
		TEXT("fMulAddToAVX512F", NOSPLIT, "func(vOut, v0, v1 []uint64, q uint64, qf, qfInv float64)")
	case OpSub:
		TEXT("fMulSubToAVX512F", NOSPLIT, "func(vOut, v0, v1 []uint64, q uint64, qf, qfInv float64)")
	}
	Pragma("noescape")

	zero := ZMM()
	VPXORQ(zero, zero, zero)

	q, qf, qfInv := ZMM(), ZMM(), ZMM()
	VPBROADCASTQ(NewParamAddr("q", 72), q)
	VPBROADCASTQ(NewParamAddr("qf", 80), qf)
	VPBROADCASTQ(NewParamAddr("qfInv", 88), qfInv)

	N := Load(Param("vOut").Len(), GP64())
	vOut := Load(Param("vOut").Base(), GP64())
	v0 := Load(Param("v0").Base(), GP64())
	v1 := Load(Param("v1").Base(), GP64())

	M := GP64()
	MOVQ(N, M)
	SHRQ(Imm(3), M)
	SHLQ(Imm(3), M)

	i := GP64()
	XORQ(i, i)
	JMP(LabelRef("loop_end"))
	Label("loop_body")

	x0, x1 := ZMM(), ZMM()
	VMOVDQU64(Mem{Base: v0, Index: i, Scale: 8}, x0)
	VMOVDQU64(Mem{Base: v1, Index: i, Scale: 8}, x1)

	xOut, xMul := ZMM(), ZMM()

	VCVTUQQ2PD_RU_SAE(x0, x0)
	VCVTUQQ2PD_RU_SAE(x1, x1)

	hi, lo := ZMM(), ZMM()
	VMULPD(x0, x1, hi)
	VMOVAPD(hi, lo)
	VFMSUB231PD(x0, x1, lo)

	quo, rem := ZMM(), ZMM()
	VMULPD(hi, qfInv, quo)
	VRNDSCALEPD(Imm(0x1), quo, quo)
	VMOVAPD(hi, rem)
	VFNMADD231PD(quo, qf, rem)

	VADDPD(rem, lo, xMul)
	negMask := K()
	VCMPPD(Imm(0x11), zero, xMul, negMask)
	VADDPD(xMul, qf, negMask, xMul)

	VCVTPD2UQQ_RU_SAE(xMul, xMul)

	switch opType {
	case OpPure:
		xOut = xMul
	case OpAdd:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)

		VPADDQ(xMul, xOut, xOut)
		xSubQ := ZMM()
		VPSUBQ(q, xOut, xSubQ)
		VPMINUQ(xSubQ, xOut, xOut)
	case OpSub:
		VMOVDQU64(Mem{Base: vOut, Index: i, Scale: 8}, xOut)

		VPSUBQ(xMul, xOut, xOut)
		xAddQ := ZMM()
		VPADDQ(q, xOut, xAddQ)
		VPMINUQ(xAddQ, xOut, xOut)

	}

	VMOVDQU64(xOut, Mem{Base: vOut, Index: i, Scale: 8})

	ADDQ(Imm(8), i)

	Label("loop_end")
	CMPQ(i, M)
	JL(LabelRef("loop_body"))

	RET()
}
