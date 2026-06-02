package crt

// checkLength checks if all vectors have the same length,
// and panics if not.
func checkLength(xs ...int) {
	if len(xs) == 0 {
		return
	}

	for i := 1; i < len(xs); i++ {
		if xs[i] != xs[0] {
			panic("inconsistent input(s)")
		}
	}
}

// checkShape panics if e is not consistent with given ring parameters and modulus.
func checkShape(rank, modLen int, e *Element) {
	if len(e.Coeffs) != modLen {
		panic("input(s) shape not consistent")
	}

	for i := 0; i < modLen; i++ {
		if len(e.Coeffs[i]) != rank {
			panic("input(s) shape not consistent")
		}
	}
}

// isBinaryOperable panics if eOut, e0, e1 is not operable.
func isBinaryOperable(rank, modLen int, eOut, e0, e1 *Element) {
	if e0.Type() == TypeScalar && e1.Type() == TypeScalar {
		if eOut.Type() != TypeScalar {
			panic("output type not consistent")
		}
	} else {
		if eOut.Type() != TypePoly {
			panic("output type not consistent")
		}
		checkShape(rank, modLen, eOut)
		if e0.Type() == TypePoly {
			checkShape(rank, modLen, e0)
		}
		if e1.Type() == TypePoly {
			checkShape(rank, modLen, e1)
		}
		if e0.Type() == TypePoly && e1.Type() == TypePoly {
			if e0.IsNTT != e1.IsNTT {
				panic("input(s) NTT flag not consistent")
			}
		}
	}
}

// isUnaryOperable panics if eOut, e is not operable.
func isUnaryOperable(rank, modLen int, eOut, e *Element) {
	if e.Type() == TypeScalar {
		if eOut.Type() != TypeScalar {
			panic("output type not consistent")
		}
	} else {
		if eOut.Type() != TypePoly {
			panic("output type not consistent")
		}
		checkShape(rank, modLen, eOut)
		checkShape(rank, modLen, e)
	}
}

// isEqualType checks if given elements are of the same type.
func isEqualType(e0, e1 *Element, t ElementType) bool {
	return e0.Type() == t && e1.Type() == t
}

// orderByType returns e0, e1 as the order of scalar and poly.
// Assumes that one of e0, e1 is scalar and the other is poly.
func orderByType(e0, e1 *Element) (c *Element, p *Element) {
	if e0.Type() == TypeScalar {
		return e0, e1
	}
	return e1, e0
}
