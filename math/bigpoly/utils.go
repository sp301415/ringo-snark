package bigpoly

// IsPowerOfTwo returns true if n is a power of two.
func isPowerOfTwo(n int) bool {
	return n > 0 && (n&(n-1)) == 0
}
