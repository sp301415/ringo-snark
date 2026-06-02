package num

// Unsigned represents the unsigned Integer type.
type Unsigned interface {
	uint | uint8 | uint16 | uint32 | uint64
}

// Integer represents the Integer type.
type Integer interface {
	Unsigned | int | int8 | int16 | int32 | int64
}

// Real represents the Integer and Float type.
type Real interface {
	Integer | float32 | float64
}

// Number represents Integer, Float, and Complex type.
type Number interface {
	Real | complex64 | complex128
}
