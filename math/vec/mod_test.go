package vec_test

import (
	"fmt"
	"testing"

	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/sp301415/ringo-snark/math/vec"
	"github.com/stretchr/testify/assert"
)

var (
	rSrc      = csprng.NewUniformSamplerWithSeed(nil)
	benchLogN = []int{12, 13, 14, 15, 16, 17}
)

func testOps(t *testing.T, logQ int) {
	q := num.NewModulus(rSrc.SampleN(1<<logQ) | 1)

	N := 1 << 10
	v0 := make([]uint64, N)
	v1 := make([]uint64, N)
	vOut := make([]uint64, N)
	vOutCheck := make([]uint64, N)
	vOutInit := make([]uint64, N)

	for i := 0; i < N; i++ {
		v0[i] = rSrc.SampleN(q.Value())
		v1[i] = rSrc.SampleN(q.Value())
		vOutInit[i] = rSrc.SampleN(q.Value())
	}

	t.Run(fmt.Sprintf("LogQ=%v", logQ), func(t *testing.T) {
		t.Run("Add", func(t *testing.T) {
			vec.AddTo(vOut, v0, v1, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] + v1[i]
				if vOutCheck[i] >= q.Value() {
					vOutCheck[i] -= q.Value()
				}
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("AddWord", func(t *testing.T) {
			vec.AddTo(vOut, v0, v1, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] + v1[i]
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), 2*q.Value())
		})

		t.Run("AddScalar", func(t *testing.T) {
			vec.AddScalarTo(vOut, v0, v1[0], q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] + v1[0]
				if vOutCheck[i] >= q.Value() {
					vOutCheck[i] -= q.Value()
				}
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("AddScalarWord", func(t *testing.T) {
			vec.AddScalarTo(vOut, v0, v1[0], nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] + v1[0]
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), 2*q.Value())
		})

		t.Run("Sub", func(t *testing.T) {
			vec.SubTo(vOut, v0, v1, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] - v1[i]
				if vOutCheck[i] >= q.Value() {
					vOutCheck[i] += q.Value()
				}
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SubWord", func(t *testing.T) {
			vec.SubTo(vOut, v0, v1, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] - v1[i]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("SubScalar", func(t *testing.T) {
			vec.SubScalarTo(vOut, v0, v1[0], q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] - v1[0]
				if vOutCheck[i] >= q.Value() {
					vOutCheck[i] += q.Value()
				}
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SubScalarWord", func(t *testing.T) {
			vec.SubScalarTo(vOut, v0, v1[0], nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] - v1[0]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("Neg", func(t *testing.T) {
			vec.NegTo(vOut, v0, q)
			for i := 0; i < N; i++ {
				if v0[i] == 0 {
					vOutCheck[i] = 0
				} else {
					vOutCheck[i] = q.Value() - v0[i]
				}
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("NegWord", func(t *testing.T) {
			vec.NegTo(vOut, v0, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = -v0[i]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulScalar", func(t *testing.T) {
			vec.MulScalarTo(vOut, v0, v1[0], q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Mul(v0[i], v1[0], q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulAddScalar", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddScalarTo(vOut, v0, v1[0], q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Add(vOutCheck[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulSubScalar", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubScalarTo(vOut, v0, v1[0], q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Sub(vOutCheck[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulScalarLazy", func(t *testing.T) {
			vec.MulScalarLazyTo(vOut, v0, v1[0], q)

			assert.Less(t, vec.Max(vOut), 2*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Mul(v0[i], v1[0], q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulAddScalarLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddScalarLazyTo(vOut, v0, v1[0], q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Add(vOutInit[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulSubScalarLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubScalarLazyTo(vOut, v0, v1[0], q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Sub(vOutInit[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulScalarWord", func(t *testing.T) {
			vec.MulScalarTo(vOut, v0, v1[0], nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] * v1[0]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulAddScalarWord", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddScalarTo(vOut, v0, v1[0], nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] += v0[i] * v1[0]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulSubScalarWord", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubScalarTo(vOut, v0, v1[0], nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] -= v0[i] * v1[0]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		v1cS := num.SForm(v1[0], q)
		t.Run("SMulScalar", func(t *testing.T) {
			vec.SMulScalarTo(vOut, v0, v1[0], v1cS, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Mul(v0[i], v1[0], q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulAddScalar", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulAddScalarTo(vOut, v0, v1[0], v1cS, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Add(vOutCheck[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulSubScalar", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulSubScalarTo(vOut, v0, v1[0], v1cS, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Sub(vOutCheck[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulScalarLazy", func(t *testing.T) {
			vec.SMulScalarLazyTo(vOut, v0, v1[0], v1cS, q)

			assert.Less(t, vec.Max(vOut), 2*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Mul(v0[i], v1[0], q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("SMulAddScalarLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulAddScalarLazyTo(vOut, v0, v1[0], v1cS, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Add(vOutInit[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("SMulSubScalarLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulSubScalarLazyTo(vOut, v0, v1[0], v1cS, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Sub(vOutInit[i], num.Mul(v0[i], v1[0], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("Mul", func(t *testing.T) {
			vec.MulTo(vOut, v0, v1, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Mul(v0[i], v1[i], q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulAdd", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddTo(vOut, v0, v1, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Add(vOutCheck[i], num.Mul(v0[i], v1[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulSub", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubTo(vOut, v0, v1, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Sub(vOutCheck[i], num.Mul(v0[i], v1[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("MulLazy", func(t *testing.T) {
			vec.MulLazyTo(vOut, v0, v1, q)

			assert.Less(t, vec.Max(vOut), 2*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Mul(v0[i], v1[i], q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulAddLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddLazyTo(vOut, v0, v1, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Add(vOutInit[i], num.Mul(v0[i], v1[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulSubLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubLazyTo(vOut, v0, v1, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Sub(vOutInit[i], num.Mul(v0[i], v1[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulWord", func(t *testing.T) {
			vec.MulTo(vOut, v0, v1, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] * v1[i]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulAddWord", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulAddTo(vOut, v0, v1, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] += v0[i] * v1[i]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("MulSubWord", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.MulSubTo(vOut, v0, v1, nil)
			for i := 0; i < N; i++ {
				vOutCheck[i] -= v0[i] * v1[i]
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		v1S := vec.SForm(v1, q)

		t.Run("SMul", func(t *testing.T) {
			vec.SMulTo(vOut, v0, v1, v1S, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Mul(v0[i], v1[i], q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulAdd", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulAddTo(vOut, v0, v1, v1S, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Add(vOutCheck[i], num.SMul(v0[i], v1[i], v1S[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulSub", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulSubTo(vOut, v0, v1, v1S, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = num.Sub(vOutCheck[i], num.SMul(v0[i], v1[i], v1S[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)

			assert.Less(t, vec.Max(vOut), q.Value())
		})

		t.Run("SMulLazy", func(t *testing.T) {
			vec.SMulLazyTo(vOut, v0, v1, v1S, q)

			assert.Less(t, vec.Max(vOut), 2*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.SMul(v0[i], v1[i], v1S[i], q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("SMulAddLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulAddLazyTo(vOut, v0, v1, v1S, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Add(vOutInit[i], num.SMul(v0[i], v1[i], v1S[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("SMulSubLazy", func(t *testing.T) {
			copy(vOut, vOutInit)
			copy(vOutCheck, vOutInit)

			vec.SMulSubLazyTo(vOut, v0, v1, v1S, q)

			assert.Less(t, vec.Max(vOut), 3*q.Value())

			for i := 0; i < N; i++ {
				vOut[i] %= q.Value()
				vOutCheck[i] = num.Sub(vOutInit[i], num.SMul(v0[i], v1[i], v1S[i], q), q)
			}
			assert.Equal(t, vOutCheck, vOut)
		})

		t.Run("Reduce", func(t *testing.T) {
			for i := 0; i < N; i++ {
				v0[i] = rSrc.Sample()
			}

			vec.ReduceTo(vOut, v0, q)
			for i := 0; i < N; i++ {
				vOutCheck[i] = v0[i] % q.Value()
			}
			assert.Equal(t, vOutCheck, vOut)
		})
	})
}

func TestOps(t *testing.T) {
	testOps(t, num.MaxModulusBits)
}

func benchmarkOps(b *testing.B, logQ int) {
	q := num.NewModulus(rSrc.SampleN(1<<logQ) | 1)

	for _, logN := range benchLogN {
		N := 1 << logN
		v0 := make([]uint64, N)
		v1 := make([]uint64, N)
		v1S := make([]uint64, N)
		vOut := make([]uint64, N)

		for i := 0; i < N; i++ {
			v0[i] = rSrc.SampleN(q.Value())
			v1[i] = rSrc.SampleN(q.Value())
			v1S[i] = rSrc.SampleN(q.Value())
		}

		b.Run(fmt.Sprintf("LogN=%v", logN), func(b *testing.B) {
			b.Run(fmt.Sprintf("LogQ=%v", logQ), func(b *testing.B) {
				b.Run("Add", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.AddTo(vOut, v0, v1, q)
					}
				})

				b.Run("AddWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.AddTo(vOut, v0, v1, nil)
					}
				})

				b.Run("AddScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.AddScalarTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("AddScalarWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.AddScalarTo(vOut, v0, v1[0], nil)
					}
				})

				b.Run("Sub", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SubTo(vOut, v0, v1, q)
					}
				})

				b.Run("SubWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SubTo(vOut, v0, v1, nil)
					}
				})

				b.Run("SubScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SubScalarTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("SubScalarWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SubScalarTo(vOut, v0, v1[0], nil)
					}
				})

				b.Run("Neg", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.NegTo(vOut, v0, q)
					}
				})

				b.Run("MulScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulScalarTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulAddScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddScalarTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulSubScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubScalarTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulScalarLazyTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulAddScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddScalarLazyTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulSubScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubScalarLazyTo(vOut, v0, v1[0], q)
					}
				})

				b.Run("MulScalarWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulScalarTo(vOut, v0, v1[0], nil)
					}
				})

				b.Run("MulAddScalarWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddScalarTo(vOut, v0, v1[0], nil)
					}
				})

				b.Run("MulSubScalarWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubScalarTo(vOut, v0, v1[0], nil)
					}
				})

				b.Run("SMulScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulScalarTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("SMulAddScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulAddScalarTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("SMulSubScalar", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulSubScalarTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("SMulScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulScalarLazyTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("SMulAddScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulAddScalarLazyTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("SMulSubScalarLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulSubScalarLazyTo(vOut, v0, v1[0], v1S[0], q)
					}
				})

				b.Run("Mul", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulAdd", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulSub", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulLazyTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulAddLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddLazyTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulSubLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubLazyTo(vOut, v0, v1, q)
					}
				})

				b.Run("MulWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulTo(vOut, v0, v1, nil)
					}
				})

				b.Run("MulAddWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulAddTo(vOut, v0, v1, nil)
					}
				})

				b.Run("MulSubWord", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.MulSubTo(vOut, v0, v1, nil)
					}
				})

				b.Run("SForm", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SFormTo(vOut, v0, q)
					}
				})

				b.Run("SMul", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("SMulAdd", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulAddTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("SMulSub", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulSubTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("SMulLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulLazyTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("SMulAddLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulAddLazyTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("SMulSubLazy", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.SMulSubLazyTo(vOut, v0, v1, v1S, q)
					}
				})

				b.Run("Reduce", func(b *testing.B) {
					for i := 0; i < b.N; i++ {
						vec.ReduceTo(vOut, v0, q)
					}
				})
			})
		})
	}
}

func BenchmarkOps(b *testing.B) {
	benchmarkOps(b, num.MaxModulusBits)
}
