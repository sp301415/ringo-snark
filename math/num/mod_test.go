package num_test

import (
	"crypto/rand"
	"math/big"
	"testing"

	"github.com/sp301415/ringo-snark/math/csprng"
	"github.com/sp301415/ringo-snark/math/num"
	"github.com/stretchr/testify/assert"
)

var (
	rSrc = csprng.NewUniformSamplerWithSeed(nil)
)

func TestReduce(t *testing.T) {
	q := num.NewModulus(rSrc.SampleN(num.MaxModulus) | 1)

	x64 := rSrc.Sample()
	x128Hi := rSrc.Sample()
	x128Lo := rSrc.Sample()
	x128 := new(big.Int).Lsh(new(big.Int).SetUint64(x128Hi), 64)
	x128.Add(x128, new(big.Int).SetUint64(x128Lo))

	t.Run("Reduce", func(t *testing.T) {
		assert.Equal(t, num.Reduce(x64, q), x64%q.Value())
	})

	t.Run("Reduce128", func(t *testing.T) {
		x128.Mod(x128, new(big.Int).SetUint64(q.Value()))
		assert.Equal(t, num.Reduce128(x128Hi, x128Lo, q), x128.Uint64())
	})
}

func TestOps(t *testing.T) {
	qBig, err := rand.Prime(rSrc, num.MaxModulusBits)
	assert.NoError(t, err)

	q := num.NewModulus(qBig.Uint64())
	x0 := rSrc.SampleN(q.Value())
	x1 := rSrc.SampleN(q.Value())

	x0Big := new(big.Int).SetUint64(x0)
	x1Big := new(big.Int).SetUint64(x1)

	t.Run("Add", func(t *testing.T) {
		xAdd := num.Add(x0, x1, q)
		xAddBig := new(big.Int).Add(x0Big, x1Big)
		xAddBig.Mod(xAddBig, qBig)
		assert.Equal(t, xAddBig.Uint64(), xAdd)
	})

	t.Run("Sub", func(t *testing.T) {
		xSub := num.Sub(x0, x1, q)
		xSubBig := new(big.Int).Sub(x0Big, x1Big)
		xSubBig.Mod(xSubBig, qBig)
		assert.Equal(t, xSubBig.Uint64(), xSub)
	})

	xMulBig := new(big.Int).Mul(x0Big, x1Big)
	xMulBig.Mod(xMulBig, qBig)

	t.Run("Barrett", func(t *testing.T) {
		xMul := num.Mul(x0, x1, q)
		assert.Equal(t, xMulBig.Uint64(), xMul)
	})

	t.Run("Shoup", func(t *testing.T) {
		x1S := num.SForm(x1, q)
		xMul := num.SMul(x0, x1, x1S, q)
		assert.Equal(t, xMulBig.Uint64(), xMul)
	})

	t.Run("Exp", func(t *testing.T) {
		xExp := num.Exp(x0, x1, q)
		xExpBig := new(big.Int).Exp(x0Big, x1Big, qBig)
		assert.Equal(t, xExpBig.Uint64(), xExp)
	})

	t.Run("Inv", func(t *testing.T) {
		xInv := num.Inv(x0, q)
		xInvBig := new(big.Int).ModInverse(x0Big, qBig)
		assert.Equal(t, xInvBig.Uint64(), xInv)
	})
}
