package main

import (
	"bytes"
	"flag"
	"fmt"
	"math"
	"math/big"
	"os"
	"path/filepath"
	"regexp"
	"strings"

	"github.com/consensys/gnark-crypto/field/generator"
	"github.com/consensys/gnark-crypto/field/generator/config"
)

var (
	basePtr = flag.Uint64("b", 0, "The \"base\" of modulus in base 10. Ignored when -n is set.")
	expPtr  = flag.Uint64("k", 0, "The \"exponent\" of the modulus. Ignored when -n is set.")
	bitPtr  = flag.String("n", "", "The bit length of the modulus. Can be a single number or range (of the form \"<start>-<end>\"). If set, -b, -k is ignored, and the modulus is automatically set.")
	dirPtr  = flag.String("o", ".", "The output directory for the package.")
	pkgPtr  = flag.String("p", "zp", "The name of the package.")
)

const (
	maxRank   = 1 << 30
	baseBound = 1 << 20
)

func findModulus(bitStart, bitEnd int) (p *big.Int, b uint64, k uint64) {
	p = new(big.Int)
	maxLog2 := int(math.Ceil(math.Log2(float64(bitEnd))))

	for logk := 1; logk < maxLog2; logk++ {
		k := uint64(1) << logk
		kBig := big.NewInt(int64(k))

		bStart := uint64(math.Floor(math.Exp2((float64(bitStart) - 1) / float64(k))))
		bEnd := uint64(math.Ceil(math.Exp2(float64(bitEnd) / float64(k))))
		if bStart > baseBound {
			continue
		}

		for b := bStart; b <= min(math.MaxUint64, bEnd); b++ {
			bBig := big.NewInt(int64(b))
			bExpBig := new(big.Int).Exp(bBig, kBig, nil)
			p.Add(bExpBig, big.NewInt(1))

			if p.BitLen() < bitStart || p.BitLen() >= bitEnd {
				continue
			}

			if !p.ProbablyPrime(64) {
				continue
			}

			if new(big.Int).Mod(bExpBig, big.NewInt(2*maxRank)).Sign() != 0 {
				continue
			}

			if b > baseBound {
				continue
			}

			return p, b, k
		}
	}

	return nil, 0, 0
}

func main() {
	flag.Parse()

	var p *big.Int
	var b, k uint64

	bits := *bitPtr
	if bits != "" {
		bitStart, bitEnd := 0, 0
		if ok, _ := regexp.MatchString(`^\d+-\d+$`, bits); ok {
			fmt.Sscanf(bits, "%d-%d", &bitStart, &bitEnd)
		} else if ok, _ := regexp.MatchString(`^\d+$`, bits); ok {
			fmt.Sscanf(bits, "%d", &bitStart)
			bitEnd = bitStart + 1
		} else {
			fmt.Println("cannot parse bit length")
			os.Exit(1)
		}

		if bitStart >= bitEnd {
			fmt.Println("invalid bit length range")
			os.Exit(1)
		}

		p, b, k = findModulus(bitStart, bitEnd)
		if p == nil {
			fmt.Println("cannot find suitable modulus")
			os.Exit(1)
		}
	} else {
		b = *basePtr
		k = *expPtr

		if b == 0 || k == 0 {
			fmt.Println("either -b or -k is not set")
			os.Exit(1)
		}

		bBig := new(big.Int).SetUint64(b)
		kBig := new(big.Int).SetUint64(k)
		p = new(big.Int).Exp(bBig, kBig, nil)
		p.Add(p, big.NewInt(1))

		if !p.ProbablyPrime(64) {
			fmt.Println("modulus not prime")
			os.Exit(1)
		}
	}

	fmt.Printf("[*] Using %v-bit modulus: %v = %v^%v + 1\n", p.BitLen(), p, b, k)

	dir := *dirPtr
	pkg := *pkgPtr

	dir = filepath.Clean(dir)
	pkg = strings.ToLower(pkg)
	dir = filepath.Join(dir, pkg)

	f, err := config.NewFieldConfig(pkg, "Uint", p.String(), false)
	if err != nil {
		panic(err)
	}

	asm := &config.Assembly{
		IncludeDir: "asm",
		BuildDir:   filepath.Join(dir, "asm"),
	}

	err = generator.GenerateFF(f, dir, generator.WithASM(asm))
	if err != nil {
		panic(err)
	}

	newFunc := `
// New creates a new element, from possibly uninitialized memory.
func (z *Uint) New() *Uint {
	return new(Uint)
}

// Slice copies an underlying uint64 slice of z.
func (z *Uint) Slice(res []uint64) {
	_z := (*Uint)(unsafe.Pointer(&res[0]))
	copy(_z[:], z[:])
	fromMont(_z)
}

// Limb returns the length of z.
func (z *Uint) Limb() int {
	return len(z)
}
	`

	mainFile, err := os.ReadFile(filepath.Join(dir, "element.go"))
	if err != nil {
		panic(err)
	}

	newFile := bytes.Replace(mainFile, []byte("import ("), []byte("import (\n\t\"unsafe\""), 1)
	newFile = append(newFile, []byte(newFunc)...)

	err = os.WriteFile(filepath.Join(dir, "element.go"), newFile, 0644)
	if err != nil {
		panic(err)
	}
}
