package main

import (
	"C"
	"fmt"
	mcl "github.com/alinush/go-mcl"
	"math/bits"
	//kzg2 "github.com/protolambda/go-kzg"
	kzg2 "github.com/aulichney/go-kzg"
	bls "github.com/aulichney/go-kzg/bls"
	"github.com/sshravan/go-poly/ff"
	"math/rand"
)

//eventually move this somewhere else
func nextPowOf2(v uint64) uint64 {
	if v == 0 {
		return 1
	}
	return uint64(1) << bits.Len64(v-1)
}

// Returns true if polynomial A is a zero polynomial.
func IsPolyZero(a []bls.Fr) bool {

	n := len(a)
	if n == 0 {
		panic("IsPolyZero Error")
	}
	var flag bool
	flag = true
	for i := 0; i < n && flag == true; i++ {
		flag = flag && bls.EqualZero(&a[i])
	}
	return flag
}

//  Removes extraneous zero entries from in vector representation of polynomial.
//  Example - Degree-4 Polynomial: [0, 1, 2, 3, 4, 0, 0, 0, 0] -> [0, 1, 2, 3, 4]
//  Note: Simplest condensed form is a zero polynomial of vector form: [0]
func PolyCondense(a []bls.Fr) []bls.Fr {
	n := len(a)
	if n == 0 {
		panic("PolyCondense Error")
	}

	i := n
	for i > 1 {
		if bls.EqualZero(&a[i-1]) != true {
			break
		}
		i--
	}
	return a[:i]
}

// Compute a(x) * b(x)
func PolyMul(a []bls.Fr, b []bls.Fr) []bls.Fr {
	if IsPolyZero(a) || IsPolyZero(b) {
		return []bls.Fr{bls.ZERO}
	}

	aLen := len(a)
	bLen := len(b)
	if aLen == bLen && aLen == 1 {
		c := make([]bls.Fr, 1, 1)
		bls.MulModFr(&c[0], &a[0], &b[0])
		return c
	}
	n := uint64(2 * ff.Max(aLen, bLen))
	n = nextPowOf2(n)

	var padding []bls.Fr

	padding = make([]bls.Fr, n-uint64(aLen), n-uint64(aLen))
	a = append(a, padding...)

	padding = make([]bls.Fr, n-uint64(bLen), n-uint64(bLen))
	b = append(b, padding...)

	l := uint8(bits.Len64(n)) - 1 // n = 8 => 3 or 4?
	fs := kzg2.NewFFTSettings(l)

	evalsA, _ := fs.FFT(a, false)
	evalsB, _ := fs.FFT(b, false)

	res, _ := fs.FFT(bls.MulVecFr(evalsA, evalsB), true)
	res = res[:(aLen + bLen - 1)]
	res = PolyCondense(res)
	return res
}

func SubProductTree(a []bls.Fr) [][][]bls.Fr {
	// SubProdTree
	// Needs to be power of two
	// (x - a_1)(x - a_2)(x - a_3)(x - a_4)(x - a_5)(x - a_6)(x - a_7)(x - a_8)

	n := uint64(len(a))

	if ff.IsPowerOfTwo(n) == false {
		panic("SubProductTree inputs needs to be power of two")
	}

	l := uint8(bits.Len64(n)) - 1
	// fmt.Println(l)

	var M [][][]bls.Fr
	M = make([][][]bls.Fr, l+1, l+1)
	M[0] = make([][]bls.Fr, n, n)

	for j := uint64(0); j < n; j++ {
		M[0][j] = make([]bls.Fr, 2)

		bls.NegModFr(&M[0][j][0], &a[j])
		bls.IntAsFr(&M[0][j][1], 1)
	}

	var x []bls.Fr
	var y []bls.Fr
	var index int64
	index = 0
	for i := uint8(1); i <= l; i++ {
		L := uint64(1) << (l - i)
		M[i] = make([][]bls.Fr, L, L)
		for j := uint64(0); j < L; j++ {
			x = M[i-1][index]
			index++
			y = M[i-1][index]
			index++
			M[i][j] = PolyMul(x, y)
		}
		index = 0
	}

	return M
}

// Given M(x) computes  M'(x)
// For first derivative and multi-point evaluation:
// This [paper](https://arxiv.org/pdf/2002.10304.pdf) claims there is a faster way to do this
// Page 10 under interpolation
// Not sure how it is different from doing subproduct tree on M'(x)
func PolyDifferentiate(a []bls.Fr) []bls.Fr {
	n := uint64(len(a))
	if n == 0 {
		panic("PolyDifferentiate: Input is empty")
	}
	if n == 1 {
		return make([]bls.Fr, 1)
	}
	c := make([]bls.Fr, n, n)
	var temp bls.Fr
	for i := uint64(1); i < n; i++ {
		bls.IntAsFr(&temp, i)
		bls.MulModFr(&c[i], &a[i], &temp)
	}
	return c[1:]
}

func testPoly(polynomial ...uint64) []bls.Fr {
	n := len(polynomial)
	polynomialFr := make([]bls.Fr, n, n)
	for i := 0; i < n; i++ {
		bls.AsFr(&polynomialFr[i], polynomial[i])
	}
	return polynomialFr
}

func main() {
	//module initialization function, we use bls12-381, pairing-friendly elliptic curve
	mcl.InitFromString("bls12-381")

	//make vector of proofs
	const numProofs = int(3)
	const numCoeffs = int(16)

	//fill with random coefficients
	polyVec := [numProofs][numCoeffs]uint64{}
	for i := 0; i < numProofs; i++ {
		for j := 0; j < numCoeffs; j++ {
			polyVec[i][j] = rand.Uint64()
		}
	}

	for i := 0; i < numProofs; i++ {
		//setup
		fs := kzg2.NewFFTSettings(4)
		s1, s2 := kzg2.GenerateTestingSetup("1927409816240961209460912649124", 16+1)
		ks := kzg2.NewKZGSettings(fs, s1, s2)

		var polynomial = polyVec[i]

		//convert coeff vector to Fr
		polynomialFr := make([]bls.Fr, len(polynomial), len(polynomial))

		for j := 0; j < len(polynomial); j++ {
			bls.AsFr(&polynomialFr[j], polynomial[j])
		}
		//commit to this poly
		commitment := ks.CommitToPoly(polynomialFr)

		//evaluate polynomial at roots of unity
		x := uint64(5431)
		var xFr bls.Fr
		bls.AsFr(&xFr, x)

		cosetScale := uint8(3)
		coset := make([]bls.Fr, 1<<cosetScale, 1<<cosetScale)
		s1, s2 = kzg2.GenerateTestingSetup("1927409816240961209460912649124", 1<<cosetScale+1)
		ks = kzg2.NewKZGSettings(kzg2.NewFFTSettings(cosetScale), s1, s2)

		for k := 0; k < len(coset); k++ {
			fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
			bls.MulModFr(&coset[k], &xFr, &ks.ExpandedRootsOfUnity[k])
			fmt.Printf("coset %d: %s\n", i, bls.FrStr(&coset[i]))
		}

		//evaluate polynomial at each point
		ys := make([]bls.Fr, len(coset), len(coset))
		for l := 0; l < len(coset); l++ {
			bls.EvalPolyAt(&ys[l], polynomialFr, &coset[l])
			//fmt.Printf("ys %d: %s\n", l, bls.FrStr(&ys[l]))
		}

		//compute proof
		proof := ks.ComputeProofMulti(polynomialFr, x, uint64(len(coset)))
		fmt.Printf("proof %d: %s\n", i, bls.StrG1(proof))

		//Check that proof matches expected
		if !ks.CheckProofMulti(commitment, proof, &xFr, ys) {
			fmt.Printf("could not verify proof %d\n\n", i)
		}
		if ks.CheckProofMulti(commitment, proof, &xFr, ys) {
			fmt.Printf("proof %d verified!\n\n ", i)
		}
	}

	//compute A(x) using subproduct trees
	//x := uint64(5431)
	x := uint64(2)
	var xFr bls.Fr
	bls.AsFr(&xFr, x)

	cosetScale := uint8(3)
	coset := make([]bls.Fr, 1<<cosetScale, 1<<cosetScale)
	s1, s2 := kzg2.GenerateTestingSetup("1927409816240961209460912649124", 1<<cosetScale+1)
	ks := kzg2.NewKZGSettings(kzg2.NewFFTSettings(cosetScale), s1, s2)

	for k := 0; k < len(coset); k++ {
		fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
		bls.MulModFr(&coset[k], &xFr, &ks.ExpandedRootsOfUnity[k])
		fmt.Printf("coset %d: %s\n", k, bls.FrStr(&coset[k]))
	}

	//test := SubProductTree(*coset)

	/*for k := 0; k < len(aFr); k++ {
		//fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
		fmt.Printf("subproduct %d: %s\n", k, bls.FrStr(&aFr[k]))
	}*/

	//aPrimeFr := PolyDifferentiate(aFr)

	//polynomial2 := [16]uint64{1, 2, 3, 4, 7, 7, 7, 7, 13, 13, 13, 13, 13, 13, 13, 13}
	polynomial2 := testPoly(1, 2, 3, 4)

	testTree := SubProductTree(polynomial2)
	fmt.Printf("aFr: %s \n", bls.FrStr(&testTree[len(testTree)-1][0][1]))

	aFr := SubProductTree(coset)

	/*for i := 0; i < len(aFr); i++ {
		for j := 0; j < len(aFr[i]); j++ {
			fmt.Printf("aFr %d, %d: %s \n", i, j, bls.FrStr(&aFr[i][j][0]))
			fmt.Printf("aFr %d, %d: %s \n", i, j, bls.FrStr(&aFr[i][j][1]))
			fmt.Printf("\n")
		}
	}*/

	//fmt.Printf("aFr FINAL: %s \n", bls.FrStr(&aFr[len(aFr)-1][0][0]))

	aPrimeFr := PolyDifferentiate(aFr[len(aFr)-1][0])

	for i := 0; i < len(aFr); i++ {
		fmt.Printf("poly coeff AP %d: %s \n", i, bls.FrStr(&aFr[i][0][0]))
	}

	for i := 0; i < len(aPrimeFr); i++ {
		fmt.Printf("poly coeff APRIME %d: %s \n", i, bls.FrStr(&aPrimeFr[i]))
	}

	/*fmt.Print("TEST TREE \n")
	fmt.Print(len(testTree))
	fmt.Print(len(testTree[0]))
	fmt.Print(len(testTree[0][0]))
	fmt.Print("\n")

	for i := 0; i < len(testTree); i++ {
		for j := 0; j < len(testTree[i]); j++ {
			fmt.Printf("aFr %d, %d: %s \n", i, j, bls.FrStr(&testTree[i][j][0]))
			fmt.Printf("aFr %d, %d: %s \n", i, j, bls.FrStr(&testTree[i][j][1]))
			fmt.Printf("\n")
		}
	}*/

	//fmt.Print("\n")
	//fmt.Print(bls.FrStr(&testTree[0][1][0]))
	//fmt.Print("\n")
	//
	//fmt.Printf("test print: %s\n", bls.FrStr(&polynomial2[0]))
	//fmt.Printf("test print len: %d\n", len(polynomial2))
	//fmt.Print(len(aFr))
	//fmt.Print("separation")
	//fmt.Print(len(aFr[0]))

	//for i := 0; i < len(aFr); i++ {
	//	fmt.Printf("aFr %d: %s \n", i, bls.FrStr(&aFr[i]))
	//}
	//fmt.Print(reflect.TypeOf(aFr[len(aFr)]))

	//polynomial2Fr := make([]bls.Fr, len(polynomial2), len(polynomial2))

	//for i := 0; i < len(polynomial2); i++ {
	//	fmt.Printf("poly coeff %d: %s \n", i, bls.FrStr(&polynomial2[i]))
	//}

	/*polydiff := PolyDifferentiate(polynomial2)

	for i := 0; i < len(polydiff); i++ {
		fmt.Printf("poly diff coeff %d: %s \n", i, bls.FrStr(&polydiff[i]))
	}*/

	//print(bls.FrStr(&polynomial2Fr))

	//test2 := PolyDifferentiate(polynomial2Fr)

	//fmt.Print(bls.FrStr(&test2))

	//check relation between ff.Fr and
	/*x = uint64(3)
	y := uint64(4)

	var ffFr ff.Fr
	var ffFr2 ff.Fr
	var ffFr3 ff.Fr

	ff.AsFr(&ffFr, x)
	ff.AsFr(&ffFr2, y)

	ff.DivModFr(&ffFr3, &ffFr2, &ffFr)
	print(ff.FrStr(&ffFr3))
	print("\n")

	var blsFr bls.Fr
	var blsFr2 bls.Fr
	var blsFr3 bls.Fr

	bls.AsFr(&blsFr, x)
	bls.AsFr(&blsFr2, y)
	bls.DivModFr(&blsFr3, &blsFr2, &blsFr)

	print(bls.FrStr(&blsFr3))*/

	//bls12381.NewFr().setUint()

	//test := fft.SubProductTree(*coset)
	//fmt.Print(test)

	/*cosetScale = uint8(3)
	coset = make([]bls.Fr, 1<<cosetScale, 1<<cosetScale)
	//s1, s2 = kzg2.GenerateTestingSetup("1927409816240961209460912649124", 8+1)
	//ks = kzg2.NewKZGSettings(kzg2.NewFFTSettings(cosetScale), s1, s2)

	x = uint64(5431)
	var xFr bls.Fr
	bls.AsFr(&xFr, x)

	for k := 0; k < len(coset); k++ {
		//fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
		bls.MulModFr(&coset[k], &xFr, &fft.expandRootOfUnity[k])
		//fmt.Printf("coset %d: %s\n", i, bls.FrStr(&coset[i]))
	}

	bls.AsFr(&coset)

	test := SubProductTree(*coset)
	fmt.Print(test)*/

}
