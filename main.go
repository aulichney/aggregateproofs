package main

import (
	"C"
	"fmt"
	mcl "github.com/alinush/go-mcl"
	kzg2 "github.com/protolambda/go-kzg"
	//kzg2 "github.com/aulichney/go-aSVC/go-kzg"
	bls "github.com/protolambda/go-kzg/bls"
	"github.com/sshravan/go-poly/ff"
	"math/bits"
	"math/rand"
)

//go list -m all | grep github.com/aulichney/go-aSVC/go-kzg | awk '{print $2}'
////go mod edit -replace github.com/protolambda/go-kzg@v0.0.0=github.com/aulichney/go-aSVC/go-kzg@v1.2.3
//kzg2 "github.com/protolambda/go-kzg"
//hbls "github.com/herumi/bls-eth-go-binary/bls"
//"github.com/protolambda/go-kzg/bls"

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
		ff.IntAsFr(&M[0][j][1], 1)
	}

	var x []ff.Fr
	var y []ff.Fr
	var index int64
	index = 0
	for i := uint8(1); i <= l; i++ {
		L := uint64(1) << (l - i)
		M[i] = make([][]ff.Fr, L, L)
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

func main() {
	//module initialization function, we use bls12-381, pairing-friendly elliptic curve
	mcl.InitFromString("bls12-381")

	//make vector of proofs
	const numProofs = int(3)
	const numCoeffs = int(16)

	polyVec := [numProofs][numCoeffs]uint64{}
	for i := 0; i < numProofs; i++ {
		for j := 0; j < numCoeffs; j++ {
			polyVec[i][j] = rand.Uint64()
		}
	}

	for i := 0; i < numProofs; i++ {
		fs := kzg2.NewFFTSettings(4)
		s1, s2 := kzg2.GenerateTestingSetup("1927409816240961209460912649124", 16+1)
		ks := kzg2.NewKZGSettings(fs, s1, s2)

		var polynomial = polyVec[i]

		//polynomial := [16]uint64{1, 2, 3, 4, 7, 7, 7, 7, 13, 13, 13, 13, 13, 13, 13, 13}
		polynomialFr := make([]bls.Fr, len(polynomial), len(polynomial))

		for j := 0; j < len(polynomial); j++ {
			bls.AsFr(&polynomialFr[j], polynomial[j])
		}
		commitment := ks.CommitToPoly(polynomialFr)

		//evaluate polynomial at roots of unity
		x := uint64(5431)
		var xFr bls.Fr
		bls.AsFr(&xFr, x)
		cosetScale := uint8(3)
		coset := make([]bls.Fr, 1<<cosetScale, 1<<cosetScale)
		s1, s2 = kzg2.GenerateTestingSetup("1927409816240961209460912649124", 8+1)
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

	//need to make bls.Fr into ff.Fr so that I can use the subproduct tree function
	//at point where I have a vector of proofs

	//need to compute A(x) using subproduct trees

	x := uint64(5431)
	var xFr bls.Fr
	bls.AsFr(&xFr, x)
	cosetScale := uint8(3)
	coset := make([]bls.Fr, 1<<cosetScale, 1<<cosetScale)
	s1, s2 := kzg2.GenerateTestingSetup("1927409816240961209460912649124", 8+1)
	ks := kzg2.NewKZGSettings(kzg2.NewFFTSettings(cosetScale), s1, s2)

	for k := 0; k < len(coset); k++ {
		//fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
		bls.MulModFr(&coset[k], &xFr, &ks.ExpandedRootsOfUnity[k])
		//fmt.Printf("coset %d: %s\n", k, bls.FrStr(&coset[k]))
	}

	x = uint64(3)
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

	print(bls.FrStr(&blsFr3))

	//test := fft.SubProductTree(*coset)
	//fmt.Print(test)

	/*
		cosetScale := uint8(3)
		coset := make([]ff.Fr, 1<<cosetScale, 1<<cosetScale)
		//s1, s2 = kzg2.GenerateTestingSetup("1927409816240961209460912649124", 8+1)
		//ks = kzg2.NewKZGSettings(kzg2.NewFFTSettings(cosetScale), s1, s2)

		x := uint64(5431)
		var xFr ff.Fr
		ff.AsFr(&xFr, x)

		for k := 0; k < len(coset); k++ {
			//fmt.Printf("rootz %d: %s\n", k, bls.FrStr(&ks.ExpandedRootsOfUnity[k]))
			ff.MulModFr(&coset[k], &xFr, &fft.expandRootOfUnity[k])
			//fmt.Printf("coset %d: %s\n", i, bls.FrStr(&coset[i]))
		}

		ff.AsFr(&coset)

		test := fft.SubProductTree(*coset)
		fmt.Print(test)


	*/
}
