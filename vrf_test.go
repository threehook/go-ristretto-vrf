package vrf

import (
	"bytes"
	"fmt"
	"testing"
)

func TestHonestComplete(t *testing.T) {
	pk, sk := GenerateKey()

	alice := []byte("alice")
	aliceVRF := Compute(alice, sk)
	aliceVRFFromProof, aliceProof := Prove(alice, sk)

	//fmt.Printf("pk:           %X\n", pk)
	//fmt.Printf("sk:           %X\n", *sk)
	//fmt.Printf("alice(bytes): %X\n", alice)
	//fmt.Printf("aliceVRF:     %X\n", aliceVRF)
	//fmt.Printf("aliceProof:   %X\n", aliceProof)

	if !Verify(pk[:], alice, aliceVRF, aliceProof) {
		t.Errorf("Gen -> Compute -> Prove -> Verify -> FALSE")
	}
	if !bytes.Equal(aliceVRF, aliceVRFFromProof) {
		t.Errorf("Compute != Prove")
	}
}

func TestProof(t *testing.T) {
	alice := []byte{0x61, 0x6C, 0x69, 0x63, 0x65}
	sk := [64]byte{0xA3, 0xC7, 0x1D, 0x17, 0x7F, 0xC7, 0x6C, 0xEB, 0xFD, 0xB6, 0xC8, 0x94, 0x35, 0x3D, 0xD8, 0x6A, 0x2B, 0x4B, 0x0B, 0x7B, 0x0E, 0x83, 0xE6, 0x91, 0x3B, 0x60, 0x3D, 0x47, 0x19, 0x51, 0xE2, 0x45, 0xD4, 0x22, 0x0C, 0x7E, 0x62, 0xA4, 0xB1, 0xB2, 0x66, 0x7E, 0xD7, 0x47, 0x37, 0x22, 0x45, 0xA0, 0x9B, 0x6F, 0x79, 0xEA, 0x33, 0x0E, 0x05, 0x28, 0x23, 0x32, 0xE2, 0xEE, 0xEA, 0xD5, 0xB8, 0xAF}
	aliceVRFFromProof, aliceProof := Prove(alice, &sk)
	fmt.Printf("aliceProof:   %X\n", aliceProof)
	fmt.Printf("aliceVRFFromProof:   %X\n", aliceVRFFromProof)
}

func TestVerify(t *testing.T) {
	pk := []byte{0xBA, 0xF5, 0x43, 0xCF, 0xA7, 0x61, 0xAB, 0x43, 0xB6, 0xC8, 0x10, 0x40, 0x20, 0xDD, 0x07, 0x4B, 0x90, 0x7B, 0x96, 0x44, 0xA3, 0x15, 0x05, 0xE1, 0x1F, 0x0B, 0x6B, 0xAE, 0x47, 0x32, 0xAC, 0x7C}
	alice := []byte{0x61, 0x6C, 0x69, 0x63, 0x65}
	aliceVRF := []byte{0x49, 0xE1, 0x12, 0x4E, 0xE9, 0x76, 0x1A, 0x7A, 0xDC, 0xF8, 0xC3, 0x3C, 0x0D, 0x33, 0xF6, 0x20, 0x7E, 0x5C, 0xE6, 0xAB, 0xD5, 0xF6, 0xFE, 0xAD, 0x73, 0xD0, 0xBC, 0x84, 0xB1, 0xAB, 0xE9, 0xCF}
	aliceProof := []byte{0x78, 0x3E, 0xBA, 0xBA, 0xFD, 0xD7, 0x0F, 0xB9, 0x21, 0x6C, 0x3F, 0xE3, 0xF7, 0xD6, 0x52, 0x89, 0x24, 0xED, 0x93, 0x32, 0x52, 0x02, 0x91, 0x93, 0xDB, 0x58, 0x55, 0x36, 0x57, 0x6B, 0x05, 0x01, 0x44, 0x50, 0x40, 0x37, 0x2F, 0x06, 0x82, 0x75, 0x58, 0xC3, 0xE8, 0x7A, 0x9A, 0x68, 0x4D, 0x83, 0x98, 0x63, 0x59, 0x3B, 0x57, 0xD3, 0xBD, 0xC0, 0x9F, 0x09, 0x42, 0x21, 0xD8, 0xBF, 0x20, 0x08, 0x00, 0xF5, 0x01, 0xC3, 0xE8, 0xE4, 0xF4, 0xBC, 0xDD, 0xD9, 0xE2, 0x2D, 0x59, 0x00, 0xE7, 0x1C, 0xC8, 0x33, 0x64, 0xC2, 0x7C, 0x03, 0xB4, 0x67, 0xFB, 0x9A, 0x7E, 0x0B, 0x8D, 0xC0, 0x99, 0x22}

	if !Verify(pk, alice, aliceVRF, aliceProof) {
		t.Errorf("Gen -> Compute -> Prove -> Verify -> FALSE")
	}
}

//func TestUint64ArrayToInt32Array(t *testing.T) {
//	iA := uint64ArrayToInt32Array([]uint64{18446744073709551615, 123456789012344})
//	fmt.Println(iA)
//}

func TestFlipBitForgery(t *testing.T) {
	pk, sk := GenerateKey()
	alice := []byte("alice")
	for i := 0; i < 32; i++ {
		for j := uint(0); j < 8; j++ {
			aliceVRF := Compute(alice, sk)
			aliceVRF[i] ^= 1 << j
			_, aliceProof := Prove(alice, sk)
			if Verify(pk[:], alice, aliceVRF, aliceProof) {
				t.Fatalf("forged by using aliceVRF[%d]^=%d:\n (sk=%x)", i, j, sk)
			}
		}
	}
}

func BenchmarkCompute(b *testing.B) {
	_, sk := GenerateKey()
	alice := []byte("alice")
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		Compute(alice, sk)
	}
}

func BenchmarkProve(b *testing.B) {
	_, sk := GenerateKey()
	alice := []byte("alice")
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		Prove(alice, sk)
	}
}

func BenchmarkVerify(b *testing.B) {
	pk, sk := GenerateKey()
	alice := []byte("alice")
	aliceVRF := Compute(alice, sk)
	_, aliceProof := Prove(alice, sk)
	b.ResetTimer()
	for n := 0; n < b.N; n++ {
		Verify(pk[:], alice, aliceVRF, aliceProof)
	}
}
