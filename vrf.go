// Package vrf implements a verifiable random function using the Ristretto form
// of Curve25519, SHA3 and the Elligator2 map.
//
//     E is Curve25519 (in Ristretto coordinates), h is SHA3.
//     f is the elligator map (bytes->E) that covers half of E.
//     8 is the cofactor of E, the group order is 8*l for prime l.
//     Setup : the prover publicly commits to a public key (P : E)
//     H : names -> E
//         H(n) = f(h(n))^8
//     VRF : keys -> names -> vrfs
//         VRF_x(n) = h(n, H(n)^x))
//     Prove : keys -> names -> proofs
//         Prove_x(n) = tuple(c=h(n, g^r, H(n)^r), t=r-c*x, ii=H(n)^x)
//             where r = h(x, n) is used as a source of randomness
//     Check : E -> names -> vrfs -> proofs -> bool
//         Check(P, n, vrf, (c,t,ii)) = vrf == h(n, ii)
//                                     && c == h(n, g^t*P^c, H(n)^t*ii^c)
package vrf

import (
	"bytes"
	"encoding/binary"
	"github.com/bwesterb/go-ristretto"
	"golang.org/x/crypto/sha3"
)

const (
	PublicKeySize    = 32
	SecretKeySize    = 64
	Size             = 32
	intermediateSize = 32
	ProofSize        = 32 + 32 + intermediateSize
)

// GenerateKey creates a public/secret key pair.
func GenerateKey() (pk [PublicKeySize]byte, sk *[SecretKeySize]byte) {
	var secretKey ristretto.Scalar
	var digest [64]byte
	secretKey.Rand() // Generate a new secret key
	sk = new([SecretKeySize]byte)
	copy(sk[:32], secretKey.Bytes())

	h := sha3.NewShake256()
	h.Write(sk[:32])
	h.Read(digest[:])

	digest[0] &= 248
	digest[31] &= 127
	digest[31] |= 64

	var A ristretto.Point
	var hBytes [32]byte
	copy(hBytes[:], digest[:32])

	var hBytesScalar ristretto.Scalar
	hBytesScalar.SetBytes(&hBytes)

	A.ScalarMultBase(&hBytesScalar) // compute public key
	A.BytesInto(&pk)

	copy(sk[32:], pk[:])
	return
}

func expandSecret(sk *[SecretKeySize]byte) (x, skhr *[32]byte) {
	x, skhr = new([32]byte), new([32]byte)
	hash := sha3.NewShake256()
	hash.Write(sk[:32])
	hash.Read(x[:])
	hash.Read(skhr[:])
	x[0] &= 248
	x[31] &= 127
	x[31] |= 64
	return
}

func Compute(m []byte, sk *[SecretKeySize]byte) []byte {
	x, _ := expandSecret(sk)
	p := hashToCurve(m)

	var ii ristretto.Point
	var mScalar ristretto.Scalar
	mScalar.SetBytes(x)
	ii.ScalarMult(p, &mScalar)

	var iiB = new([32]byte)
	ii.BytesInto(iiB)
	hash := sha3.NewShake256()
	hash.Write(iiB[:]) // const length: Size
	hash.Write(m)
	var vrf [Size]byte
	hash.Read(vrf[:])
	return vrf[:]
}

// Prove returns the vrf value and a proof such that Verify(pk, m, vrf, proof) == true.
// The vrf value is the same as returned by Compute(m, sk).
func Prove(m []byte, sk *[SecretKeySize]byte) (vrf, proof []byte) {
	x, skhr := expandSecret(sk) // Create hashes
	var cH, rH [64]byte
	var r, c, minusC, t ristretto.Scalar
	var ii, gr, hr ristretto.Point
	hm := hashToCurve(m) // Hashed message to Point

	var xScalar ristretto.Scalar
	xScalar.SetBytes(x)
	ii.ScalarMult(hm, &xScalar)
	iiB := new([32]byte)
	ii.BytesInto(iiB)

	hash := sha3.NewShake256()
	hash.Write(skhr[:])
	hash.Write(sk[32:]) // public key
	hash.Write(m)
	hash.Read(rH[:])
	hash.Reset()
	r.SetReduced(&rH)

	gr.ScalarMultBase(&r)
	hr.ScalarMult(hm, &r)
	grB := new([32]byte)
	gr.BytesInto(grB)
	hrB := new([32]byte)
	hr.BytesInto(hrB)

	hash.Write(grB[:])
	hash.Write(hrB[:])
	hash.Write(m)
	hash.Read(cH[:])
	hash.Reset()
	c.SetReduced(&cH)
	minusC.Neg(&c)

	t.MulAdd(&xScalar, &minusC, &r)

	proof = make([]byte, ProofSize)
	copy(proof[:32], c.Bytes())
	copy(proof[32:64], t.Bytes())
	copy(proof[64:96], iiB[:])

	hash.Write(iiB[:]) // const length: Size
	hash.Write(m)
	vrf = make([]byte, Size)
	hash.Read(vrf[:])
	return
}

// Verify returns true if vrf=Compute(m, sk) for the sk that corresponds to pk.
func Verify(pkBytes, m, vrfBytes, proof []byte) bool {
	var pk, iiB, vrf, ABytes, BBytes [32]byte
	var b, cRef, c, t ristretto.Scalar

	if len(proof) != ProofSize || len(vrfBytes) != Size || len(pkBytes) != PublicKeySize {
		return false
	}

	copy(vrf[:], vrfBytes)
	copy(pk[:], pkBytes)
	copy(c[:32], proof[:32])
	copy(t[:32], proof[32:64])
	copy(iiB[:], proof[64:96])

	hash := sha3.NewShake256()
	hash.Write(iiB[:]) // const length
	hash.Write(m)
	var hCheck [Size]byte
	hash.Read(hCheck[:])
	if !bytes.Equal(hCheck[:], vrf[:]) {
		return false
	}
	hash.Reset()

	var P, ii, A, B, X, Y, J, K, R, S, hmtP, iicP ristretto.Point
	if !P.SetBytes(&pk) {
		return false
	}

	if !ii.SetBytes(&iiB) {
		return false
	}

	X.ScalarMultBase(&t)
	Y.ScalarMult(&P, &c)
	A.Add(&X, &Y)
	A.BytesInto(&ABytes)

	hm := hashToCurve(m)

	b.SetZero()
	J.ScalarMultBase(&b)
	K.ScalarMult(hm, &t)
	hmtP.Add(&J, &K)

	R.ScalarMultBase(&b)
	S.ScalarMult(&ii, &c)
	iicP.Add(&R, &S)

	B.Add(&hmtP, &iicP)
	B.BytesInto(&BBytes)

	var cH [64]byte
	hash.Write(ABytes[:]) // const length
	hash.Write(BBytes[:]) // const length
	hash.Write(m)
	hash.Read(cH[:])
	cRef.SetReduced(&cH)

	return cRef.Equals(&c)
}

func hashToCurve(m []byte) *ristretto.Point {
	var p ristretto.Point
	var hmb [32]byte
	sha3.ShakeSum256(hmb[:], m)
	p.SetElligator(&hmb)
	return &p
}

func uint64ArrayToInt32Array(uis []uint64) (iA []int32) {
	iA = []int32{}
	for _, ui := range uis {
		i, i2 := uint64ToInt32(ui)
		iA = append(iA, i, i2)
	}
	return
}

func uint64ToInt32(ui uint64) (i, i2 int32) {
	b := make([]byte, 8)
	binary.LittleEndian.PutUint64(b, uint64(ui))
	i |= int32(b[0])
	i |= int32(b[1]) << 8
	i |= int32(b[2]) << 16
	i |= int32(b[3]) << 24
	i2 |= int32(b[0])
	i2 |= int32(b[1]) << 32
	i2 |= int32(b[2]) << 40
	i2 |= int32(b[3]) << 48
	return
}
