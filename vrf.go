// Package vrf implements a verifiable random function using the Ristretto form
// of Curve25519, SHA3 and the Elligator2 map.
//
//     E is Curve25519 (in Edwards coordinates), h is SHA3.
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
//         Check(P, n, vrf, (c,t,ii)) = vrf == h(n, ii) && c == h(n, g^t*P^c, H(n)^t*ii^c)
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
func GenerateKey() (*[PublicKeySize]byte, *[SecretKeySize]byte) {
	var secretKey ristretto.Scalar
	var pk = new([PublicKeySize]byte)
	var sk = new([SecretKeySize]byte)
	var digest [64]byte

	secretKey.Rand() // Generate a new secret key
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
	A.BytesInto(pk)

	copy(sk[32:], pk[:])
	return pk, sk
}

func expandSecret(sk *[SecretKeySize]byte) (*[32]byte, *[32]byte) {
	var x, skhr = new([32]byte), new([32]byte)
	hash := sha3.NewShake256()
	hash.Write(sk[:32])
	hash.Read(x[:])
	hash.Read(skhr[:])
	x[0] &= 248
	x[31] &= 127
	x[31] |= 64
	return x, skhr
}

func Compute(m []byte, sk *[SecretKeySize]byte) []byte {
	var ii ristretto.Point
	var mScalar ristretto.Scalar
	var iiB, vrf [Size]byte

	x, _ := expandSecret(sk)
	p := hashToCurve(m)

	mScalar.SetBytes(x)
	ii.ScalarMult(p, &mScalar)
	ii.BytesInto(&iiB)
	hash := sha3.NewShake256()
	hash.Write(iiB[:]) // const length: Size
	hash.Write(m)

	hash.Read(vrf[:])
	return vrf[:]
}

// Prove returns the vrf value and a proof such that Verify(pk, d, vrf, proof) == true.
// The vrf value is the same as returned by Compute(d, sk).
//
// Prove_x(d) = tuple(c=h(d, g^r, H(d)^r), t=r-c*x, ii=H(d)^x) where r = h(x, d) is used as a source of randomness
// and x = secret key, d = data, c = encrypted composite of data and proof, t = encrypted c plus r and r = randomness
func Prove(d []byte, sk *[SecretKeySize]byte) ([]byte, []byte) { // Return vrf, proof
	x, skhr := expandSecret(sk) // Create two separate 32 byte hashes from the secret key 64 byte hash
	var cH, rH [SecretKeySize]byte
	var r, c, minusC, t ristretto.Scalar
	var ii, gr, hr ristretto.Point // ii = encrypted data, gr and hr = encrypted randomness
	var grB, hrB, iiB [Size]byte

	dP := hashToCurve(d) // Curve point of data

	var xSc ristretto.Scalar
	xSc.SetBytes(x)
	ii.ScalarMult(dP, &xSc) // ii=H(d)^x) where d = data and x = secret key
	ii.BytesInto(&iiB)

	// Create randomness
	// r = h(x, d) is used as a source of randomness where d = data and x = secret key
	hash := sha3.NewShake256()
	hash.Write(skhr[:])
	hash.Write(sk[32:])
	hash.Write(d)
	hash.Read(rH[:])
	hash.Reset()
	r.SetReduced(&rH)

	// Create curve points from randomness r
	gr.ScalarMultBase(&r)
	hr.ScalarMult(dP, &r)
	gr.BytesInto(&grB)
	hr.BytesInto(&hrB)

	hash.Write(grB[:])
	hash.Write(hrB[:])
	hash.Write(d)
	hash.Read(cH[:]) // Encrypted composite of data, proof and randomness
	hash.Reset()
	c.SetReduced(&cH)

	minusC.Neg(&c)
	t.MulAdd(&xSc, &minusC, &r) // t=r-c*x

	var proof = make([]byte, ProofSize)
	copy(proof[:32], c.Bytes())
	copy(proof[32:64], t.Bytes())
	copy(proof[64:96], iiB[:])

	// VRF_x(d) = h(d, H(d)^x)) where x = secret key and d = data
	hash.Write(iiB[:])
	hash.Write(d)
	var vrf = make([]byte, Size)
	hash.Read(vrf[:])
	return vrf, proof
}

// Verify returns true if vrf=Compute(data, sk) for the sk that corresponds to pk.
//
// Check(P, d, vrf, (c,t,ii)) = vrf == h(d, ii) && c == h(d, g^t*pkP^c, H(d)^t*ii^c)
func Verify(pkBytes, d, vrfBytes, proof []byte) bool {
	var pk, iiB, vrf, ABytes, BBytes, hCheck [Size]byte
	var scZero, cRef, c, t ristretto.Scalar

	if len(proof) != ProofSize || len(vrfBytes) != Size || len(pkBytes) != PublicKeySize {
		return false
	}
	scZero.SetZero() // Scalar zero

	copy(vrf[:], vrfBytes)
	copy(pk[:], pkBytes)
	copy(c[:32], proof[:32])   // Retrieve c = h(d, g^t*P^c, H(d)^t*ii^c) = encrypted composite of data, proof and randomness
	copy(t[:32], proof[32:64]) // Retrieve t = r-c = encrypted composite of data and proof
	copy(iiB[:], proof[64:96]) // Retrieve ii = encrypted data

	hash := sha3.NewShake256()
	hash.Write(iiB[:])
	hash.Write(d)
	hash.Read(hCheck[:]) // hCheck is supposed to be vrf
	if !bytes.Equal(hCheck[:], vrf[:]) {
		return false
	}
	hash.Reset()

	var pZero ristretto.Point
	var pkP, hmtP, iicP, ii, A, B, X, Y, R, S ristretto.Point
	// Get curve point of public key, consequently checking if it is on the Curve
	if !pkP.SetBytes(&pk) {
		return false
	}

	// Get curve point of encrypted data, consequently checking if it is on the Curve
	if !ii.SetBytes(&iiB) {
		return false
	}

	X.ScalarMultBase(&t)
	Y.ScalarMult(&pkP, &c)
	A.Add(&X, &Y) // A = encrypted composite of data, proof and randomness
	A.BytesInto(&ABytes)

	dP := hashToCurve(d) // dP = curve point of data

	pZero.ScalarMultBase(&scZero)
	R.ScalarMult(dP, &t) // R = encrypted composite of data and proof
	hmtP.Add(&pZero, &R)

	S.ScalarMult(&ii, &c) // S = ii * h(d, g^t*pkP^c, H(d)^t*ii^c) = encrypted data
	iicP.Add(&pZero, &S)

	B.Add(&hmtP, &iicP) // Create a new Point from composite of encrypted data and proof (R) and encrypted data (S)
	B.BytesInto(&BBytes)

	var cH [64]byte
	hash.Write(ABytes[:])
	hash.Write(BBytes[:])
	hash.Write(d)
	hash.Read(cH[:])
	cRef.SetReduced(&cH) // cRef must have same hash as encrypted composite of data, proof and randomness

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
