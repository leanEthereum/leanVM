//go:build cgo

package leanpq

import (
	"bytes"
	"runtime"
	"sync"
	"testing"
)

func TestSphincsConcurrentVerifyStress(t *testing.T) {
	if old := runtime.GOMAXPROCS(0); old < 4 {
		runtime.GOMAXPROCS(4)
		defer runtime.GOMAXPROCS(old)
	}

	const keyCount = 4
	pks := make([][32]byte, keyCount)
	msgs := make([][32]byte, keyCount)
	sigs := make([]SphincsSignature, keyCount)
	for i := range keyCount {
		key := mustSphincsKey(t, bytes32(byte(0x20+i)))
		pks[i] = mustSphincsPublicKey(t, key)
		msgs[i] = bytes32(byte(0x80 + i))
		sig, err := key.Sign(msgs[i])
		if err != nil {
			t.Fatal(err)
		}
		sigs[i] = sig
	}

	var wg sync.WaitGroup
	errs := make(chan string, 64)
	for worker := range 16 {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for round := range 32 {
				idx := (worker + round) % keyCount
				if err := SphincsVerify(pks[idx], msgs[idx], sigs[idx]); err != nil {
					errs <- "valid leanSPHINCS signature rejected under concurrent cgo load"
					return
				}
				bad := sigs[idx]
				bad[(worker*257+round*13)%len(bad)] ^= 1 << byte((worker+round)%8)
				if SphincsVerify(pks[idx], msgs[idx], bad) == nil {
					errs <- "mutated leanSPHINCS signature accepted under concurrent cgo load"
					return
				}
			}
		}()
	}
	wg.Wait()
	close(errs)
	for msg := range errs {
		t.Error(msg)
	}
}

func TestSphincsBitFlipRegionsRejected(t *testing.T) {
	key := mustSphincsKey(t, bytes32(0x31))
	pk := mustSphincsPublicKey(t, key)
	msg := bytes32(0x62)
	sig, err := key.Sign(msg)
	if err != nil {
		t.Fatal(err)
	}
	if err := SphincsVerify(pk, msg, sig); err != nil {
		t.Fatalf("valid signature failed: %v", err)
	}

	// Probe every structural region of the 7740-byte signature:
	// randomizer (0..16), FORS openings (16..4240), layer 0 (4240..5396), layer 1 (5396..6552), layer 2 (6552..7740).
	offsets := []int{0, 15, 16, 31, 32, 1000, 4239, 4240, 4243, 4244, 5395, 5396, 5399, 6551, 6552, 6555, 7739}
	for _, off := range offsets {
		mutated := sig
		mutated[off] ^= 0x80
		if SphincsVerify(pk, msg, mutated) == nil {
			t.Fatalf("mutated signature at byte %d verified", off)
		}
	}
}

// FuzzSphincsVerify: edits of a valid (public key, message, signature) verify only when unedited.
func FuzzSphincsVerify(f *testing.F) {
	key, err := SphincsSecretKeyFromSeed(bytes32(0x41))
	if err != nil {
		f.Fatal(err)
	}
	f.Cleanup(key.Close)
	pk, err := key.PublicKey()
	if err != nil {
		f.Fatal(err)
	}
	msg := bytes32(0x91)
	sig, err := key.Sign(msg)
	if err != nil {
		f.Fatal(err)
	}
	valid := append(append(append([]byte{}, pk[:]...), msg[:]...), sig[:]...)
	f.Add(valid)
	f.Add(append(bytes.Clone(valid[:64]), make([]byte, len(sig))...))
	f.Fuzz(func(t *testing.T, data []byte) {
		if len(data) != len(valid) {
			return
		}
		var candidate SphincsSignature
		copy(candidate[:], data[64:])
		if SphincsVerify([32]byte(data[:32]), [32]byte(data[32:64]), candidate) == nil && !bytes.Equal(data, valid) {
			t.Fatal("an edited leanSPHINCS signature verified")
		}
	})
}
