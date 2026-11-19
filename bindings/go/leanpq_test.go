package leanpq

import (
	"reflect"
	"runtime"
	"sync"
	"testing"
)

func TestEncodingLengths(t *testing.T) {
	if got := len(SphincsSignature{}); got != 7740 {
		t.Fatalf("leanSPHINCS signature length = %d, want 7740", got)
	}
	if sphincsRecordLen != 7804 {
		t.Fatalf("leanSPHINCS record length = %d, want 7804", sphincsRecordLen)
	}
	if got := len(XmssSignature{}); got != 2404 {
		t.Fatalf("leanXMSS signature length = %d, want 2404", got)
	}
	if xmssRecordLen != 2468 {
		t.Fatalf("leanXMSS record length = %d, want 2468", xmssRecordLen)
	}
}

func TestSignAndVerify(t *testing.T) {
	message := bytes32(0x42)
	other := bytes32(0x43)

	xmssKey := mustXmssKey(t, bytes32(1))
	xmssPublicKey := mustXmssPublicKey(t, xmssKey)
	xmssSignature, err := xmssKey.Sign(message, 3)
	if err != nil {
		t.Fatal(err)
	}
	if err := XmssVerify(xmssPublicKey, message, xmssSignature); err != nil {
		t.Fatalf("leanXMSS signature must verify: %v", err)
	}
	if XmssVerify(xmssPublicKey, other, xmssSignature) == nil {
		t.Fatal("leanXMSS signature must not verify under another message")
	}

	sphincsKey := mustSphincsKey(t, bytes32(2))
	sphincsPublicKey := mustSphincsPublicKey(t, sphincsKey)
	sphincsSignature, err := sphincsKey.Sign(message)
	if err != nil {
		t.Fatal(err)
	}
	if err := SphincsVerify(sphincsPublicKey, message, sphincsSignature); err != nil {
		t.Fatalf("leanSPHINCS signature must verify: %v", err)
	}
	if SphincsVerify(sphincsPublicKey, other, sphincsSignature) == nil {
		t.Fatal("leanSPHINCS signature must not verify under another message")
	}
}

func TestXmssKeyLoadsFromItsTreeCache(t *testing.T) {
	message := bytes32(7)
	seed := bytes32(8)

	key := mustXmssKey(t, seed)
	if err := key.Prepare(3); err != nil {
		t.Fatal(err)
	}
	cache, err := key.CacheBytes()
	if err != nil {
		t.Fatal(err)
	}
	publicKey := mustXmssPublicKey(t, key)
	loaded, err := XmssSecretKeyFromCacheBytes(seed, publicKey, cache)
	if err != nil {
		t.Fatal(err)
	}
	defer loaded.Close()
	if mustXmssPublicKey(t, loaded) != publicKey {
		t.Fatal("loaded leanXMSS key must keep its public key")
	}
	want, err := key.Sign(message, 3)
	if err != nil {
		t.Fatal(err)
	}
	got, err := loaded.Sign(message, 3)
	if err != nil {
		t.Fatal(err)
	}
	if got != want {
		t.Fatal("loaded leanXMSS key must sign as the original")
	}
	if err := XmssVerify(publicKey, message, got); err != nil {
		t.Fatal(err)
	}
	if _, err := XmssSecretKeyFromCacheBytes(seed, publicKey, cache[1:]); err == nil {
		t.Fatal("a cache of another length must be rejected")
	}
	tampered := append([]byte(nil), cache...)
	tampered[0] ^= 1
	if _, err := XmssSecretKeyFromCacheBytes(seed, publicKey, tampered); err == nil {
		t.Fatal("a tampered cache must be rejected")
	}
	otherKey := mustXmssPublicKey(t, mustXmssKey(t, bytes32(9)))
	if _, err := XmssSecretKeyFromCacheBytes(seed, otherKey, cache); err == nil {
		t.Fatal("a cache under another key's public key must be rejected")
	}
}

func TestSecretKeysRoundTripThroughBytes(t *testing.T) {
	message := bytes32(7)

	xmssKey := mustXmssKey(t, bytes32(3))
	encoded, err := xmssKey.Bytes()
	if err != nil {
		t.Fatal(err)
	}
	restoredXmss, err := XmssSecretKeyFromBytes(encoded)
	if err != nil {
		t.Fatal(err)
	}
	defer restoredXmss.Close()
	xmssPublicKey := mustXmssPublicKey(t, xmssKey)
	if mustXmssPublicKey(t, restoredXmss) != xmssPublicKey {
		t.Fatal("restored leanXMSS key must keep its public key")
	}
	xmssSignature, err := restoredXmss.Sign(message, 9)
	if err != nil {
		t.Fatal(err)
	}
	if err := XmssVerify(xmssPublicKey, message, xmssSignature); err != nil {
		t.Fatal(err)
	}

	sphincsKey := mustSphincsKey(t, bytes32(4))
	encoded, err = sphincsKey.Bytes()
	if err != nil {
		t.Fatal(err)
	}
	if len(encoded) != 32 {
		t.Fatalf("leanSPHINCS secret key encoding has %d bytes, want 32", len(encoded))
	}
	restoredSphincs, err := SphincsSecretKeyFromBytes(encoded)
	if err != nil {
		t.Fatal(err)
	}
	defer restoredSphincs.Close()
	sphincsPublicKey := mustSphincsPublicKey(t, sphincsKey)
	if mustSphincsPublicKey(t, restoredSphincs) != sphincsPublicKey {
		t.Fatal("restored leanSPHINCS key must keep its public key")
	}
	sphincsSignature, err := restoredSphincs.Sign(message)
	if err != nil {
		t.Fatal(err)
	}
	if err := SphincsVerify(sphincsPublicKey, message, sphincsSignature); err != nil {
		t.Fatal(err)
	}
}

func TestAggregateRecursively(t *testing.T) {
	if err := Setup(); err != nil {
		t.Fatal(err)
	}
	first := bytes32(0x11)
	second := bytes32(0x22)
	xmssKey := mustXmssKey(t, bytes32(5))
	xmssPublicKey := mustXmssPublicKey(t, xmssKey)
	sphincsKey := mustSphincsKey(t, bytes32(6))
	sphincsPublicKey := mustSphincsPublicKey(t, sphincsKey)

	firstXmss, err := xmssKey.Sign(first, 0)
	if err != nil {
		t.Fatal(err)
	}
	left, err := AggregateSignatures(nil, []XmssSignedMessage{{xmssPublicKey, first, firstXmss}}, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer left.Close()

	sphincsSignature, err := sphincsKey.Sign(first)
	if err != nil {
		t.Fatal(err)
	}
	right, err := AggregateSignatures(nil, nil, []SphincsSignedMessage{{sphincsPublicKey, first, sphincsSignature}})
	if err != nil {
		t.Fatal(err)
	}
	defer right.Close()

	secondXmss, err := xmssKey.Sign(second, 1)
	if err != nil {
		t.Fatal(err)
	}
	root, err := AggregateSignatures(
		[]*Aggregate{left, right}, []XmssSignedMessage{{xmssPublicKey, second, secondXmss}}, nil,
	)
	if err != nil {
		t.Fatal(err)
	}
	defer root.Close()

	encoded, err := root.Bytes()
	if err != nil {
		t.Fatal(err)
	}
	expectedXmss := []Claim{{xmssPublicKey, first}, {xmssPublicKey, second}}
	expectedSphincs := []Claim{{sphincsPublicKey, first}}
	rootXmss, err := root.XmssClaims()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(rootXmss, expectedXmss) {
		t.Fatalf("root leanXMSS claims = %x, want %x", rootXmss, expectedXmss)
	}

	// The receiver rebuilds the claims in any order; a repeated claim counts once.
	received, err := AggregateFromBytes(
		encoded, []Claim{{xmssPublicKey, second}, {xmssPublicKey, first}, {xmssPublicKey, second}}, expectedSphincs,
	)
	if err != nil {
		t.Fatal(err)
	}
	defer received.Close()
	xmssClaims, err := received.XmssClaims()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(xmssClaims, expectedXmss) {
		t.Fatalf("leanXMSS claims = %x, want %x", xmssClaims, expectedXmss)
	}
	sphincsClaims, err := received.SphincsClaims()
	if err != nil {
		t.Fatal(err)
	}
	if !reflect.DeepEqual(sphincsClaims, expectedSphincs) {
		t.Fatalf("leanSPHINCS claims = %x, want %x", sphincsClaims, expectedSphincs)
	}

	reencoded, err := received.Bytes()
	if err != nil {
		t.Fatal(err)
	}
	roundTrip, err := AggregateFromBytes(reencoded, xmssClaims, sphincsClaims)
	if err != nil {
		t.Fatalf("an aggregate must decode against its own claims: %v", err)
	}
	roundTrip.Close()

	wrongClaims := []struct {
		name    string
		xmss    []Claim
		sphincs []Claim
	}{
		{"one leanXMSS claim short", expectedXmss[:1], expectedSphincs},
		{"no leanSPHINCS claim", expectedXmss, nil},
		{"another leanXMSS message", []Claim{{xmssPublicKey, first}, {xmssPublicKey, bytes32(0x33)}}, expectedSphincs},
		{"an extra leanSPHINCS claim", expectedXmss, []Claim{{sphincsPublicKey, first}, {sphincsPublicKey, second}}},
		{"claims of the wrong scheme", expectedSphincs, expectedXmss},
	}
	for _, claims := range wrongClaims {
		if wrong, err := AggregateFromBytes(encoded, claims.xmss, claims.sphincs); err == nil {
			wrong.Close()
			t.Fatalf("the proof must be rejected against %s", claims.name)
		}
	}

	truncated := encoded[:len(encoded)-1]
	if wrong, err := AggregateFromBytes(truncated, expectedXmss, expectedSphincs); err == nil {
		wrong.Close()
		t.Fatal("truncated aggregate bytes must be rejected")
	}
	tampered := append([]byte(nil), encoded...)
	tampered[len(tampered)/2] ^= 1
	if wrong, err := AggregateFromBytes(tampered, expectedXmss, expectedSphincs); err == nil {
		wrong.Close()
		t.Fatal("tampered aggregate bytes must be rejected")
	}
	if wrong, err := AggregateFromBytes(nil, expectedXmss, expectedSphincs); err == nil {
		wrong.Close()
		t.Fatal("empty aggregate bytes must be rejected")
	}
}

func TestConcurrentNativeErrors(t *testing.T) {
	// Ensure at least 2 OS threads for concurrent testing.
	if old := runtime.GOMAXPROCS(0); old < 2 {
		runtime.GOMAXPROCS(2)
		defer runtime.GOMAXPROCS(old)
	}

	if err := Setup(); err != nil {
		t.Fatal(err)
	}

	var workers sync.WaitGroup
	start := make(chan struct{})
	for range 4 * runtime.NumCPU() {
		workers.Add(1)
		go func() {
			defer workers.Done()
			<-start
			for range 10000 {
				key, err := XmssSecretKeyFromBytes([]byte{1})
				key.Close()
				if want := "leanpq: leanXMSS secret key must be 32 bytes, got 1"; err == nil || err.Error() != want {
					t.Errorf("XmssSecretKeyFromBytes error = %v, want %q", err, want)
					return
				}
				aggregate, err := AggregateFromBytes([]byte{1, 2, 3}, nil, nil)
				aggregate.Close()
				if want := "leanpq: malformed aggregate: the bytes are not a leanVM aggregate proof"; err == nil || err.Error() != want {
					t.Errorf("AggregateFromBytes error = %v, want %q", err, want)
					return
				}
				if err := Setup(); err != nil {
					t.Errorf("Setup: %v", err)
					return
				}
			}
		}()
	}
	close(start)
	workers.Wait()
}

func mustXmssKey(t *testing.T, seed [32]byte) *XmssSecretKey {
	t.Helper()
	key, err := XmssSecretKeyFromSeed(seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(key.Close)
	return key
}

func mustSphincsKey(t *testing.T, seed [32]byte) *SphincsSecretKey {
	t.Helper()
	key, err := SphincsSecretKeyFromSeed(seed)
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(key.Close)
	return key
}

func mustXmssPublicKey(t *testing.T, key *XmssSecretKey) [32]byte {
	t.Helper()
	publicKey, err := key.PublicKey()
	if err != nil {
		t.Fatal(err)
	}
	return publicKey
}

func mustSphincsPublicKey(t *testing.T, key *SphincsSecretKey) [32]byte {
	t.Helper()
	publicKey, err := key.PublicKey()
	if err != nil {
		t.Fatal(err)
	}
	return publicKey
}

func bytes32(value byte) [32]byte {
	var result [32]byte
	for index := range result {
		result[index] = value
	}
	return result
}
