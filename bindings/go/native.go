//go:build cgo

// Package leanpq provides Go bindings for leanXMSS and leanSPHINCS signatures, their recursive
// aggregation, and the consensus VRF.
package leanpq

// #cgo CFLAGS: -I${SRCDIR}/internal/native/include
// #include "lean_pq_native.h"
import "C"

import (
	"errors"
	"fmt"
	"runtime"
	"sort"
	"sync"
	"unsafe"
)

const (
	statusOK = C.int32_t(0)

	keyLen            = len(Claim{}.PublicKey)
	claimRecordLen    = keyLen + len(Claim{}.Message)
	xmssRecordLen     = claimRecordLen + len(XmssSignature{})
	sphincsRecordLen  = claimRecordLen + len(SphincsSignature{})
	maxBufferLen      = 1<<31 - 1
	nativeErrorFormat = "leanpq: native operation failed with status %d"
)

// XmssSignature is an encoded leanXMSS signature.
type XmssSignature [2404]byte

// SphincsSignature is an encoded leanSPHINCS signature.
type SphincsSignature [7740]byte

// VrfProof is a VRF proof: the secret of a slot, then its leaf's 31 siblings, bottom-up.
type VrfProof [1024]byte

// XmssSignedMessage is a leanXMSS signature over Message by PublicKey, as input to aggregation.
type XmssSignedMessage struct {
	PublicKey [32]byte
	Message   [32]byte
	Signature XmssSignature
}

// SphincsSignedMessage is a leanSPHINCS signature over Message by PublicKey, as input to aggregation.
type SphincsSignedMessage struct {
	PublicKey [32]byte
	Message   [32]byte
	Signature SphincsSignature
}

// Claim states that PublicKey signed Message.
type Claim struct {
	PublicKey [32]byte
	Message   [32]byte
}

// XmssSecretKey owns a stateful leanXMSS secret key in the native bridge. Never sign two different
// messages at the same leaf index. Call Close when finished.
type XmssSecretKey struct {
	mu     sync.Mutex
	handle *C.lpq_xmss_secret_key
}

// SphincsSecretKey owns a stateless leanSPHINCS secret key in the native bridge. Call Close when
// finished.
type SphincsSecretKey struct {
	mu     sync.Mutex
	handle *C.lpq_sphincs_secret_key
}

// VrfKey is a VRF key: a seed and its range of slots, which fix the root, so keep both. Call
// Close when finished.
type VrfKey struct {
	mu     sync.Mutex
	handle *C.lpq_vrf_key
}

// Aggregate owns a verified recursive proof that each of its claims was signed. Call Close when
// finished.
type Aggregate struct {
	mu     sync.Mutex
	handle *C.lpq_aggregate
}

// Setup starts the prover on threads threads (0: one per core). It fails if the prover already
// runs with another count.
func Setup(threads int) error {
	if threads < 0 {
		return errors.New("leanpq: threads must not be negative")
	}
	return call(func() C.int32_t { return C.lpq_setup(C.size_t(threads)) })
}

// GenerateXmssSecretKey creates a random leanXMSS key.
func GenerateXmssSecretKey() (*XmssSecretKey, error) {
	var handle *C.lpq_xmss_secret_key
	if err := call(func() C.int32_t { return C.lpq_xmss_secret_key_generate(&handle) }); err != nil {
		return nil, err
	}
	return &XmssSecretKey{handle: handle}, nil
}

// XmssSecretKeyFromSeed deterministically creates a leanXMSS key from seed.
func XmssSecretKeyFromSeed(seed [32]byte) (*XmssSecretKey, error) {
	return XmssSecretKeyFromBytes(seed[:])
}

// XmssSecretKeyFromBytes restores a leanXMSS key from the bytes returned by Bytes.
func XmssSecretKeyFromBytes(bytes []byte) (*XmssSecretKey, error) {
	var handle *C.lpq_xmss_secret_key
	if err := call(func() C.int32_t {
		return C.lpq_xmss_secret_key_from_bytes(bytesPointer(bytes), C.size_t(len(bytes)), &handle)
	}); err != nil {
		return nil, err
	}
	return &XmssSecretKey{handle: handle}, nil
}

// XmssSecretKeyFromCacheBytes loads a leanXMSS key from its seed, its public key and the bytes
// returned by CacheBytes, building no tree. The cache is checked against the public key.
func XmssSecretKeyFromCacheBytes(seed, publicKey [32]byte, cache []byte) (*XmssSecretKey, error) {
	var handle *C.lpq_xmss_secret_key
	if err := call(func() C.int32_t {
		return C.lpq_xmss_secret_key_from_cache_bytes(
			arrayPointer(&seed), C.size_t(len(seed)),
			arrayPointer(&publicKey), C.size_t(len(publicKey)),
			bytesPointer(cache), C.size_t(len(cache)),
			&handle,
		)
	}); err != nil {
		return nil, err
	}
	return &XmssSecretKey{handle: handle}, nil
}

// Bytes returns the key's secret encoding (its 32-byte seed).
func (key *XmssSecretKey) Bytes() ([]byte, error) {
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return nil, errClosed("leanXMSS secret key")
	}
	return bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_xmss_secret_key_to_bytes(key.handle, output)
	})
}

// CacheBytes returns the trees the key holds, without any secret.
func (key *XmssSecretKey) CacheBytes() ([]byte, error) {
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return nil, errClosed("leanXMSS secret key")
	}
	return bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_xmss_secret_key_cache_to_bytes(key.handle, output)
	})
}

// PublicKey returns the key's 32-byte public key.
func (key *XmssSecretKey) PublicKey() ([32]byte, error) {
	var publicKey [32]byte
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return publicKey, errClosed("leanXMSS secret key")
	}
	err := fixedResult(publicKey[:], "public key", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_xmss_secret_key_public_key(key.handle, output)
	})
	return publicKey, err
}

// Prepare precomputes key material for signing at leafIndex.
func (key *XmssSecretKey) Prepare(leafIndex uint32) error {
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return errClosed("leanXMSS secret key")
	}
	return call(func() C.int32_t {
		return C.lpq_xmss_secret_key_prepare(key.handle, C.uint32_t(leafIndex))
	})
}

// Sign signs message at leafIndex.
func (key *XmssSecretKey) Sign(message [32]byte, leafIndex uint32) (XmssSignature, error) {
	var signature XmssSignature
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return signature, errClosed("leanXMSS secret key")
	}
	err := fixedResult(signature[:], "leanXMSS signature", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_xmss_secret_key_sign(key.handle, arrayPointer(&message), C.size_t(len(message)), C.uint32_t(leafIndex), output)
	})
	return signature, err
}

// Close releases the native key. It is safe to call repeatedly.
func (key *XmssSecretKey) Close() {
	if key == nil {
		return
	}
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle != nil {
		C.lpq_xmss_secret_key_destroy(key.handle)
		key.handle = nil
	}
}

// XmssVerify returns nil when signature is a valid leanXMSS signature over message by publicKey.
func XmssVerify(publicKey, message [32]byte, signature XmssSignature) error {
	return call(func() C.int32_t {
		return C.lpq_xmss_verify(
			arrayPointer(&publicKey), C.size_t(len(publicKey)),
			arrayPointer(&message), C.size_t(len(message)),
			(*C.uint8_t)(unsafe.Pointer(&signature[0])), C.size_t(len(signature)),
		)
	})
}

// GenerateSphincsSecretKey creates a random leanSPHINCS key.
func GenerateSphincsSecretKey() (*SphincsSecretKey, error) {
	var handle *C.lpq_sphincs_secret_key
	if err := call(func() C.int32_t { return C.lpq_sphincs_secret_key_generate(&handle) }); err != nil {
		return nil, err
	}
	return &SphincsSecretKey{handle: handle}, nil
}

// SphincsSecretKeyFromSeed deterministically creates a leanSPHINCS key from seed.
func SphincsSecretKeyFromSeed(seed [32]byte) (*SphincsSecretKey, error) {
	var handle *C.lpq_sphincs_secret_key
	if err := call(func() C.int32_t {
		return C.lpq_sphincs_secret_key_from_seed(arrayPointer(&seed), C.size_t(len(seed)), &handle)
	}); err != nil {
		return nil, err
	}
	return &SphincsSecretKey{handle: handle}, nil
}

// SphincsSecretKeyFromBytes restores a leanSPHINCS key from the bytes returned by Bytes.
func SphincsSecretKeyFromBytes(bytes []byte) (*SphincsSecretKey, error) {
	var handle *C.lpq_sphincs_secret_key
	if err := call(func() C.int32_t {
		return C.lpq_sphincs_secret_key_from_bytes(bytesPointer(bytes), C.size_t(len(bytes)), &handle)
	}); err != nil {
		return nil, err
	}
	return &SphincsSecretKey{handle: handle}, nil
}

// Bytes returns the key's secret encoding (its 32-byte seed).
func (key *SphincsSecretKey) Bytes() ([]byte, error) {
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return nil, errClosed("leanSPHINCS secret key")
	}
	return bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_sphincs_secret_key_to_bytes(key.handle, output)
	})
}

// PublicKey returns the key's 32-byte public key.
func (key *SphincsSecretKey) PublicKey() ([32]byte, error) {
	var publicKey [32]byte
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return publicKey, errClosed("leanSPHINCS secret key")
	}
	err := fixedResult(publicKey[:], "public key", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_sphincs_secret_key_public_key(key.handle, output)
	})
	return publicKey, err
}

// Sign signs message.
func (key *SphincsSecretKey) Sign(message [32]byte) (SphincsSignature, error) {
	var signature SphincsSignature
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return signature, errClosed("leanSPHINCS secret key")
	}
	err := fixedResult(signature[:], "leanSPHINCS signature", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_sphincs_secret_key_sign(key.handle, arrayPointer(&message), C.size_t(len(message)), output)
	})
	return signature, err
}

// Close releases the native key. It is safe to call repeatedly.
func (key *SphincsSecretKey) Close() {
	if key == nil {
		return
	}
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle != nil {
		C.lpq_sphincs_secret_key_destroy(key.handle)
		key.handle = nil
	}
}

// SphincsVerify returns nil when signature is a valid leanSPHINCS signature over message by
// publicKey.
func SphincsVerify(publicKey, message [32]byte, signature SphincsSignature) error {
	return call(func() C.int32_t {
		return C.lpq_sphincs_verify(
			arrayPointer(&publicKey), C.size_t(len(publicKey)),
			arrayPointer(&message), C.size_t(len(message)),
			(*C.uint8_t)(unsafe.Pointer(&signature[0])), C.size_t(len(signature)),
		)
	})
}

// VrfKeyFromSeed builds the key of the slots [start, end), hashing every slot of the range. It
// fails if the range is empty or ends past 2^31.
func VrfKeyFromSeed(seed [32]byte, start, end uint32) (*VrfKey, error) {
	var handle *C.lpq_vrf_key
	if err := call(func() C.int32_t {
		return C.lpq_vrf_key_new(arrayPointer(&seed), C.size_t(len(seed)), C.uint32_t(start), C.uint32_t(end), &handle)
	}); err != nil {
		return nil, err
	}
	return &VrfKey{handle: handle}, nil
}

// VrfKeyFromCacheBytes rebuilds a key from its seed, its root and a cache from CacheBytes, without
// hashing the range. It fails if the cache is malformed or does not lead to root.
func VrfKeyFromCacheBytes(seed, root [32]byte, cache []byte) (*VrfKey, error) {
	var handle *C.lpq_vrf_key
	if err := call(func() C.int32_t {
		return C.lpq_vrf_key_from_cache_bytes(arrayPointer(&seed), C.size_t(len(seed)), arrayPointer(&root), C.size_t(len(root)), bytesPointer(cache), C.size_t(len(cache)), &handle)
	}); err != nil {
		return nil, err
	}
	return &VrfKey{handle: handle}, nil
}

// CacheBytes encodes the key's cache: its range and cached layer, no secret.
func (key *VrfKey) CacheBytes() ([]byte, error) {
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return nil, errClosed("VRF key")
	}
	return bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_vrf_key_cache_to_bytes(key.handle, output)
	})
}

// Root returns the root, which the validator registers.
func (key *VrfKey) Root() ([32]byte, error) {
	var root [32]byte
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return root, errClosed("VRF key")
	}
	err := fixedResult(root[:], "VRF root", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_vrf_key_root(key.handle, output)
	})
	return root, err
}

// Proof returns the proof of slot. It fails outside the range.
func (key *VrfKey) Proof(slot uint32) (VrfProof, error) {
	var proof VrfProof
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle == nil {
		return proof, errClosed("VRF key")
	}
	err := fixedResult(proof[:], "VRF proof", func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_vrf_key_proof(key.handle, C.uint32_t(slot), output)
	})
	return proof, err
}

// Close releases the native key. It is safe to call repeatedly.
func (key *VrfKey) Close() {
	if key == nil {
		return
	}
	key.mu.Lock()
	defer key.mu.Unlock()
	if key.handle != nil {
		C.lpq_vrf_key_destroy(key.handle)
		key.handle = nil
	}
}

// VrfVerify returns nil if proof opens slot under root, as is_valid_vrf_proof in the consensus
// specifications.
func VrfVerify(root [32]byte, slot uint64, proof VrfProof) error {
	return call(func() C.int32_t {
		return C.lpq_vrf_verify(
			arrayPointer(&root), C.size_t(len(root)),
			C.uint64_t(slot),
			(*C.uint8_t)(unsafe.Pointer(&proof[0])), C.size_t(len(proof)),
		)
	})
}

// AggregateSignatures proves the union of the children's claims and the raw signatures' claims.
// Raw signatures are verified first; children are neither consumed nor closed. At least one input
// is required, and at most 16 children.
func AggregateSignatures(children []*Aggregate, xmss []XmssSignedMessage, sphincs []SphincsSignedMessage) (*Aggregate, error) {
	return aggregateSignatures(children, xmss, sphincs, nil, nil, false)
}

// AggregateSignaturesOnly is AggregateSignatures, but the result proves exactly the given claims,
// in any order, a repeat counting once; each must be one the inputs cover.
func AggregateSignaturesOnly(children []*Aggregate, xmss []XmssSignedMessage, sphincs []SphincsSignedMessage, xmssClaims, sphincsClaims []Claim) (*Aggregate, error) {
	return aggregateSignatures(children, xmss, sphincs, xmssClaims, sphincsClaims, true)
}

func aggregateSignatures(children []*Aggregate, xmss []XmssSignedMessage, sphincs []SphincsSignedMessage, xmssClaims, sphincsClaims []Claim, only bool) (*Aggregate, error) {
	handles, release, err := acquireAggregates(children)
	if err != nil {
		return nil, err
	}
	defer release()
	xmssRecords := make([]byte, 0, len(xmss)*xmssRecordLen)
	for index := range xmss {
		xmssRecords = append(xmssRecords, xmss[index].PublicKey[:]...)
		xmssRecords = append(xmssRecords, xmss[index].Message[:]...)
		xmssRecords = append(xmssRecords, xmss[index].Signature[:]...)
	}
	sphincsRecords := make([]byte, 0, len(sphincs)*sphincsRecordLen)
	for index := range sphincs {
		sphincsRecords = append(sphincsRecords, sphincs[index].PublicKey[:]...)
		sphincsRecords = append(sphincsRecords, sphincs[index].Message[:]...)
		sphincsRecords = append(sphincsRecords, sphincs[index].Signature[:]...)
	}
	xmssClaimRecords := claimRecords(xmssClaims)
	sphincsClaimRecords := claimRecords(sphincsClaims)
	var output *C.lpq_aggregate
	if err := call(func() C.int32_t {
		if only {
			return C.lpq_aggregate_create_only(
				aggregatePointer(handles), C.size_t(len(handles)),
				bytesPointer(xmssRecords), C.size_t(len(xmss)),
				bytesPointer(sphincsRecords), C.size_t(len(sphincs)),
				bytesPointer(xmssClaimRecords), C.size_t(len(xmssClaims)),
				bytesPointer(sphincsClaimRecords), C.size_t(len(sphincsClaims)),
				&output,
			)
		}
		return C.lpq_aggregate_create(
			aggregatePointer(handles), C.size_t(len(handles)),
			bytesPointer(xmssRecords), C.size_t(len(xmss)),
			bytesPointer(sphincsRecords), C.size_t(len(sphincs)),
			&output,
		)
	}); err != nil {
		return nil, err
	}
	return &Aggregate{handle: output}, nil
}

// AggregateFromBytes checks that bytes, from Aggregate.Bytes, prove exactly the given claims, which
// may be in any order; a repeated claim counts once. The encoding is the proof alone: send the claims
// alongside it or have the receiver rebuild them. Any other claim set is rejected.
func AggregateFromBytes(bytes []byte, xmssClaims, sphincsClaims []Claim) (*Aggregate, error) {
	xmssRecords := claimRecords(xmssClaims)
	sphincsRecords := claimRecords(sphincsClaims)
	var handle *C.lpq_aggregate
	if err := call(func() C.int32_t {
		return C.lpq_aggregate_from_bytes(
			bytesPointer(bytes), C.size_t(len(bytes)),
			bytesPointer(xmssRecords), C.size_t(len(xmssClaims)),
			bytesPointer(sphincsRecords), C.size_t(len(sphincsClaims)),
			&handle,
		)
	}); err != nil {
		return nil, err
	}
	return &Aggregate{handle: handle}, nil
}

// Bytes returns the aggregate's proof encoding, without its claims.
func (aggregate *Aggregate) Bytes() ([]byte, error) {
	handle, release, err := aggregate.acquire()
	if err != nil {
		return nil, err
	}
	defer release()
	return bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return C.lpq_aggregate_to_bytes(handle, output)
	})
}

// XmssClaims returns the leanXMSS claims the aggregate proves, strictly sorted.
func (aggregate *Aggregate) XmssClaims() ([]Claim, error) {
	return aggregate.claims(func(handle *C.lpq_aggregate, output *C.lpq_buffer) C.int32_t {
		return C.lpq_aggregate_xmss_claims(handle, output)
	})
}

// SphincsClaims returns the leanSPHINCS claims the aggregate proves, strictly sorted.
func (aggregate *Aggregate) SphincsClaims() ([]Claim, error) {
	return aggregate.claims(func(handle *C.lpq_aggregate, output *C.lpq_buffer) C.int32_t {
		return C.lpq_aggregate_sphincs_claims(handle, output)
	})
}

// Close releases the native aggregate. It is safe to call repeatedly.
func (aggregate *Aggregate) Close() {
	if aggregate == nil {
		return
	}
	aggregate.mu.Lock()
	defer aggregate.mu.Unlock()
	if aggregate.handle != nil {
		C.lpq_aggregate_destroy(aggregate.handle)
		aggregate.handle = nil
	}
}

func (aggregate *Aggregate) claims(f func(*C.lpq_aggregate, *C.lpq_buffer) C.int32_t) ([]Claim, error) {
	handle, release, err := aggregate.acquire()
	if err != nil {
		return nil, err
	}
	defer release()
	encoded, err := bufferResult(func(output *C.lpq_buffer) C.int32_t {
		return f(handle, output)
	})
	if err != nil {
		return nil, err
	}
	if len(encoded)%claimRecordLen != 0 {
		return nil, fmt.Errorf("leanpq: native claim data is not a multiple of %d bytes", claimRecordLen)
	}
	claims := make([]Claim, len(encoded)/claimRecordLen)
	for index := range claims {
		record := encoded[index*claimRecordLen:]
		copy(claims[index].PublicKey[:], record[:keyLen])
		copy(claims[index].Message[:], record[keyLen:claimRecordLen])
	}
	return claims, nil
}

// claimRecords packs claims into the native bridge's 64-byte public key | message records.
func claimRecords(claims []Claim) []byte {
	records := make([]byte, 0, len(claims)*claimRecordLen)
	for index := range claims {
		records = append(records, claims[index].PublicKey[:]...)
		records = append(records, claims[index].Message[:]...)
	}
	return records
}

func (aggregate *Aggregate) acquire() (*C.lpq_aggregate, func(), error) {
	if aggregate == nil {
		return nil, nil, errors.New("leanpq: aggregate is nil")
	}
	aggregate.mu.Lock()
	if aggregate.handle == nil {
		aggregate.mu.Unlock()
		return nil, nil, errClosed("aggregate")
	}
	return aggregate.handle, aggregate.mu.Unlock, nil
}

// acquireAggregates locks each distinct aggregate in address order so concurrent calls sharing
// children cannot deadlock.
func acquireAggregates(aggregates []*Aggregate) ([]*C.lpq_aggregate, func(), error) {
	unique := make(map[*Aggregate]struct{}, len(aggregates))
	ordered := make([]*Aggregate, 0, len(aggregates))
	for _, aggregate := range aggregates {
		if aggregate == nil {
			return nil, nil, errors.New("leanpq: aggregate is nil")
		}
		if _, exists := unique[aggregate]; !exists {
			unique[aggregate] = struct{}{}
			ordered = append(ordered, aggregate)
		}
	}
	sort.Slice(ordered, func(left, right int) bool {
		return uintptr(unsafe.Pointer(ordered[left])) < uintptr(unsafe.Pointer(ordered[right]))
	})
	release := func() {
		for index := len(ordered) - 1; index >= 0; index-- {
			ordered[index].mu.Unlock()
		}
	}
	for _, aggregate := range ordered {
		aggregate.mu.Lock()
	}
	for _, aggregate := range ordered {
		if aggregate.handle == nil {
			release()
			return nil, nil, errClosed("aggregate")
		}
	}
	handles := make([]*C.lpq_aggregate, len(aggregates))
	for index, aggregate := range aggregates {
		handles[index] = aggregate.handle
	}
	return handles, release, nil
}

func call(f func() C.int32_t) error {
	// The native error message belongs to the OS thread that made the call.
	runtime.LockOSThread()
	defer runtime.UnlockOSThread()

	if status := f(); status != statusOK {
		return nativeError(status)
	}
	return nil
}

func nativeError(status C.int32_t) error {
	var buffer C.lpq_buffer
	if C.lpq_last_error(&buffer) != statusOK {
		return fmt.Errorf(nativeErrorFormat, status)
	}
	message, err := takeBuffer(&buffer)
	if err != nil || len(message) == 0 {
		return fmt.Errorf(nativeErrorFormat, status)
	}
	return fmt.Errorf("leanpq: %s", message)
}

func bufferResult(f func(*C.lpq_buffer) C.int32_t) ([]byte, error) {
	var buffer C.lpq_buffer
	if err := call(func() C.int32_t { return f(&buffer) }); err != nil {
		return nil, err
	}
	return takeBuffer(&buffer)
}

// fixedResult copies a native buffer of exactly len(destination) bytes into destination.
func fixedResult(destination []byte, kind string, f func(*C.lpq_buffer) C.int32_t) error {
	var buffer C.lpq_buffer
	if err := call(func() C.int32_t { return f(&buffer) }); err != nil {
		return err
	}
	defer C.lpq_buffer_free(buffer.data, buffer.len)
	if int(buffer.len) != len(destination) {
		return fmt.Errorf("leanpq: native %s has %d bytes", kind, buffer.len)
	}
	copy(destination, unsafe.Slice((*byte)(unsafe.Pointer(buffer.data)), len(destination)))
	return nil
}

func takeBuffer(buffer *C.lpq_buffer) ([]byte, error) {
	defer C.lpq_buffer_free(buffer.data, buffer.len)
	if uint64(buffer.len) > maxBufferLen {
		return nil, errors.New("leanpq: native buffer is too large")
	}
	if buffer.len == 0 {
		return []byte{}, nil
	}
	return C.GoBytes(unsafe.Pointer(buffer.data), C.int(buffer.len)), nil
}

func arrayPointer(bytes *[32]byte) *C.uint8_t {
	return (*C.uint8_t)(unsafe.Pointer(&bytes[0]))
}

func bytesPointer(bytes []byte) *C.uint8_t {
	if len(bytes) == 0 {
		return nil
	}
	return (*C.uint8_t)(unsafe.Pointer(unsafe.SliceData(bytes)))
}

func aggregatePointer(handles []*C.lpq_aggregate) **C.lpq_aggregate {
	if len(handles) == 0 {
		return nil
	}
	return (**C.lpq_aggregate)(unsafe.Pointer(unsafe.SliceData(handles)))
}

func errClosed(kind string) error {
	return fmt.Errorf("leanpq: %s is closed", kind)
}
