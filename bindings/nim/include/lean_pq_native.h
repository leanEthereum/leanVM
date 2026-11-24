/*
 * Internal ABI between managed-language wrappers and the Rust implementation.
 *
 * It is not a supported public C API. Every non-empty input range must point to readable
 * memory. Every output pointer must be writable.
 * Handles are opaque and must be destroyed exactly once with their matching destroy function.
 * Buffers returned through lpq_buffer must be released with lpq_buffer_free exactly once.
 *
 * Public keys and messages are 32 bytes. Secret keys in both schemes are their 32-byte seed.
 * leanXMSS signatures are 2404 bytes and leanSPHINCS signatures are 7740 bytes.
 *
 * A VRF key is a 32-byte seed and slots [start, end), end <= 2^31. VRF roots are 32 bytes and
 * proofs 1024: the slot's secret, then its leaf's 31 siblings.
 */
#ifndef LEAN_PQ_NATIVE_H
#define LEAN_PQ_NATIVE_H

#include <stddef.h>
#include <stdint.h>

typedef struct { uint8_t *data; size_t len; } lpq_buffer;
typedef struct lpq_xmss_secret_key lpq_xmss_secret_key;
typedef struct lpq_sphincs_secret_key lpq_sphincs_secret_key;
typedef struct lpq_aggregate lpq_aggregate;
typedef struct lpq_vrf_key lpq_vrf_key;

/* Returns 0 on success, 1 for a checked error, and 2 when Rust caught a panic. */
int32_t lpq_last_error(lpq_buffer *out);
void lpq_buffer_free(uint8_t *data, size_t len);

/*
 * Starts the prover with threads threads (0: one per core). Fails above the machine's parallelism,
 * if it runs with another count, or in a process forked after it started.
 */
int32_t lpq_setup(size_t threads);

int32_t lpq_xmss_secret_key_generate(lpq_xmss_secret_key **out);
int32_t lpq_xmss_secret_key_from_bytes(const uint8_t *data, size_t len, lpq_xmss_secret_key **out);
int32_t lpq_xmss_secret_key_to_bytes(lpq_xmss_secret_key *key, lpq_buffer *out);
/*
 * The trees a key holds, without any secret, and a key loaded from its seed, its 32-byte public
 * key and those bytes in place of building the trees. Loading checks the cache against the public
 * key, and fails for any bytes that are not this key's cache.
 */
int32_t lpq_xmss_secret_key_cache_to_bytes(lpq_xmss_secret_key *key, lpq_buffer *out);
int32_t lpq_xmss_secret_key_from_cache_bytes(const uint8_t *seed, size_t seed_len, const uint8_t *public_key, size_t public_key_len, const uint8_t *cache, size_t cache_len, lpq_xmss_secret_key **out);
int32_t lpq_xmss_secret_key_public_key(lpq_xmss_secret_key *key, lpq_buffer *out);
int32_t lpq_xmss_secret_key_prepare(lpq_xmss_secret_key *key, uint32_t leaf_index);
int32_t lpq_xmss_secret_key_sign(lpq_xmss_secret_key *key, const uint8_t *message, size_t message_len, uint32_t leaf_index, lpq_buffer *out);
void lpq_xmss_secret_key_destroy(lpq_xmss_secret_key *key);
/* Returns 0 when the signature verifies and 1, with lpq_last_error set, when it does not. */
int32_t lpq_xmss_verify(const uint8_t *public_key, size_t public_key_len, const uint8_t *message, size_t message_len, const uint8_t *signature, size_t signature_len);

int32_t lpq_sphincs_secret_key_generate(lpq_sphincs_secret_key **out);
int32_t lpq_sphincs_secret_key_from_seed(const uint8_t *seed, size_t seed_len, lpq_sphincs_secret_key **out);
int32_t lpq_sphincs_secret_key_from_bytes(const uint8_t *data, size_t len, lpq_sphincs_secret_key **out);
int32_t lpq_sphincs_secret_key_to_bytes(lpq_sphincs_secret_key *key, lpq_buffer *out);
int32_t lpq_sphincs_secret_key_public_key(lpq_sphincs_secret_key *key, lpq_buffer *out);
int32_t lpq_sphincs_secret_key_sign(lpq_sphincs_secret_key *key, const uint8_t *message, size_t message_len, lpq_buffer *out);
void lpq_sphincs_secret_key_destroy(lpq_sphincs_secret_key *key);
/* Returns 0 when the signature verifies and 1, with lpq_last_error set, when it does not. */
int32_t lpq_sphincs_verify(const uint8_t *public_key, size_t public_key_len, const uint8_t *message, size_t message_len, const uint8_t *signature, size_t signature_len);

/*
 * Raw signatures are concatenated fixed-width records of public key (32) | message (32) |
 * signature: 2468-byte records for leanXMSS and 7804-byte records for leanSPHINCS. Children are
 * at most 16 aggregates; the call neither consumes nor retains them.
 */
int32_t lpq_aggregate_create(lpq_aggregate *const *children, size_t child_count, const uint8_t *xmss, size_t xmss_count, const uint8_t *sphincs, size_t sphincs_count, lpq_aggregate **out);
/*
 * lpq_aggregate_create, but the result proves exactly these claims, given as lpq_aggregate_from_bytes
 * takes them; each must be one the inputs cover.
 */
int32_t lpq_aggregate_create_only(lpq_aggregate *const *children, size_t child_count, const uint8_t *xmss, size_t xmss_count, const uint8_t *sphincs, size_t sphincs_count, const uint8_t *xmss_claims, size_t xmss_claim_count, const uint8_t *sphincs_claims, size_t sphincs_claim_count, lpq_aggregate **out);
/*
 * Verifies that a proof proves exactly these claims, given as concatenated 64-byte public key (32)
 * | message (32) records in any order; a repeated claim counts once. A returned handle is always a
 * verified aggregate.
 */
int32_t lpq_aggregate_from_bytes(const uint8_t *data, size_t len, const uint8_t *xmss_claims, size_t xmss_count, const uint8_t *sphincs_claims, size_t sphincs_count, lpq_aggregate **out);
/* The proof alone, without its claims. */
int32_t lpq_aggregate_to_bytes(lpq_aggregate *aggregate, lpq_buffer *out);
/* Claims are concatenated 64-byte public key (32) | message (32) records, strictly sorted. */
int32_t lpq_aggregate_xmss_claims(lpq_aggregate *aggregate, lpq_buffer *out);
int32_t lpq_aggregate_sphincs_claims(lpq_aggregate *aggregate, lpq_buffer *out);
void lpq_aggregate_destroy(lpq_aggregate *aggregate);

/* Hashes every slot of the range. */
int32_t lpq_vrf_key_new(const uint8_t *seed, size_t seed_len, uint32_t start, uint32_t end, lpq_vrf_key **out);
/* Rebuilds a key from its seed and a cache from lpq_vrf_key_cache_to_bytes. Fails if the cache does not lead to root. */
int32_t lpq_vrf_key_from_cache_bytes(const uint8_t *seed, size_t seed_len, const uint8_t *root, size_t root_len, const uint8_t *cache, size_t cache_len, lpq_vrf_key **out);
/* Encodes the key's cache: its range and cached layer, no secret. */
int32_t lpq_vrf_key_cache_to_bytes(lpq_vrf_key *key, lpq_buffer *out);
int32_t lpq_vrf_key_root(lpq_vrf_key *key, lpq_buffer *out);
/* Fails for a slot outside the range. */
int32_t lpq_vrf_key_proof(lpq_vrf_key *key, uint32_t slot, lpq_buffer *out);
void lpq_vrf_key_destroy(lpq_vrf_key *key);
/* Returns 0 when the proof opens and 1, with lpq_last_error set, when not. */
int32_t lpq_vrf_verify(const uint8_t *root, size_t root_len, uint64_t slot, const uint8_t *proof, size_t proof_len);

#endif
