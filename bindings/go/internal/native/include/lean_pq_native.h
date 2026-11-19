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
 */
#ifndef LEAN_PQ_NATIVE_H
#define LEAN_PQ_NATIVE_H

#include <stddef.h>
#include <stdint.h>

typedef struct { uint8_t *data; size_t len; } lpq_buffer;
typedef struct lpq_xmss_secret_key lpq_xmss_secret_key;
typedef struct lpq_sphincs_secret_key lpq_sphincs_secret_key;
typedef struct lpq_aggregate lpq_aggregate;

/* Returns 0 on success, 1 for a checked error, and 2 when Rust caught a panic. */
int32_t lpq_setup(void);
int32_t lpq_last_error(lpq_buffer *out);
void lpq_buffer_free(uint8_t *data, size_t len);

int32_t lpq_xmss_secret_key_generate(lpq_xmss_secret_key **out);
int32_t lpq_xmss_secret_key_from_bytes(const uint8_t *data, size_t len, lpq_xmss_secret_key **out);
int32_t lpq_xmss_secret_key_to_bytes(lpq_xmss_secret_key *key, lpq_buffer *out);
/*
 * The trees a key holds, without any secret, and a key loaded from its seed and those bytes in
 * place of building the trees. The cache is not checked: a wrong one gives invalid signatures.
 * Mostly useful for testing.
 */
int32_t lpq_xmss_secret_key_cache_to_bytes(lpq_xmss_secret_key *key, lpq_buffer *out);
int32_t lpq_xmss_secret_key_from_cache_bytes(const uint8_t *seed, size_t seed_len, const uint8_t *cache, size_t cache_len, lpq_xmss_secret_key **out);
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
 * Decodes a proof and verifies that it proves exactly these claims, given as concatenated 64-byte
 * public key (32) | message (32) records in any order; a repeated claim counts once. A returned
 * handle is always a verified aggregate.
 */
int32_t lpq_aggregate_from_bytes(const uint8_t *data, size_t len, const uint8_t *xmss_claims, size_t xmss_count, const uint8_t *sphincs_claims, size_t sphincs_count, lpq_aggregate **out);
/* The proof alone, without its claims. */
int32_t lpq_aggregate_to_bytes(lpq_aggregate *aggregate, lpq_buffer *out);
/* Claims are concatenated 64-byte public key (32) | message (32) records, strictly sorted. */
int32_t lpq_aggregate_xmss_claims(lpq_aggregate *aggregate, lpq_buffer *out);
int32_t lpq_aggregate_sphincs_claims(lpq_aggregate *aggregate, lpq_buffer *out);
void lpq_aggregate_destroy(lpq_aggregate *aggregate);

#endif
