from snark_lib import *

DIM = 5
DIGEST_LEN = 8
N = N_PLACEHOLDER
M = M_PLACEHOLDER
K = K_PLACEHOLDER
C = C_PLACEHOLDER
N_CELLS = N_CELLS_PLACEHOLDER
SYSTEMATIC_STRIDE = SYSTEMATIC_STRIDE_PLACEHOLDER
ROW_CHUNKS = ROW_CHUNKS_PLACEHOLDER
COLUMN_CHUNKS = COLUMN_CHUNKS_PLACEHOLDER
MERKLE_DEPTH = MERKLE_DEPTH_PLACEHOLDER
TREE_DIGESTS = TREE_DIGESTS_PLACEHOLDER
LEVEL_SIZES = LEVEL_SIZES_PLACEHOLDER
LEVEL_OFFSETS = LEVEL_OFFSETS_PLACEHOLDER

PUBLIC_ROW_HASHES_PTR = PUBLIC_ROW_HASHES_PTR_PLACEHOLDER
PUBLIC_ROOT_PTR = PUBLIC_ROOT_PTR_PLACEHOLDER
CHECK_VECTOR_PTR = CHECK_VECTOR_PTR_PLACEHOLDER


@inline
# Constrains one extension element to be zero in all five coordinates.
def assert_ext_zero(a):
    for i in unroll(0, DIM):
        assert a[i] == 0
    return


# Poseidon-hashes complete rate-eight blocks with a compact runtime loop.
def hash_chunks(data, num_chunks: Const):
    iv = Array(DIGEST_LEN)
    iv[0] = num_chunks * DIGEST_LEN
    for i in unroll(1, DIGEST_LEN):
        iv[i] = 0

    full = Array(2 * DIGEST_LEN)
    if num_chunks == 1:
        poseidon16_permute(iv, data, full)
    else:
        states = Array((num_chunks - 1) * DIGEST_LEN)
        poseidon16_permute_half(iv, data, states)
        for chunk in range(1, num_chunks - 1):
            poseidon16_permute_half(
                states + (chunk - 1) * DIGEST_LEN,
                data + chunk * DIGEST_LEN,
                states + chunk * DIGEST_LEN,
            )
        poseidon16_permute(
            states + (num_chunks - 2) * DIGEST_LEN,
            data + (num_chunks - 1) * DIGEST_LEN,
            full,
        )
    return full + DIGEST_LEN


# Checks only the construction's row hashes, column Merkle root, and RS identities.
def main():
    codewords = Array(N * M)
    hint_witness("codewords", codewords)
    public_row_hashes = PUBLIC_ROW_HASHES_PTR
    public_root = PUBLIC_ROOT_PTR
    check_vector = CHECK_VECTOR_PTR

    for row in range(0, N):
        systematic = Array(K)
        for i in range(0, K):
            systematic[i] = codewords[row * M + i * SYSTEMATIC_STRIDE]
        digest = hash_chunks(systematic, ROW_CHUNKS)
        for i in unroll(0, DIGEST_LEN):
            assert digest[i] == public_row_hashes[row * DIGEST_LEN + i]

    tree = Array(TREE_DIGESTS * DIGEST_LEN)
    for cell in range(0, N_CELLS):
        column_data = Array(N * C)
        for row in range(0, N):
            for offset in range(0, C):
                column_data[row * C + offset] = codewords[row * M + cell * C + offset]
        digest = hash_chunks(column_data, COLUMN_CHUNKS)
        for i in unroll(0, DIGEST_LEN):
            tree[cell * DIGEST_LEN + i] = digest[i]

    for level in unroll(0, MERKLE_DEPTH):
        input_offset = LEVEL_OFFSETS[level]
        output_offset = LEVEL_OFFSETS[level + 1]
        for node in range(0, LEVEL_SIZES[level + 1]):
            poseidon16_compress_half(
                tree + (input_offset + 2 * node) * DIGEST_LEN,
                tree + (input_offset + 2 * node + 1) * DIGEST_LEN,
                tree + (output_offset + node) * DIGEST_LEN,
            )

    root_offset = LEVEL_OFFSETS[MERKLE_DEPTH] * DIGEST_LEN
    for i in unroll(0, DIGEST_LEN):
        assert tree[root_offset + i] == public_root[i]

    for row in range(0, N):
        result = Array(DIM)
        dot_product_be(codewords + row * M, check_vector, result, M)
        assert_ext_zero(result)
    return
