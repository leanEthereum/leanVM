from snark_lib import *

DIM = 5  # extension degree
DIGEST_LEN = 8

# memory layout: [public_input (PUBLIC_INPUT_LEN)] [preamble_memory (PREAMBLE_MEMORY_LEN)] [runtime ...]
# `preamble_memory` is a region that is filled by the guest program, with useful constants [0000...][1000...]...
PUBLIC_INPUT_LEN = DIGEST_LEN
PARTIAL_UNROLL_BATCH = 64
ZERO_VEC_PTR = PUBLIC_INPUT_LEN
ZERO_VEC_LEN = ZERO_VEC_LEN_PLACEHOLDER
SAMPLING_DOMAIN_SEPARATOR_PTR = ZERO_VEC_PTR + ZERO_VEC_LEN
ONE_EF_PTR = SAMPLING_DOMAIN_SEPARATOR_PTR + DIGEST_LEN
NUM_REPEATED_ONES = NUM_REPEATED_ONES_PLACEHOLDER
REPEATED_ONES_PTR = ONE_EF_PTR + DIM
PREAMBLE_MEMORY_END = REPEATED_ONES_PTR + NUM_REPEATED_ONES
PREAMBLE_MEMORY_LEN = PREAMBLE_MEMORY_END - PUBLIC_INPUT_LEN


# IV for the sponge: [slice length in field elements, 0, 0, ..., 0]
@inline
def build_iv(length):
    iv = Array(DIGEST_LEN)
    iv[0] = length
    for k in unroll(1, DIGEST_LEN):
        iv[k] = 0
    return iv


@inline
def sponge_finalize(carried_capacity, last_chunk):
    full = Array(2 * DIGEST_LEN)
    poseidon16_permute(carried_capacity, last_chunk, full)
    return full + DIGEST_LEN


@inline
def slice_hash_rtl(data, num_chunks, iv):
    debug_assert(1 <= num_chunks)
    result = Array(2 * DIGEST_LEN)
    if num_chunks == 1:
        poseidon16_permute(iv, data, result)
    else:
        states = Array((num_chunks - 1) * DIGEST_LEN)
        poseidon16_permute_half(iv, data + (num_chunks - 1) * DIGEST_LEN, states)
        for j in unroll(1, num_chunks - 1):
            poseidon16_permute_half(
                states + (j - 1) * DIGEST_LEN, data + (num_chunks - 1 - j) * DIGEST_LEN, states + j * DIGEST_LEN
            )
        poseidon16_permute(states + (num_chunks - 2) * DIGEST_LEN, data, result)
    return result + DIGEST_LEN


@inline
def slice_hash_ret(data, num_chunks):
    res = Array(DIGEST_LEN)
    slice_hash(data, num_chunks, res)
    return res


def slice_hash_range(data, num_chunks, dest):
    debug_assert(0 < num_chunks)
    debug_assert(2 < num_chunks)
    iv = build_iv(num_chunks * DIGEST_LEN)
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16_permute_half(iv, data, states)
    for j in range(1, num_chunks - 1):
        poseidon16_permute_half(states + (j - 1) * DIGEST_LEN, data + j * DIGEST_LEN, states + j * DIGEST_LEN)
    rate = sponge_finalize(states + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN)
    copy_8(rate, dest)
    return


@inline
def slice_hash(data, num_chunks, dest):
    debug_assert(2 <= num_chunks)
    iv = build_iv(num_chunks * DIGEST_LEN)
    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16_permute_half(iv, data, states)
    for j in unroll(1, num_chunks - 1):
        poseidon16_permute_half(states + (j - 1) * DIGEST_LEN, data + j * DIGEST_LEN, states + j * DIGEST_LEN)
    rate = sponge_finalize(states + (num_chunks - 2) * DIGEST_LEN, data + (num_chunks - 1) * DIGEST_LEN)
    copy_8(rate, dest)
    return


@inline
def slice_hash_continue(running, data, num_chunks):
    states = Array(num_chunks * DIGEST_LEN)
    poseidon16_permute_half(running, data, states)
    for j in unroll(1, num_chunks):
        poseidon16_permute_half(states + (j - 1) * DIGEST_LEN, data + j * DIGEST_LEN, states + j * DIGEST_LEN)
    return states + (num_chunks - 1) * DIGEST_LEN


@inline
def euclidean_div_runtime(a, b):
    # Returns (q, r) with q = floor(a / b) and r = a mod b.
    # Requires:
    #   1 <= b < 2^14
    #   floor(a / b) < 2^16  (so that q*b + r stays well below p)
    q: Imm
    r: Imm
    hint_div_floor(a, b, q, r)
    assert r < b
    assert q < 2 ** 16
    assert q * b + r == a
    return q, r


def absorb_n_hashes_const(n: Const, sp_in, dp_in):
    sp: Mut = sp_in
    dp: Mut = dp_in
    for _ in unroll(0, n):
        new_state = sp + DIGEST_LEN
        poseidon16_permute_half(sp, dp, new_state)
        sp = new_state
        dp += DIGEST_LEN
    return sp


def slice_hash_runtime(data, num_chunks):
    debug_assert(num_chunks != 0)

    iv = build_iv(num_chunks * DIGEST_LEN)

    if num_chunks == 1:
        return sponge_finalize(iv, data)

    states = Array((num_chunks - 1) * DIGEST_LEN)
    poseidon16_permute_half(iv, data, states)
    n_iters = num_chunks - 2

    n_chunks_outer, remainder = euclidean_div_runtime(n_iters, PARTIAL_UNROLL_BATCH)
    carry = Array((n_chunks_outer + 1) * 2)
    carry[0] = states
    carry[1] = data + DIGEST_LEN
    for c in range(0, n_chunks_outer):
        base = c * 2
        state_ptr: Mut = carry[base]
        data_ptr: Mut = carry[base + 1]
        for _ in unroll(0, PARTIAL_UNROLL_BATCH):
            new_state = state_ptr + DIGEST_LEN
            poseidon16_permute_half(state_ptr, data_ptr, new_state)
            state_ptr = new_state
            data_ptr += DIGEST_LEN
        carry[base + 2] = state_ptr
        carry[base + 3] = data_ptr
    state_ptr = carry[n_chunks_outer * 2]
    data_ptr = carry[n_chunks_outer * 2 + 1]

    final_state_ptr = match_range(
        remainder,
        range(0, PARTIAL_UNROLL_BATCH),
        lambda r: absorb_n_hashes_const(r, state_ptr, data_ptr),
    )
    return sponge_finalize(final_state_ptr, data + (num_chunks - 1) * DIGEST_LEN)


@inline
def whir_do_4_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2
    r3 = (r2 - b2) / 2
    b3 = r3 % 2

    temps = Array(3 * DIGEST_LEN)

    if b0 == 0:
        poseidon16_compress_half(state_in, path_chunk, temps)
    else:
        poseidon16_compress_half(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16_compress_half(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16_compress_half(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16_compress_half(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, temps + 2 * DIGEST_LEN)
    else:
        poseidon16_compress_half(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, temps + 2 * DIGEST_LEN)

    if b3 == 0:
        poseidon16_compress_half(temps + 2 * DIGEST_LEN, path_chunk + 3 * DIGEST_LEN, state_out)
    else:
        poseidon16_compress_half(path_chunk + 3 * DIGEST_LEN, temps + 2 * DIGEST_LEN, state_out)
    return


@inline
def whir_do_3_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2
    r2 = (r1 - b1) / 2
    b2 = r2 % 2

    temps = Array(2 * DIGEST_LEN)

    if b0 == 0:
        poseidon16_compress_half(state_in, path_chunk, temps)
    else:
        poseidon16_compress_half(path_chunk, state_in, temps)

    if b1 == 0:
        poseidon16_compress_half(temps, path_chunk + DIGEST_LEN, temps + DIGEST_LEN)
    else:
        poseidon16_compress_half(path_chunk + DIGEST_LEN, temps, temps + DIGEST_LEN)

    if b2 == 0:
        poseidon16_compress_half(temps + DIGEST_LEN, path_chunk + 2 * DIGEST_LEN, state_out)
    else:
        poseidon16_compress_half(path_chunk + 2 * DIGEST_LEN, temps + DIGEST_LEN, state_out)
    return


@inline
def whir_do_2_merkle_levels(b, state_in, path_chunk, state_out):
    b0 = b % 2
    r1 = (b - b0) / 2
    b1 = r1 % 2

    temp = Array(DIGEST_LEN)

    if b0 == 0:
        poseidon16_compress_half(state_in, path_chunk, temp)
    else:
        poseidon16_compress_half(path_chunk, state_in, temp)

    if b1 == 0:
        poseidon16_compress_half(temp, path_chunk + DIGEST_LEN, state_out)
    else:
        poseidon16_compress_half(path_chunk + DIGEST_LEN, temp, state_out)
    return


@inline
def whir_do_1_merkle_level(b, state_in, path_chunk, state_out):
    b0 = b % 2

    if b0 == 0:
        poseidon16_compress_half(state_in, path_chunk, state_out)
    else:
        poseidon16_compress_half(path_chunk, state_in, state_out)
    return
