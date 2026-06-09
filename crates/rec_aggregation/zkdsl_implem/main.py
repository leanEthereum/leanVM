from recursion import *
from xmss_aggregate import *

MAX_RECURSIONS = MAX_RECURSIONS_PLACEHOLDER
MAX_N_SIGS = MAX_XMSS_AGGREGATED_PLACEHOLDER
MAX_N_DUPS = MAX_XMSS_DUPLICATES_PLACEHOLDER

# data_buf[0..8] = [flag, count, 0×6] (count = n_sigs for single-message, n_components for multi-message).
SINGLE_MESSAGE_FLAG = SINGLE_MESSAGE_FLAG_PLACEHOLDER
MULTI_MESSAGE_FLAG = MULTI_MESSAGE_FLAG_PLACEHOLDER

BYTECODE_SUMCHECK_PROOF_SIZE = BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER

# layout: [flag, count, 0×6 (8)] [bytecode_claim_padded] [initial_fiat_shamir_cap(8)] [single-message/multi-message mode-specific data]
BYTECODE_CLAIM_OFFSET = DIGEST_LEN  # (right after the prefix chunk)
INITIAL_FIAT_SHAMIR_CAP_OFFSET = BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE_PADDED
COMPONENT_DATA_OFFSET = INITIAL_FIAT_SHAMIR_CAP_OFFSET + DIGEST_LEN

# Single-message mode-specific data (fixed): pubkeys_hash | message | merkle_chunks | tweaks_hash.
SINGLE_MESSAGE_PUBKEYS_HASH_OFFSET = COMPONENT_DATA_OFFSET
SINGLE_MESSAGE_MSG_HASH_OFFSET = COMPONENT_DATA_OFFSET + DIGEST_LEN
SINGLE_MESSAGE_MERKLE_CHUNKS_OFFSET = SINGLE_MESSAGE_MSG_HASH_OFFSET + DIGEST_LEN
SINGLE_MESSAGE_TWEAKS_HASH_OFFSET = SINGLE_MESSAGE_MERKLE_CHUNKS_OFFSET + N_MERKLE_CHUNKS
SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED = SINGLE_MESSAGE_TWEAKS_HASH_OFFSET + DIGEST_LEN
SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS = SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED / DIGEST_LEN

# Multi-message mode-specific data (variable): n_components × digest(8).
MULTI_MESSAGE_DIGESTS_OFFSET = COMPONENT_DATA_OFFSET

BYTECODE_CLAIM_NUM_CHUNKS = BYTECODE_CLAIM_SIZE_PADDED / DIGEST_LEN
MULTI_MESSAGE_BASE_NUM_CHUNKS = BYTECODE_CLAIM_NUM_CHUNKS + 2  # prefix chunk + domsep chunk


def main():
    debug_assert(MAX_N_SIGS + MAX_N_DUPS <= 2**16)  # because of range checking, TODO increase
    pub_mem = 0  # See hashing.py for the memory layout
    build_preamble_memory()

    input_data_num_chunks_buf = Array(1)
    hint_witness("input_data_num_chunks", input_data_num_chunks_buf)
    input_data_num_chunks = input_data_num_chunks_buf[0]
    data_buf = Array(input_data_num_chunks * DIGEST_LEN)
    hint_witness("input_data", data_buf)
    set_to_6_zeros(data_buf + 2)

    bytecode_claim_output = data_buf + BYTECODE_CLAIM_OFFSET
    initial_fiat_shamir_cap = data_buf + INITIAL_FIAT_SHAMIR_CAP_OFFSET

    discriminator = data_buf[0]
    if discriminator == MULTI_MESSAGE_FLAG:
        # Multi-message: merge of n single-message aggregate signatures.
        n_components = data_buf[1]
        assert n_components != 0
        assert n_components <= MAX_RECURSIONS

        n_bytecode_claims = n_components * 2
        bytecode_claims = Array(n_bytecode_claims)

        for c in range(0, n_components):
            component_digest = data_buf + MULTI_MESSAGE_DIGESTS_OFFSET + c * DIGEST_LEN
            inner_single_message_buf = Array(SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED)
            hint_witness("component_layout", inner_single_message_buf)
            ensure_well_formed_input_data(inner_single_message_buf, initial_fiat_shamir_cap, SINGLE_MESSAGE_FLAG)
            slice_hash(inner_single_message_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, component_digest)

            bytecode_claims[2 * c] = inner_single_message_buf + BYTECODE_CLAIM_OFFSET
            bytecode_claims[2 * c + 1] = recursion(component_digest, initial_fiat_shamir_cap)

        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, initial_fiat_shamir_cap)

        slice_hash_range(data_buf, n_components + MULTI_MESSAGE_BASE_NUM_CHUNKS, pub_mem)
        return

    assert discriminator == SINGLE_MESSAGE_FLAG

    is_split_buf = Array(1)
    hint_witness("is_split", is_split_buf)
    if is_split_buf[0] == 1:
        # ============ single-message: Split (extract a single-message from a multi-message) ============
        multi_message_meta_hint = Array(2)
        hint_witness("multi_message_meta", multi_message_meta_hint)
        multi_message_n_components = multi_message_meta_hint[0]
        multi_message_kept_index = multi_message_meta_hint[1]
        assert multi_message_n_components != 0
        assert multi_message_n_components <= MAX_RECURSIONS
        assert multi_message_kept_index < multi_message_n_components

        multi_message_num_chunks = multi_message_n_components + MULTI_MESSAGE_BASE_NUM_CHUNKS
        multi_message_data_buf = Array(multi_message_num_chunks * DIGEST_LEN)
        hint_witness("inner_multi_message_layout", multi_message_data_buf)
        ensure_well_formed_input_data(multi_message_data_buf, initial_fiat_shamir_cap, MULTI_MESSAGE_FLAG)
        multi_message_digests = multi_message_data_buf + MULTI_MESSAGE_DIGESTS_OFFSET

        kept_single_message_buff = Array(SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED)
        hint_witness("kept_single_message_buff", kept_single_message_buff)
        copy_8(data_buf, kept_single_message_buff)  # single-message flag | n_signatures | 0×6
        copy_32(data_buf + COMPONENT_DATA_OFFSET, kept_single_message_buff + COMPONENT_DATA_OFFSET)
        ensure_well_formed_input_data(kept_single_message_buff, initial_fiat_shamir_cap, SINGLE_MESSAGE_FLAG)
        digest_kept = multi_message_digests + multi_message_kept_index * DIGEST_LEN
        slice_hash(kept_single_message_buff, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, digest_kept)

        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        slice_hash_range(multi_message_data_buf, multi_message_num_chunks, inner_pub_mem)
        bytecode_claims = Array(2)
        bytecode_claims[0] = multi_message_data_buf + BYTECODE_CLAIM_OFFSET
        bytecode_claims[1] = recursion(inner_pub_mem, initial_fiat_shamir_cap)
        reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output, initial_fiat_shamir_cap)
        slice_hash(data_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, pub_mem)
        return

    # ============ Standard single-message: single (message, slot) aggregation ============
    n_sigs = data_buf[1]
    assert n_sigs != 0
    assert n_sigs <= MAX_N_SIGS

    tweak_table: Mut = TWEAK_TABLE_ADDR
    hint_witness("tweak_table", tweak_table)

    pubkeys_hash_expected = data_buf + SINGLE_MESSAGE_PUBKEYS_HASH_OFFSET
    message = data_buf + SINGLE_MESSAGE_MSG_HASH_OFFSET
    merkle_chunks_for_slot = data_buf + SINGLE_MESSAGE_MERKLE_CHUNKS_OFFSET
    tweaks_hash_expected = data_buf + SINGLE_MESSAGE_TWEAKS_HASH_OFFSET

    # meta = [n_recursions, n_dup, n_raw_xmss]
    meta = Array(3)
    hint_witness("meta", meta)
    n_recursions = meta[0]
    assert n_recursions <= MAX_RECURSIONS

    n_dup = meta[1]
    assert n_dup <= MAX_N_DUPS  # TODO increase

    all_pubkeys = Array((n_sigs + n_dup) * PUB_KEY_SIZE)
    hint_witness("pubkeys", all_pubkeys)
    n_raw_xmss = meta[2]
    raw_indices = Array(n_raw_xmss)
    hint_witness("raw_indices", raw_indices)

    aggregate_sizes = Array(n_recursions)
    hint_witness("aggregate_sizes", aggregate_sizes)

    computed_tweaks_hash = slice_hash_ret(tweak_table, TWEAK_TABLE_SIZE_FE_PADDED / DIGEST_LEN)
    copy_8(computed_tweaks_hash, tweaks_hash_expected)

    # 1->1 optimization: a single recursive single-message child, no raw signatures, no duplicates.
    if n_recursions == 1:
        assert n_dup == 0
        if n_raw_xmss == 0:
            single_message_data_buf = Array(SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED)
            copy_8(data_buf, single_message_data_buf)  # prefix
            copy_32(data_buf + COMPONENT_DATA_OFFSET, single_message_data_buf + COMPONENT_DATA_OFFSET)
            hint_witness("inner_bytecode_claim", single_message_data_buf + BYTECODE_CLAIM_OFFSET)
            ensure_well_formed_input_data(single_message_data_buf, initial_fiat_shamir_cap, SINGLE_MESSAGE_FLAG)
            inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
            slice_hash(single_message_data_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, inner_pub_mem)
            bytecode_claims = Array(2)
            bytecode_claims[0] = single_message_data_buf + BYTECODE_CLAIM_OFFSET
            bytecode_claims[1] = recursion(inner_pub_mem, initial_fiat_shamir_cap)
            reduce_bytecode_claims(bytecode_claims, 2, bytecode_claim_output, initial_fiat_shamir_cap)
            slice_hash(data_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, pub_mem)
            return

    # General path
    computed_pubkeys_hash = slice_hash_runtime(all_pubkeys, n_sigs)
    copy_8(computed_pubkeys_hash, pubkeys_hash_expected)

    # Buffer for partition verification
    n_total = n_sigs + n_dup
    buffer = Array(n_total)

    for i in parallel_range(0, n_raw_xmss):
        idx = raw_indices[i]
        assert idx < n_total
        buffer[idx] = i
        pk = all_pubkeys + idx * PUB_KEY_SIZE
        xmss_verify(pk, message, merkle_chunks_for_slot)

    n_bytecode_claims = n_recursions * 2
    bytecode_claims = Array(n_bytecode_claims)

    counter_outer_buf = Array(n_recursions + 1)
    counter_outer_buf[0] = n_raw_xmss
    for rec_idx in range(0, n_recursions):
        counter: Mut = counter_outer_buf[rec_idx]
        n_sub = aggregate_sizes[rec_idx]
        assert n_sub != 0
        assert n_sub <= MAX_N_SIGS
        sub_indices_arr = Array(n_sub)
        hint_witness("sub_indices", sub_indices_arr)

        running_hash: Mut = build_iv(n_sub * PUB_KEY_SIZE)
        n_first = n_sub - 1
        n_chunks, remainder = euclidean_div_runtime(n_first, PARTIAL_UNROLL_BATCH)
        pubkey_idx: Mut = 0
        inner_carry = Array((n_chunks + 1) * 3)
        inner_carry[0] = counter
        inner_carry[1] = running_hash
        inner_carry[2] = pubkey_idx
        for c in range(0, n_chunks):
            base = c * 3
            cur_counter: Mut = inner_carry[base]
            cur_running_hash: Mut = inner_carry[base + 1]
            cur_pubkey_idx: Mut = inner_carry[base + 2]
            for u in unroll(0, PARTIAL_UNROLL_BATCH):
                cur_counter, cur_running_hash = absorb_recursive_pubkey(
                    cur_pubkey_idx + u, sub_indices_arr, n_total, all_pubkeys, buffer, cur_counter, cur_running_hash
                )
            cur_pubkey_idx += PARTIAL_UNROLL_BATCH
            inner_carry[base + 3] = cur_counter
            inner_carry[base + 4] = cur_running_hash
            inner_carry[base + 5] = cur_pubkey_idx
        counter = inner_carry[n_chunks * 3]
        running_hash = inner_carry[n_chunks * 3 + 1]
        pubkey_idx = inner_carry[n_chunks * 3 + 2]
        # Tail iterations
        tail_counter, tail_running_hash = match_range(
            remainder,
            range(0, PARTIAL_UNROLL_BATCH),
            lambda r: absorb_n_pubkeys_const(
                r, pubkey_idx, sub_indices_arr, n_total, all_pubkeys, buffer, counter, running_hash
            ),
        )
        counter = tail_counter
        running_hash = tail_running_hash
        # Final pubkey (index n_sub - 1)
        counter, running_hash = absorb_recursive_pubkey_final(
            n_sub - 1, sub_indices_arr, n_total, all_pubkeys, buffer, counter, running_hash
        )

        single_message_data_buf = Array(SINGLE_MESSAGE_INPUT_DATA_SIZE_PADDED)
        single_message_data_buf[0] = SINGLE_MESSAGE_FLAG
        single_message_data_buf[1] = n_sub
        for k in unroll(2, DIGEST_LEN):
            single_message_data_buf[k] = 0

        copy_8(running_hash, single_message_data_buf + SINGLE_MESSAGE_PUBKEYS_HASH_OFFSET)
        copy_8(message, single_message_data_buf + SINGLE_MESSAGE_PUBKEYS_HASH_OFFSET + DIGEST_LEN)
        copy_8(merkle_chunks_for_slot, single_message_data_buf + SINGLE_MESSAGE_PUBKEYS_HASH_OFFSET + DIGEST_LEN + MESSAGE_LEN)
        copy_8(tweaks_hash_expected, single_message_data_buf + SINGLE_MESSAGE_TWEAKS_HASH_OFFSET)
        hint_witness("inner_bytecode_claim", single_message_data_buf + BYTECODE_CLAIM_OFFSET)
        ensure_well_formed_input_data(single_message_data_buf, initial_fiat_shamir_cap, SINGLE_MESSAGE_FLAG)
        inner_pub_mem = Array(INNER_PUB_MEM_SIZE)
        slice_hash(single_message_data_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, inner_pub_mem)

        bytecode_claims[2 * rec_idx] = single_message_data_buf + BYTECODE_CLAIM_OFFSET
        bytecode_claims[2 * rec_idx + 1] = recursion(inner_pub_mem, initial_fiat_shamir_cap)
        counter_outer_buf[rec_idx + 1] = counter

    counter = counter_outer_buf[n_recursions]
    assert counter == n_total

    if n_recursions == 0:
        for k in unroll(0, BYTECODE_POINT_N_VARS):
            set_to_5_zeros(bytecode_claim_output + k * DIM)
        bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM] = BYTECODE_ZERO_EVAL
        for k in unroll(1, DIM):
            bytecode_claim_output[BYTECODE_POINT_N_VARS * DIM + k] = 0
    else:
        reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, initial_fiat_shamir_cap)

    slice_hash(data_buf, SINGLE_MESSAGE_INPUT_DATA_NUM_CHUNKS, pub_mem)
    return


def reduce_bytecode_claims(bytecode_claims, n_bytecode_claims, bytecode_claim_output, initial_fiat_shamir_cap):
    debug_assert(n_bytecode_claims != 0)
    bytecode_sumcheck_proof = Array(BYTECODE_SUMCHECK_PROOF_SIZE)
    hint_witness("bytecode_sumcheck_proof", bytecode_sumcheck_proof)
    reduction_capacity = Array(DIGEST_LEN)
    reduction_capacity[0] = initial_fiat_shamir_cap[0] + 1  # Domain-separate this sub-protocol from the main snark
    for i in unroll(1, DIGEST_LEN):
        reduction_capacity[i] = initial_fiat_shamir_cap[i]

    count_block = Array(DIGEST_LEN)
    count_block[0] = n_bytecode_claims
    for k in unroll(1, DIGEST_LEN):
        count_block[k] = 0
    rc_buf = Array(n_bytecode_claims)
    rc_buf[0] = slice_hash_continue(reduction_capacity, count_block, 1)

    for i in range(0, n_bytecode_claims - 1):
        running_capacity: Mut = rc_buf[i]
        claim_ptr = bytecode_claims[i]
        for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
            assert claim_ptr[k] == 0
        running_capacity = slice_hash_continue(running_capacity, claim_ptr, BYTECODE_CLAIM_NUM_CHUNKS)
        rc_buf[i + 1] = running_capacity

    running_capacity: Mut = rc_buf[n_bytecode_claims - 1]
    last_claim = bytecode_claims[n_bytecode_claims - 1]
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        assert last_claim[k] == 0
    running_capacity = slice_hash_continue(running_capacity, last_claim, BYTECODE_CLAIM_NUM_CHUNKS - 1)
    reduction_fs: Mut = fs_new(bytecode_sumcheck_proof, running_capacity)
    reduction_fs = fs_observe_chunks(reduction_fs, last_claim + (BYTECODE_CLAIM_NUM_CHUNKS - 1) * DIGEST_LEN, 1)
    reduction_fs, alpha = fs_sample_ef(reduction_fs)
    alpha_powers = powers(alpha, n_bytecode_claims)

    all_values = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        copy_ef(claim_ptr + BYTECODE_POINT_N_VARS * DIM, all_values + i * DIM)

    claimed_sum = Array(DIM)
    dot_product_ee_dynamic(all_values, alpha_powers, claimed_sum, n_bytecode_claims)

    reduction_fs, challenges, final_eval = sumcheck_verify(reduction_fs, BYTECODE_POINT_N_VARS, claimed_sum, 2)

    eq_evals = Array(n_bytecode_claims * DIM)
    for i in range(0, n_bytecode_claims):
        claim_ptr = bytecode_claims[i]
        poly_eq_ee(claim_ptr, challenges, eq_evals + i * DIM, BYTECODE_POINT_N_VARS)
    w_r = Array(DIM)
    dot_product_ee_dynamic(eq_evals, alpha_powers, w_r, n_bytecode_claims)

    bytecode_value_at_r = div_extension_ret(final_eval, w_r)

    copy_many_ef(challenges, bytecode_claim_output, BYTECODE_POINT_N_VARS)
    copy_ef(bytecode_value_at_r, bytecode_claim_output + BYTECODE_POINT_N_VARS * DIM)
    return


@inline
def ensure_well_formed_input_data(data_buf, initial_fiat_shamir_cap, flag):
    data_buf[0] = flag
    # data_buf[1]: count
    set_to_6_zeros(data_buf + 2)
    for k in unroll(BYTECODE_CLAIM_OFFSET + BYTECODE_CLAIM_SIZE, INITIAL_FIAT_SHAMIR_CAP_OFFSET):
        data_buf[k] = 0
    copy_8(initial_fiat_shamir_cap, data_buf + INITIAL_FIAT_SHAMIR_CAP_OFFSET)
    return


@inline
def _pubkey_absorb_prep(j, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in):
    idx = sub_indices_arr[j]
    assert idx < n_total
    buffer[idx] = counter_in
    return counter_in + 1, all_pubkeys + idx * PUB_KEY_SIZE


@inline
def absorb_recursive_pubkey(j, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in, running_hash_in):
    new_counter, pk = _pubkey_absorb_prep(j, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in)
    new_hash = Array(DIGEST_LEN)
    poseidon16_permute_half(running_hash_in, pk, new_hash)
    return new_counter, new_hash


@inline
def absorb_recursive_pubkey_final(j, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in, running_hash_in):
    new_counter, pk = _pubkey_absorb_prep(j, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in)
    return new_counter, sponge_finalize(running_hash_in, pk)


def absorb_n_pubkeys_const(
    n: Const, j_start, sub_indices_arr, n_total, all_pubkeys, buffer, counter_in, running_hash_in
):
    counter: Mut = counter_in
    running_hash: Mut = running_hash_in
    for u in unroll(0, n):
        counter, running_hash = absorb_recursive_pubkey(
            j_start + u, sub_indices_arr, n_total, all_pubkeys, buffer, counter, running_hash
        )
    return counter, running_hash
