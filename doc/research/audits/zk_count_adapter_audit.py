"""Paired MUL adapters mask the previously frozen packet-eleven count child."""

import argparse
from fractions import Fraction
from functools import cache
from random import Random

from zk_column_count_audit import Library
from zk_count_frontier_audit import geometry
from zk_flock_children_audit import THREE_POINT_SUPPORT, error_bound
from zk_flock_coset_audit import library_messages, reordered_index
from zk_flock_interface_audit import packed_words
from zk_flock_lowbank_audit import public_prefix_sources
from zk_flock_multicoset_audit import query_sources
from zk_flock_skip_audit import witness
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import verifier_module
from zk_sparse_gkr_audit import weight
from zk_stacked_audit import binary_basis
from zk_two_point_audit import dense_fixed_error


def positions():
    result = []
    for slot in range(16):
        for bank in range(96):
            number = len(result)
            blake = tuple(128 * bank + 16384 * slot + 64 * side for side in range(2))
            logical = tuple(2048 * bank + 8 * slot + 1024 * side for side in range(2))
            assert tuple(map(reordered_index, logical)) == blake
            assert all(index & 2047 in THREE_POINT_SUPPORT for index in logical)
            mul = tuple(16 + 64 * (2 * number + side) for side in range(2))
            assert all(index % 64 == 0 for index in blake)
            assert all(index % 64 == 16 for index in mul)
            assert blake[0] >> 7 == blake[1] >> 7 and mul[0] >> 7 == mul[1] >> 7
            result.append((bank, blake, mul))
    assert len(result) == 1536
    assert len({index >> 4 for _, blake, _ in result for index in blake}) == 3072
    assert max(index for _, _, mul in result for index in mul) < 1 << 19
    for prefix_log in range(9, 13):
        assert sum(min(blake) < 1 << prefix_log for _, blake, _ in result) == 1 << (prefix_log - 7)
    return result


@cache
def adapter_error(observed_bits=32):
    size = 1 << 192

    @cache
    def tail(before, after):
        return min(Fraction(1), Fraction(((1 << before) - 1) ** 2, (size - 1) * ((1 << (2 * before - after)) - 1)))

    @cache
    def remaining(steps, dimension):
        if steps == 0:
            return min(Fraction(1), Fraction(size, size - 1) ** 2 * Fraction(2) ** (192 + observed_bits - 3 * dimension))
        maximum = min(2 * dimension, 192)
        return min(
            Fraction(1),
            remaining(steps - 1, maximum)
            + sum((tail(dimension, after) * remaining(steps - 1, after) for after in range(dimension, maximum)), Fraction()),
        )

    first_five = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())
    return first_five + remaining(4, 32) + Fraction(19, size)


def span(verifier, offsets, pairs):
    rng = Random(673)
    challenge = [verifier.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(20)]
    cv1 = verifier.BLAKE2S_COLUMNS.index("cnt_cv1")
    absorber = verifier.ARITH_COLUMNS.index("cnt_a")
    selector = weight(verifier, challenge[12:], 49)
    vectors = []
    for number, (bank, blake, mul) in enumerate(pairs):
        children = [(offsets[verifier.OP_BLAKE2S, cv1] + row) >> 4 for row in blake]
        assert all(index % 4 == 0 for index in children)
        assert all(((offsets[verifier.OP_MUL, absorber] + row) >> 4) % 4 == 1 for row in mul)
        actual = (verifier.ONE + verifier.GEN) * verifier.E.sum(weight(verifier, challenge, index >> 2) for index in children)
        expected = (verifier.ONE + verifier.GEN) * selector * weight(verifier, challenge[1:8], bank) * weight(verifier, challenge[8:12], number // 96)
        assert actual == expected
        disclosure = 1 << bank if number < 32 else 0
        vectors.append(int(actual) | (disclosure << 192))
    assert len(binary_basis(vectors)) == 224
    error = adapter_error()
    assert error < Fraction(1, 1 << 160)
    total = error + error_bound(128) + Fraction(20, 1 << 192) + joint_root_bound()
    total += dense_fixed_error(176) + dense_fixed_error(48) + dense_fixed_error(240)
    assert total < Fraction(1, 1 << 151)
    print("Actual packet-eleven child and 32 prefix bits have sampled joint rank 224; the uniform fiber-failure bound is below 2^-160.", flush=True)
    print(
        "Adding this child to the established restricted boundary keeps its exact error ledger below 2^-151; earlier packets are excluded.",
        flush=True,
    )


def prefix(verifier, pairs):
    from zk_flock_lowbank_audit import extra_query_sources
    from zk_flock_lowbank_audit import positions as low_positions
    from zk_pcs_audit import Tower

    field = Tower(64, verifier)
    old = query_sources(field)[0] + extra_query_sources(field, low_positions())
    sources, disclosed = public_prefix_sources([(polynomial, 0) for polynomial in old])
    assert len(sources) == 66300 and disclosed == 1084
    occupied = {index for polynomial in old for index, _ in polynomial if index < 4096}
    new = [blake for _, blake, _ in pairs if min(blake) < 4096]
    assert len(new) == 32
    assert not occupied.intersection(index for blake in new for index in blake)
    assert len({index for blake in new for index in blake}) == 64
    print("The new prefix supports are disjoint: the complete 4096-point lane-59 prefix encodes 1084 + 32 = 1116 independent bits.", flush=True)


def valid_cycles(verifier, pairs):
    library, rng = Library(verifier), Random(677)
    baseline = packed_words(witness(verifier, [0] * 16))
    profiles = [packed_words(witness(verifier, message)) for message in library_messages()[:96]]
    locations = []
    for number, (bank, _, _) in enumerate(pairs):
        paired = []
        for side in range(2):
            frame = verifier.GEN ** ((2 << 22) + 1280 + 32 * (2 * number + side))
            row = library.row(verifier.OP_BLAKE2S, 1110, frame)
            words = profiles[bank] if rng.getrandbits(1) else baseline
            for slot, name in enumerate(verifier.BLAKE2S_SLOTS):
                if name:
                    row[verifier.BLAKE2S_COLUMNS.index(name)] = verifier.E(words[slot])
            adapter = library.row(verifier.OP_MUL, 1111, frame)
            cv1 = [row[verifier.BLAKE2S_COLUMNS.index(name)] for name in ("cv1_lo", "cv1_hi")]
            for name, value in zip(("o_a", "o_b", "o_c", "va_0", "va_1"), (verifier.GEN**9, verifier.GEN**30, verifier.GEN**31, *cv1)):
                adapter[verifier.ARITH_COLUMNS.index(name)] = value
            closing = library.row(verifier.OP_JUMP, 1112, frame, 1110)
            for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18)):
                closing[verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
            first, second, _ = library.append([(verifier.OP_BLAKE2S, row), (verifier.OP_MUL, adapter), (verifier.OP_JUMP, closing)])
            paired.append(((first, verifier.BLAKE2S_COLUMNS.index("cnt_cv1")), (second, verifier.ARITH_COLUMNS.index("cnt_a"))))
        locations.append(paired)
    for paired in locations:
        for side, (blake, mul) in enumerate(paired):
            library.set_labels((blake, mul), (side, 1 - side))
    library.verify()
    roots, reads = dict(library.exponents), dict(library.reads)
    for paired in locations:
        bit = rng.getrandbits(1)
        for side, (blake, mul) in enumerate(paired):
            library.set_labels((blake, mul), (bit ^ side, 1 ^ bit ^ side))
    library.verify()
    assert dict(library.exponents) == roots and dict(library.reads) == reads
    assert len(library.rows) == 6 * len(pairs) and len(library.images["code"]) == 3
    print(f"All {len(pairs)} paired adapters pass ISA constraints, counted buses, complete read chains and unchanged column products.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="check all 3072 compression/MUL/return cycles against the native reference constraints")
    arguments = parser.parse_args()
    verifier = verifier_module()
    pairs = positions()
    span(verifier, geometry(verifier), pairs)
    prefix(verifier, pairs)
    valid_cycles(verifier, pairs if arguments.full else pairs[:2])
