"""Long-chain low-coordinate count source, with exact span and geometry certificates."""

import argparse
import subprocess
from fractions import Fraction
from pathlib import Path
from random import Random

from zk_column_count_audit import Library
from zk_flock_children_audit import (
    METADATA_ROWS,
    THREE_POINT_SUPPORT,
    error_bound,
    families,
    pair,
)
from zk_flock_coset_audit import reordered_index
from zk_flock_pair_opening_audit import blake_bus_forms
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis


def positions():
    occupied = {row for kind, banks, support in families(True) for bank in range(banks) for index in support for row in pair(kind, bank, index)}
    available = {
        reordered_index(row)
        for row in range(96 * 2048)
        if row & 2047 not in THREE_POINT_SUPPORT and row not in occupied and row not in METADATA_ROWS and reordered_index(row) < 1 << 14
    }
    blocks = sorted(base for base in available if base & 15 == 0 and all(base + child in available for child in range(16)))
    assert len(blocks) == 240 and max(blocks) < 12288
    assert available - {base + child for base in blocks for child in range(16)} == {437, 438, 439}
    print("240 disjoint free low blocks provide 3840 rows, leaving the existing source and five general-input rows untouched.", flush=True)
    return list(zip(blocks[:120], blocks[120:]))


def build(verifier, blocks):
    library = Library(verifier)
    frame = verifier.GEN ** (1280 + 32 * 65535)
    templates = library.templates((verifier.OP_BLAKE2S, 1090, [], True), frame)
    for name, offset in zip(("o_c", "o_d", "o_f"), range(16, 19)):
        templates[-1][1][verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    pairs = []
    for block, (left, right) in enumerate(blocks):
        for child in range(16):
            first, second = library.append(templates)[0], library.append(templates)[0]
            number = 16 * block + child
            assert all(library.rows[first][1][column] == verifier.GEN ** (2 * number) for column in counts)
            assert all(library.rows[second][1][column] == verifier.GEN ** (2 * number + 1) for column in counts)
            pairs.append((first, second, left + child, right + child))
    assert len(library.rows) == 7680 and len(library.images["code"]) == 2
    library.verify()
    rng = Random(641)
    for first, second, _, _ in pairs:
        for column in counts:
            if rng.getrandbits(1):
                library.rows[first][1][column], library.rows[second][1][column] = library.rows[second][1][column], library.rows[first][1][column]
    library.verify()
    print("A single 32-cell frame and two code locations support all 3840 compression/return cycles and independent valid count swaps.", flush=True)


def span_error():
    size = 1 << 192
    moore = Fraction(14 * ((1 << 56) - 1), size)

    def finish(dimension):
        return min(Fraction(1), Fraction(size, size - 2) ** 3 * Fraction(2) ** (192 - 4 * dimension))

    low = finish(112)
    for dimension in range(56, 112):
        low += Fraction(((1 << 56) - 1) ** 2, (size - 2) * ((1 << (112 - dimension)) - 1)) * finish(dimension)
    assert low < Fraction(1, 1 << 166)
    total = moore + low + Fraction(8, size)
    assert total < Fraction(1, 1 << 132)
    print("Sixteen coset values and one terminal extension value have a joint Moore/low-coordinate error below 2^-132.", flush=True)
    return total


def combined_error():
    total = span_error() + error_bound(128) + Fraction(20, 1 << 192) + joint_root_bound()
    assert total < Fraction(1, 1 << 132)
    assert 181252 - 3840 + 1 == 177413
    assert 32 * 177413 == 5677216
    assert (3 * ((1 << 22) - 1280) - 5677216) // 256 == 26960
    print("The new local bank, prior boundary, extra count minor and memory/root ledger together remain below 2^-132.", flush=True)


def extra_joint_sources(field, verifier, seed, blocks):
    rng = Random(seed)
    terminal = [field.random(rng) for _ in range(18)]
    parent = [verifier.E(*field.coords(field.random(rng))) for _ in range(24)]
    alphas = [verifier.E(*field.coords(field.random(rng))) for _ in range(4)]
    forms, _ = blake_bus_forms(verifier, [verifier.ZERO, verifier.ZERO, *parent], alphas)
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    columns = verifier.BLAKE2S_COLUMNS
    matrix = [[int(form.terms.get((column,), verifier.ZERO)) for column in counts] for form in forms]
    first, second = [counts.index(columns.index(name)) for name in ("cnt_cv0", "cnt_out0")]
    assert field.mul(matrix[1][first], matrix[2][second]) != field.mul(matrix[1][second], matrix[2][first])
    terminal_weights = field.eq(terminal)
    parent_weights = field.eq([int(value) for value in parent[:16]])
    inverse = {reordered_index(logical): logical for logical in range(1 << 18)}
    lane_columns = [columns.index(name) for name in ("cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc")]
    result, delta = [], 3
    for left, right in blocks:
        for child in range(16):
            a, b = left + child, right + child
            terminal_delta = field.mul(delta, terminal_weights[inverse[a]] ^ terminal_weights[inverse[b]])
            child_delta = field.mul(delta, parent_weights[a >> 2] ^ parent_weights[b >> 2])
            for number, column in enumerate(counts):
                prefix = terminal_delta << (192 * (9 + number))
                prefix |= sum(field.mul(matrix[side][number], child_delta) << (192 * (19 + 3 * (child & 3) + side)) for side in range(3))
                polynomial = []
                if column in lane_columns:
                    block = lane_columns.index(column)
                    polynomial = [(block * (1 << 18) + endpoint, delta) for endpoint in (a, b)]
                result.append((polynomial, prefix))
            delta = field.kmul(delta, 4)
    assert len(result) == 19200
    return result


def decomposition_certificate(field, verifier, old, extra):
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    cv1 = counts.index(verifier.BLAKE2S_COLUMNS.index("cnt_cv1"))
    mask = (1 << 192) - 1

    def unpack(prefix):
        return [(prefix >> (192 * index)) & mask for index in range(31)]

    def pack(values):
        return sum(value << (192 * index) for index, value in enumerate(values))

    noncount_size = 8 * 384 + 4 * 1279
    other_counts = []
    for index, (polynomial, prefix) in enumerate(old[noncount_size : noncount_size + 4 * 1280 * 10]):
        if index % 10 == cv1:
            continue
        values = unpack(prefix)
        assert not any(values[:9]) and values[9 + cv1] == 0
        assert all(values[19 + 3 * child] == field.mul(2, values[20 + 3 * child]) for child in range(4))
        assert all(position >= 1 << 18 for position, _ in polynomial)
        other_counts.append(
            pack(
                [
                    *[values[9 + number] for number in range(10) if number != cv1],
                    *[values[20 + 3 * child + side] for child in range(4) for side in range(2)],
                ]
            )
        )
    assert len(binary_basis(other_counts)) == 17 * 192 == 3264
    noncounts = []
    for _, prefix in old[:noncount_size]:
        values = unpack(prefix)
        residuals = [values[19 + 3 * child] ^ field.mul(2, values[20 + 3 * child]) for child in range(4)]
        noncounts.append(pack([*values[:9], *residuals]))
    assert len(binary_basis(noncounts)) == 13 * 192 == 2496
    query_weights = field.novel(14, 12288)
    low = []
    for polynomial, prefix in extra[cv1::10]:
        values = unpack(prefix)
        assert not any(values[index] for index in range(19) if index != 9 + cv1)
        assert all(values[19 + 3 * child] == field.mul(2, values[20 + 3 * child]) for child in range(4))
        (left, delta), (right, _) = polynomial
        raw = field.kmul(delta, query_weights[left & ~15] ^ query_weights[right & ~15])
        low.append(values[9 + cv1] | (raw << (192 + 64 * (left & 15))))
    assert len(binary_basis(low)) == 1216
    print("Three-group certificate: ranks 3264, 1216 and 2496, with every required zero projection and child-plane invariance checked.", flush=True)


def sampled_rank(field, blocks):
    for query in (8192, 12288, 16384, 65536, 262128):
        weights = field.novel(14, query)
        values = [field.kmul(3, weights[left] ^ weights[right]) for left, right in blocks]
        power = 1
        for index in range(len(values)):
            values[index] = field.kmul(values[index], power)
            power = field.kmul(power, 1 << 32)
        assert len(binary_basis(values)) == 64
    print("Sampled low-bank scalar maps have rank 64; the native run checks every claimed coset.", flush=True)


def terminal_rank(field, blocks):
    rng = Random(643)
    point = [field.random(rng) for _ in range(18)]
    low, high = field.eq(point[:4]), field.eq(point[4:])
    query_weights = field.novel(14, 12288)
    vectors, scale = [], 3
    for left, right in blocks:
        for child in range(16):
            terminal = field.mul(scale, field.mul(low[child], high[left >> 4] ^ high[right >> 4]))
            raw = field.kmul(scale, query_weights[left] ^ query_weights[right])
            vectors.append(terminal | (raw << (192 + 64 * child)))
            scale = field.kmul(scale, 4)
    assert len(binary_basis(vectors)) == 192 + 16 * 64 == 1216
    print("Native-field diagnostic rank 1216 for the low-bank terminal value and sixteen raw coset coordinates jointly.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="check all valid cycles and randomized count chains")
    arguments = parser.parse_args()
    blocks = positions()
    verifier = verifier_module()
    field = Tower(64, verifier)
    sampled_rank(field, blocks)
    terminal_rank(field, blocks)
    combined_error()
    if arguments.full:
        build(verifier, blocks)
    subprocess.run(
        ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--lowbank-certificate"],
        input=" ".join(str(value) for block in blocks for value in block),
        text=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
