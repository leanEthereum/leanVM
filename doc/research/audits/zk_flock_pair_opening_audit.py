"""PCS obstructions to local and whole-row swaps, and independent counter-label repair."""

import argparse
import subprocess
from collections import defaultdict
from fractions import Fraction
from math import comb
from pathlib import Path
from random import Random

from zk_flock_columns_audit import METADATA_ROWS, build
from zk_flock_coset_audit import novel_factors, probability_all_hit, reordered_index
from zk_pcs_audit import RightInverse, Tower, kdot, verifier_module
from zk_three_point_audit import THREE_POINT_SUPPORT


def evaluate(field, coefficients, query):
    factors = novel_factors(field, 22, query)
    result = 0
    for index, coefficient in coefficients.items():
        term = coefficient
        while index:
            bit = (index & -index).bit_length() - 1
            term = field.kmul(term, factors[bit])
            index &= index - 1
        result ^= term
    return result


def collapse(coefficients, size):
    result = defaultdict(int)
    for index, value in coefficients.items():
        result[index // size * size] ^= value
    return {index: value for index, value in result.items() if value}


def witness_difference(verifier):
    layout = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    base = verifier.GLOBAL_COLUMN_BASES[verifier.OP_BLAKE2S]
    names = ("cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc")
    starts = []
    for block, name in enumerate(names):
        placement = layout.placements[base + verifier.BLAKE2S_COLUMNS.index(name)]
        assert placement.index == 59 * (1 << 22) + block * (1 << 18)
        starts.append(placement.index % (1 << 22))
    code = layout.placements[verifier.BYTECODE_FINAL_COUNTERS]
    assert code.index == 59 * (1 << 22) + 5 * (1 << 18)
    private = {}
    for start in starts[:4]:
        for index in range(4):
            private[start + reordered_index((96 << 11) + 4 + index)] = int(verifier.GEN**index + verifier.GEN ** (4 + index))
    assert max(collapse(private, 2)) == 798726
    return private


def probabilities(verifier, private):
    for size in (2, 4, 8, 16):
        degree = max(collapse(private, size))
        floors = []
        for rate in range(1, 5):
            domain = 1 << (22 + rate)
            queries = verifier.derive_config(28, rate).queries[0]
            good = (domain - degree) // size
            floor = (good * probability_all_hit(domain, queries, size) - comb(good, 2) * probability_all_hit(domain, queries, 2 * size)) / 2
            exponent = next(bits for bits in range(1, 400) if floor > Fraction(1, 1 << bits))
            floors.append(exponent)
        if size == 2:
            assert floors == [10, 13, 15, 17]
        if size == 8:
            assert floors[0] < 128 and floors[1] < 128
        print(
            f"Metadata blocks of {size}: simulator-error floors exceed " + ", ".join(f"2^-{bits}" for bits in floors) + " at rates one through four.",
            flush=True,
        )


def pointer_probabilities(verifier):
    private = {reordered_index((96 << 11) + index): int(verifier.GEN**index * (verifier.ONE + verifier.GEN)) for index in range(8)}
    degree = max(collapse(private, 2))
    assert degree == 12294
    good = ((1 << 18) - degree) // 2
    assert good == 124925
    floors = []
    for rate in range(1, 5):
        domain = 1 << (22 + rate)
        queries = verifier.derive_config(28, rate).queries[0]
        floor = (good * probability_all_hit(domain, queries, 2) - comb(good, 2) * probability_all_hit(domain, queries, 4)) / 2
        floors.append(next(bits for bits in range(1, 128) if floor > Fraction(1, 1 << bits)))
    assert floors == [15, 19, 22, 25]
    print("Whole-row shuffle: private read-target simulator-error floors exceed " + ", ".join(f"2^-{bits}" for bits in floors) + ".", flush=True)
    return private


def matching_bound():
    vertices, edges, bases = 16256, 4096, 224
    unmatched = vertices - 2 * edges
    coefficients, denominator, largest = [1], 1, Fraction(0)
    for degree in range(vertices):
        numerator = (unmatched - degree) * coefficients[degree]
        if degree >= 1:
            numerator += (2 * edges - degree + 1) * coefficients[degree - 1]
        if degree >= 2:
            numerator += (vertices - degree + 2) * coefficients[degree - 2]
        assert numerator % (degree + 1) == 0
        coefficients.append(numerator // (degree + 1))
        denominator = denominator * (vertices - degree) // (degree + 1)
        if bases <= degree + 1 <= vertices // 2:
            largest = max(largest, Fraction(coefficients[-1], denominator))
    assert coefficients == coefficients[::-1]
    for degree in (0, 1, 2, bases, vertices // 2, vertices):
        assert coefficients[degree] == sum(
            comb(edges, pairs) * comb(unmatched, degree - 2 * pairs) for pairs in range(edges + 1) if 0 <= degree - 2 * pairs <= unmatched
        )
    assert largest == Fraction(coefficients[bases], comb(vertices, bases))
    bound = ((1 << 64) - 1) * largest
    assert bound < Fraction(1, 1 << 160)
    print("Given 224 disjoint affine bases, exact random-matching rank failure is below 2^-160 for each fixed query pair.", flush=True)
    return bound


def identities(verifier, private):
    field, rng = Tower(64, verifier), Random(449)
    for size in (2, 4, 8):
        for centre in (0, 1 << 20, rng.randrange(1 << 23) // size * size):
            points = [centre ^ offset for offset in range(size)]
            matrix = list(zip(*(field.novel(size.bit_length() - 1, point) for point in points)))
            weights = RightInverse(field, matrix).solve([1] * size)
            assert all(kdot(field, row, weights) == 1 for row in matrix)
            observed = kdot(field, weights, [evaluate(field, private, point) for point in points])
            assert observed == evaluate(field, collapse(private, size), centre)
            if size == 2:
                assert weights == [centre, centre ^ 1]
    print("Native-field coset interpolation recovers coefficient-block sums; the valid frame-alias difference survives.", flush=True)


def copy_position(bank, index):
    sparse, original = index & 2047, index >> 11
    if bank < 8:
        destination = dict(zip((0, 1, 2, 4, 8, 16, 32), (5, 6, 7, 9, 10, 11, 12)))[original]
    elif bank == 8:
        destination = 64 + dict(zip((0, 1, 2, 4, 8, 16), (3, 5, 6, 7, 9, 10)))[original - 64]
    else:
        destination = original
        sparse = (sparse & 255) | (6 << 8)
    return sparse + (destination << 11)


def actual_libraries(verifier):
    first, pairs, placement = build(verifier)
    second, second_pairs, _ = build(verifier, code_shift=64, frame_shift=1 << 22)
    extra = {
        copy_position(bank, position): row
        for bank, group in enumerate(second_pairs)
        for _, left, right, a, b in group
        for position, row in ((a, left), (b, right))
    }
    assert len(extra) == 16256 and not set(extra).intersection(placement) and not set(extra).intersection(METADATA_ROWS)
    assert all((index & 2047) not in THREE_POINT_SUPPORT and index >> 11 < 96 for index in extra)
    assert not set(first.images["memory"]).intersection(second.images["memory"])
    assert not set(first.images["code"]).intersection(second.images["code"])
    columns = verifier.BLAKE2S_COLUMNS
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    tail = [columns.index(name) for name in ("cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc")]
    for group in pairs:
        for _, _, _, left, right in group:
            assert reordered_index(left) ^ reordered_index(right) == 1
    for column in tail:
        assert any(first.rows[left][1][column] != first.rows[right][1][column] for group in pairs for _, left, right, _, _ in group)

    original = [(opcode, row[:]) for opcode, row in second.rows]
    row_ids = [extra[index] for index in sorted(extra)]
    assert len(counts) == 10 and columns[counts[-1]] == "cnt_bc"
    assert all(len({int(original[row][1][column]) for column in counts[:-1]}) == 1 for row in row_ids)
    permuted = row_ids[:]
    Random(457).shuffle(permuted)
    for destination, source in zip(row_ids, permuted):
        second.rows[destination] = (original[source][0], original[source][1][:])
    second.verify()
    assert all(original[row][1][9:27] == second.rows[row][1][9:27] for row in row_ids)
    changed = defaultdict(int)
    for logical, row in extra.items():
        for block, column in enumerate(tail):
            changed[block * (1 << 18) + reordered_index(logical)] ^= int(original[row][1][column] + second.rows[row][1][column])
    assert collapse(changed, 2)
    field = Tower(64, verifier)
    for query in (1 << 20, (1 << 22) + 1234, (1 << 23) - 2):
        assert evaluate(field, collapse(changed, 2), query)
    for query in ((1 << 18), (1 << 18) + 1234, (1 << 19) - 2):
        factors = novel_factors(field, 22, query)
        assert factors[18:21] == [1, 0, 0]
        assert evaluate(field, collapse(changed, 2), query) == 0
    print("Whole-row shuffling preserves equality of all nine memory-count columns; its lane-59 contribution vanishes on e18 + V18.", flush=True)

    relabeled = [(opcode, row[:]) for opcode, row in original]
    rng = Random(461)
    for _, left, right, _, _ in second_pairs[9]:
        for column in counts:
            if rng.getrandbits(1):
                relabeled[left][1][column], relabeled[right][1][column] = relabeled[right][1][column], relabeled[left][1][column]
    for destination, source in zip(row_ids, permuted):
        second.rows[destination] = (relabeled[source][0], relabeled[source][1][:])
    second.verify()
    repaired = defaultdict(int)
    for logical, row in extra.items():
        assert second.rows[row][1][9:27] == original[row][1][9:27]
        for block, column in enumerate(tail):
            repaired[block * (1 << 18) + reordered_index(logical)] ^= int(original[row][1][column] + second.rows[row][1][column])
    for query in ((1 << 18), (1 << 18) + 1234, (1 << 19) - 2):
        assert evaluate(field, collapse(repaired, 2), query)
    assert 32 * (196608 - 2 * 4096) == 6029312
    assert (3 * ((1 << 22) - 1280) - 6029312) // 256 == 25585
    print(
        "Independent fair swaps of all ten labels on 4096 repeated pairs, followed by global shuffling, preserve the bus and break the shared-column invariant.",
        flush=True,
    )
    print(
        "The existing terminal/memory/root theorem survives these independent additions. Full PCS privacy of this revised source is not proved.",
        flush=True,
    )
    positions = sorted(reordered_index(index) for index in extra)
    assert all(left ^ right == 1 for left, right in zip(positions[::2], positions[1::2]))
    positions = positions[::2]
    Random(467).shuffle(positions)
    return positions


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--matching", action="store_true", help="exhaustively certify every adjacent query pair in the exceptional coset")
    arguments = parser.parse_args()
    verifier = verifier_module()
    private = witness_difference(verifier)
    probabilities(verifier, private)
    pointer_probabilities(verifier)
    matching_bound()
    identities(verifier, private)
    positions = actual_libraries(verifier)
    if arguments.native:
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit"],
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
    if arguments.matching:
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--matching-certificate"],
            input=" ".join(map(str, positions)),
            text=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
