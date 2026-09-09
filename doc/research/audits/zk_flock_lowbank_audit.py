"""Long-chain low-coordinate count source, with exact span and geometry certificates."""

import argparse
import subprocess
from fractions import Fraction
from math import comb, prod
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
from zk_flock_coset_audit import novel_factors, reordered_index
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
    lower = [base for base in blocks if base & 16 == 0]
    upper = [base for base in blocks if base & 16]
    assert len(lower) == 56 and len(upper) == 184
    return list(zip(lower, upper[:56])) + list(zip(upper[56:120], upper[120:]))


def sorted_matching(blocks):
    bases = sorted(base for pair in blocks for base in pair)
    pairs = list(zip(bases[:120], bases[120:]))
    assert sum(left & 16 == 0 or right & 16 == 0 for left, right in pairs) == 30
    return pairs


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


def extra_query_sources(field, blocks):
    result, delta = [], 3
    for left, right in blocks:
        for child in range(16):
            for block in range(5):
                result.append([(block * (1 << 18) + endpoint + child, delta) for endpoint in (left, right)])
            delta = field.kmul(delta, 4)
    assert len(result) == 9600
    return result


def cluster_certificate(field, verifier, blocks):
    from zk_flock_multicoset_audit import query_sources

    private = [(12288 + index, field.kmul(1 << index, 3)) for index in range(8)]
    for balanced, count, rank, membership in ((False, 27, 1728, "INSIDE 0"), (False, 28, 1760, "OUTSIDE 0 "), (True, 32, 2048, "INSIDE 0")):
        selected = blocks if balanced else sorted_matching(blocks)
        source = query_sources(field)[0] + extra_query_sources(field, selected)
        source = {tuple((index, value) for index, value in polynomial if index < 1 << 14) for polynomial in source}
        source.discard(())
        assert len(source) == 2876
        payload = [count, 0, *range(12288, 12288 + count), 0]
        for polynomials in (sorted(source), [private]):
            payload.append(len(polynomials))
            for polynomial in polynomials:
                payload.append(len(polynomial))
                payload.extend(value for term in polynomial for value in term)
                payload.append(0)
        result = subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--query-map-fiber-certificate"],
            input=" ".join(map(str, payload)),
            text=True,
            capture_output=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
        assert f"RANK {rank} {64 * count}\n" in result.stdout
        assert any(line.startswith(membership) for line in result.stdout.splitlines())
        print(
            f"{'Balanced' if balanced else 'Historical sorted'} matching: {count} queries, rank {rank}/{64 * count}, private pointer {membership.split()[0].lower()}.",
            flush=True,
        )
    for rate, bits in enumerate((399, 458, 505, 548), 1):
        count = verifier.derive_config(28, rate).queries[0]
        bound = Fraction(7936 * comb(32, 28) * prod(range(count - 27, count + 1)), 1 << (28 * (22 + rate)))
        assert bound < Fraction(1, 1 << bits)
        print(
            f"Rate {rate}: any low 32-point coset receiving 28 distinct queries has probability below 2^-{bits}; other defects remain unbounded.",
            flush=True,
        )


def scattered_certificate(field, verifier, blocks):
    from zk_flock_multicoset_audit import query_sources

    queries = [
        8261,
        8414,
        9023,
        9086,
        9225,
        9337,
        9532,
        9768,
        9853,
        9913,
        10164,
        10206,
        10615,
        11141,
        11658,
        11753,
        11818,
        12440,
        12519,
        12543,
        12590,
        12631,
        12745,
        13029,
        13138,
        13245,
        13342,
        13351,
        13412,
        13506,
        13729,
        13987,
        14099,
        14461,
        14532,
        14770,
        15086,
        15450,
        15560,
        15691,
        15738,
        16150,
    ]
    assert len(queries) == len({query >> 4 for query in queries}) == 42
    assert all(1 << 13 <= query < 1 << 14 for query in queries)
    sources = query_sources(field)[0] + extra_query_sources(field, blocks)
    assert len(sources) == 66300
    collapsed = set()
    for polynomial in sources:
        coefficients = {}
        for index, value in polynomial:
            if index < 1 << 14:
                index &= (1 << 13) - 1
                coefficients[index] = coefficients.get(index, 0) ^ value
        polynomial = tuple(sorted((index, value) for index, value in coefficients.items() if value))
        if polynomial:
            collapsed.add(polynomial)
    assert len(collapsed) == 2688
    assert all(index & 63 >= 16 for polynomial in collapsed for index, _ in polynomial)
    columns = [sum(value << (64 * index) for index, value in polynomial) for polynomial in collapsed]
    assert len(binary_basis(columns)) == 2688
    del columns
    print("The complete low-band noise code has binary dimension 2688; its coefficient support misses the private pointer direction.", flush=True)

    private = [(12288 + index, field.kmul(1 << index, 3)) for index in range(8)]
    payload = [len(queries), 0, *queries, 0]
    for polynomials in (sources, [private]):
        payload.append(len(polynomials))
        for polynomial in polynomials:
            payload.append(len(polynomial))
            payload.extend(value for term in polynomial for value in term)
            payload.append(0)
    result = subprocess.run(
        ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--query-map-fiber-certificate"],
        input=" ".join(map(str, payload)),
        text=True,
        capture_output=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
    assert "RANK 2687 2688\n" in result.stdout
    separating = [line for line in result.stdout.splitlines() if line.startswith("OUTSIDE 0 ")]
    assert len(separating) == 1
    dual = {int(query): int(weight, 16) for query, weight in (term.split(":") for term in separating[0].split()[2:])}
    assert set(dual) == set(queries) and all(dual.values())
    print("Scattered 42-query rank 2687/2688: the unique nonzero dual separates the private pointer and uses every query.", flush=True)
    print("Every proper subset of this raw query set has full rank; no two points lie in the same 16-point coset.", flush=True)
    for rate, bits in enumerate((266, 358, 432, 501), 1):
        count = verifier.derive_config(28, rate).queries[0]
        bound = Fraction(comb(count, 42), 1 << (42 * (9 + rate)))
        assert bound < Fraction(1, 1 << bits)
        print(
            f"Rate {rate}: 42 or more queries anywhere in the low band have probability below 2^-{bits}; smaller supports remain unbounded.",
            flush=True,
        )


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
    assert [polynomial for polynomial, _ in result if polynomial] == extra_query_sources(field, blocks)
    return result


def decomposition_certificate(field, verifier, old, extra):
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    cv1 = counts.index(verifier.BLAKE2S_COLUMNS.index("cnt_cv1"))
    out0 = counts.index(verifier.BLAKE2S_COLUMNS.index("cnt_out0"))
    mask = (1 << 192) - 1

    def unpack(prefix):
        return [(prefix >> (192 * index)) & mask for index in range(31)]

    def pack(values):
        return sum(value << (192 * index) for index, value in enumerate(values))

    high_factors = novel_factors(field, 19, 262144)
    high_weights = {0: 1}

    def high_weight(index):
        if index >= 1 << 19:
            return 0
        if index not in high_weights:
            bit = index.bit_length() - 1
            high_weights[index] = field.kmul(high_factors[bit], high_weight(index ^ (1 << bit)))
        return high_weights[index]

    noncount_size = 8 * 384 + 4 * 1279
    other_sources = [source for index, source in enumerate(old[noncount_size:]) if index % 10 != cv1]
    other_sources.extend(extra[out0::10])
    other_counts = []
    for polynomial, prefix in other_sources:
        values = unpack(prefix)
        assert not any(values[:9]) and values[9 + cv1] == 0
        assert all(values[19 + 3 * child] == field.mul(2, values[20 + 3 * child]) for child in range(4))
        assert all(position >= 1 << 18 for position, _ in polynomial)
        projected_prefix = pack(
            [
                *[values[9 + number] for number in range(10) if number != cv1],
                *[values[20 + 3 * child + side] for child in range(4) for side in range(2)],
            ]
        )
        raw = 0
        for position, delta in polynomial:
            raw ^= field.kmul(delta, high_weight(position & ~31)) << (64 * (position & 31))
        other_counts.append(projected_prefix | (raw << (17 * 192)))
    assert len(binary_basis(other_counts)) == 17 * 192 + 32 * 64 == 5312
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
    print("Split-region certificate: ranks 5312, 1216 and 2496, with every required zero projection and child-plane invariance checked.", flush=True)


def sampled_rank(field, blocks):
    for query in (8192, 12288, 16384, 65536, 262128, 262144, 393216, 524272):
        weights = field.novel(14, query)
        values = [field.kmul(3, weights[left] ^ weights[right]) for left, right in blocks]
        power = 1
        for index in range(len(values)):
            values[index] = field.kmul(values[index], power)
            power = field.kmul(power, 1 << 32)
        assert len(binary_basis(values)) == 64
    print("Sampled low-bank scalar maps have rank 64; the native run checks every claimed coset.", flush=True)


def invariant_rank(field, blocks):
    from zk_flock_multicoset_audit import query_sources

    for query in (262144, 393216, 524272):
        factors = novel_factors(field, 19, query)
        weights = {0: 1}

        def weight(index, weights=weights, factors=factors):
            if index >= 1 << 19:
                return 0
            if index not in weights:
                bit = index.bit_length() - 1
                weights[index] = field.kmul(factors[bit], weight(index ^ (1 << bit)))
            return weights[index]

        def projections(polynomial):
            invariant, raw, quotient = 0, 0, 0
            for index, value in polynomial:
                invariant ^= field.kmul(value, weight(index & ~15)) << (64 * (index & 3))
                coefficient = field.kmul(value, weight(index & ~31))
                low = index & 31
                slot = 4 * (low & 3) + (((low >> 2) & 1) if low < 16 else 2 + ((low >> 3) & 1))
                raw ^= coefficient << (64 * low)
                quotient ^= coefficient << (64 * slot)
            return invariant, raw, quotient

        old = [projections(polynomial) for polynomial in query_sources(field)[0]]
        new = [projections(polynomial) for polynomial in extra_query_sources(field, blocks)]
        assert not any(invariant or quotient for invariant, _, quotient in old)
        assert len(binary_basis([raw for _, raw, _ in old])) == 1024
        assert len(binary_basis([invariant for invariant, _, _ in new])) == 256
        assert len(binary_basis([quotient for _, _, quotient in new])) == 1024
    print("Old 32-point kernel rank 1024 and balanced quotient rank 1024, with all old invariants fixed, at the tested native points.", flush=True)


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
    parser.add_argument("--scattered", action="store_true", help="check the complete low-band noise code and its dispersed minimal support")
    arguments = parser.parse_args()
    blocks = positions()
    verifier = verifier_module()
    field = Tower(64, verifier)
    if arguments.scattered:
        scattered_certificate(field, verifier, blocks)
        raise SystemExit
    sampled_rank(field, blocks)
    terminal_rank(field, blocks)
    combined_error()
    if arguments.full:
        build(verifier, blocks)
        cluster_certificate(field, verifier, blocks)
        scattered_certificate(field, verifier, blocks)
        invariant_rank(field, blocks)
    subprocess.run(
        ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--lowbank-certificate"],
        input=" ".join(str(value) for block in blocks for value in block),
        text=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
    subprocess.run(
        ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--balanced-quotient-certificate"],
        input=" ".join(str(value) for block in blocks for value in block),
        text=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
