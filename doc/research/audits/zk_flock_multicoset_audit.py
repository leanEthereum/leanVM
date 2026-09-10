"""Exact coset certificates, a six-query obstruction and the full initial query matrix."""

import argparse
import subprocess
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, prod
from pathlib import Path
from random import Random

from zk_flock_children_audit import (
    DENSE_FIXED,
    PC_SUPPORT,
    PROGRAM,
    SHORT_SUPPORT,
    build,
    error_bound,
    pair,
)
from zk_flock_coset_audit import novel_factors, probability_all_hit, reordered_index
from zk_flock_pair_opening_audit import blake_bus_forms, evaluate, lane_count_columns
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import RightInverse, Tower, kdot, verifier_module
from zk_stacked_audit import binary_basis
from zk_three_point_audit import three_point_error


def determinant3(field, rows):
    result = 0
    for order in permutations(range(3)):
        result ^= field.kmul(rows[0][order[0]], field.kmul(rows[1][order[1]], rows[2][order[2]]))
    return result


def normal(field, rows):
    return [determinant3(field, [[row[column] for column in range(4) if column != omitted] for row in rows]) for omitted in range(4)]


def block_dual(field, coset):
    assert coset & 15 == 0
    evaluation = [field.novel(4, coset + offset) for offset in range(16)]
    inverse = RightInverse(field, evaluation).inverse
    dual = []
    for query in range(16):
        dual.append(
            [inverse[child][query] ^ inverse[child + 4][query] ^ inverse[child + 8][query] ^ inverse[child + 12][query] for child in range(4)]
        )
    assert len(field.pivots(dual)) == 4
    for child in range(4):
        for row in range(16):
            expected = int(row & 3 == child)
            assert kdot(field, [entry[child] for entry in dual], [entry[row] for entry in evaluation]) == expected
    return dual


def dual_formula(field, coset):
    result = []
    for offset in range(16):
        novel = field.novel(4, coset + offset)
        result.append([novel[12] ^ novel[13] ^ novel[14] ^ novel[15], novel[12] ^ novel[14], novel[12] ^ novel[13], novel[12]])
    return result


def polynomial_certificate(field):
    for coset in (0, 16):
        assert block_dual(field, coset) == dual_formula(field, coset)
    print("The 64 degree-at-most-30 dual identities hold at all 32 points of U5, so they are polynomial identities.", flush=True)


def support_certificate():
    reference = None
    for kind, fixed, bit in (("count", 80, 3), ("wide", 96, 2)):
        for child in range(4):
            for side in range(2):
                support = Counter()
                for index in DENSE_FIXED:
                    left, _ = map(reordered_index, pair(kind, child, index))
                    if (left >> bit) & 1 == side:
                        support[(left & ~15) ^ fixed] += 1
                assert len(support) == 640 and set(support.values()) == {1}
                if reference is None:
                    reference = support
                assert support == reference
    print("Both halves of every core and wider bank share the same 640 high-coordinate weights, up to nonzero sector factors.", flush=True)


def binary_coset_certificate(field, coset):
    assert 1 << 18 <= coset < 1 << 19 and coset & 15 == 0
    factors = novel_factors(field, 18, coset)

    def weight(index):
        value = 3
        for bit in range(4, 18):
            if index >> bit & 1:
                value = field.kmul(value, factors[bit])
        return value

    directions = []
    for kind in ("count", "wide"):
        for child in range(4):
            for index in DENSE_FIXED:
                left, right = map(reordered_index, pair(kind, child, index))
                value = weight(left)
                assert left >> 4 == right >> 4
                directions.append((value << (64 * (left & 15))) ^ (value << (64 * (right & 15))))
    assert len(binary_basis(directions)) == 12 * 64
    print(f"Coset {coset}: the actual binary count source fills precisely the 768-bit, four-invariant noise space.", flush=True)


def shortest_invariant(field, coset):
    dual = block_dual(field, coset)
    assert dual == dual_formula(field, coset)
    best = None
    for triple in combinations(range(16), 3):
        functional = normal(field, [dual[index] for index in triple])
        if not any(functional):
            continue
        weights = [kdot(field, functional, column) for column in dual]
        support = [index for index, value in enumerate(weights) if value]
        if best is None or len(support) < len(best[0]):
            best = support, functional, weights
    assert best is not None
    support, functional, weights = best
    if coset >= 16:
        assert len(support) == 13
    pointer_seen = bool(kdot(field, functional, [1 << child for child in range(4)]))
    if 1 << 18 <= coset < 1 << 19:
        private = {reordered_index((96 << 11) + index): field.kmul(1 << index, 3) for index in range(8)}
        observed = kdot(field, weights, [evaluate(field, private, coset + offset) for offset in range(16)])
        factor = evaluate(field, {12288: field.kmul(3, 17)}, coset)
        assert factor and observed == field.kmul(factor, kdot(field, functional, [1 << child for child in range(4)]))
    if coset == 1 << 18:
        assert pointer_seen
    print(
        f"Coset {coset}: shortest coefficient-sum invariant uses {len(support)} queries {support}; detects the private-pointer direction: {pointer_seen}.",
        flush=True,
    )
    return best


def query_event_bound(verifier):
    bounds = []
    for rate, bits in enumerate((174, 201, 222, 241), 1):
        queries = verifier.derive_config(28, rate).queries[0]
        bound = Fraction((1 << 14) * comb(16, 13) * prod(range(queries - 12, queries + 1)), 1 << (13 * (22 + rate)))
        assert bound < Fraction(1, 1 << bits)
        bounds.append(bound)
        print(f"Rate {rate}: probability of thirteen distinct queried points in any sixteen-point coset inside A is below 2^-{bits}.", flush=True)
    return max(bounds)


def fiber_error_budget(verifier):
    queries = verifier.derive_config(28, 1).queries[0]
    domain = 1 << 23
    assert 1 - Fraction(domain - 1, domain) ** queries > Fraction(1, 1 << 16)
    remainder = three_point_error() + Fraction(4187, 1 << 192) + joint_root_bound()
    assert remainder + Fraction(1, 1 << 140) < Fraction(1, 1 << 139)
    print(
        "A compatible repaired source with query-fiber defect at most 2^-140 would give joint error below 2^-139; the current source fails this premise.",
        flush=True,
    )


def six_query_obstruction(field, verifier):
    queries = list(range(12290, 12296))
    masks = [0x703E981548C0890A] * 2 + [0xAD899468BF200C90] * 2 + [0x3F945B0914A01D51] * 2
    weights = [field.novel(14, query) for query in queries]
    all_sources, _ = query_sources(field)
    sources = {tuple((index, value) for index, value in polynomial if index < 1 << 14) for polynomial in all_sources}
    sources.discard(())
    assert len(sources) == 956

    def observation(polynomial):
        result = []
        for row in weights:
            value = 0
            for index, coefficient in polynomial:
                value ^= field.kmul(row[index], coefficient)
            result.append(value)
        return result

    def test(values):
        return sum((value & mask).bit_count() for value, mask in zip(values, masks)) & 1

    columns = [observation(polynomial) for polynomial in sources]
    assert not any(test(column) for column in columns)
    assert len(binary_basis([sum(value << (64 * slot) for slot, value in enumerate(column)) for column in columns])) == 382
    private = [(12288 + index, field.kmul(1 << index, 3)) for index in range(8)]
    assert test(observation(private)) == 1
    print(
        "Exact six-query obstruction: rank 382/384; the pinned binary test annihilates every current source and detects the valid private-pointer pair.",
        flush=True,
    )
    for rate, bits in enumerate((93, 105, 114, 123), 1):
        count = verifier.derive_config(28, rate).queries[0]
        probability = probability_all_hit(1 << (22 + rate), count, 6)
        assert probability / 2 > Fraction(1, 1 << bits)
        print(f"Rate {rate}: every common simulator for this fixed-completion source has error greater than 2^-{bits}.", flush=True)


def query_sources(field, lane_blocks=5):
    assert lane_blocks in (5, 7)
    geometric, value = [], 3
    for _ in DENSE_FIXED:
        geometric.append(value)
        value = field.kmul(value, 4)
    result, labels = [], []
    for kind in ("count", "wide"):
        for child in range(4):
            for number, index in enumerate(DENSE_FIXED):
                left, right = map(reordered_index, pair(kind, child, index))
                for block in range(lane_blocks):
                    difference = geometric[number] if block == lane_blocks - 1 else 3
                    result.append([(block * (1 << 18) + endpoint, difference) for endpoint in (left, right)])
                    labels.append((kind, child, number, block))
    for child in range(4):
        for number, index in enumerate(PC_SUPPORT):
            left, right = map(reordered_index, pair("pc", child, index))
            result.append([(block * (1 << 18) + endpoint, 3) for block in range(lane_blocks - 1) for endpoint in (left, right)])
            labels.append(("pc", child, number, None))
    for number, index in enumerate(SHORT_SUPPORT):
        left, right = map(reordered_index, pair("operand", 7, index))
        result.append([((lane_blocks - 1) * (1 << 18) + endpoint, geometric[number]) for endpoint in (left, right)])
        labels.append(("operand", 7, number, None))
    assert len(result) == 8 * 1280 * lane_blocks + 4 * 1279 + 384
    return result, labels


def source_certificate(verifier, sources, labels, library_groups=None, code_log=11):
    library, groups = build(verifier, True) if library_groups is None else library_groups
    columns = lane_count_columns(verifier, code_log)
    for polynomial, (kind, child, number, block) in zip(sources, labels):
        _, first, second, logical_left, logical_right = groups[kind, child][number]
        a, b = library.rows[first][1], library.rows[second][1]
        expected = []
        for selected, column in enumerate(columns):
            difference = int(a[column] + b[column])
            if difference and (block is None or block == selected):
                expected.extend((selected * (1 << 18) + reordered_index(logical), difference) for logical in (logical_left, logical_right))
        assert polynomial == expected
    for child in range(7):
        for _, first, second, _, _ in groups["operand", child]:
            assert all(library.rows[first][1][column] == library.rows[second][1][column] for column in columns)
    print(f"All {len(sources)} nonzero lane-source directions agree with complete valid cycles; the other operand swaps vanish.", flush=True)


def joint_query_sources(field, verifier, seed, library_groups=None, code_log=11):
    library, groups = build(verifier, True) if library_groups is None else library_groups
    rng = Random(seed)
    terminal = [field.random(rng) for _ in range(18)]
    parent = [verifier.E(*field.coords(field.random(rng))) for _ in range(24)]
    alphas = [verifier.E(*field.coords(field.random(rng))) for _ in range(4)]
    forms, _ = blake_bus_forms(verifier, [verifier.ZERO, verifier.ZERO, *parent], alphas, code_log)
    columns = verifier.BLAKE2S_COLUMNS
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    selected = [columns.index(name) for name in (*PROGRAM, "fp")] + list(counts)
    lane_columns = lane_count_columns(verifier, code_log)
    parent_weights = field.eq([int(value) for value in parent[:16]])
    terminal_weights = field.eq(terminal)
    matrix = [[int(form.terms.get((column,), verifier.ZERO)) for column in counts] for form in forms]
    result = []
    for (kind, child), group in groups.items():
        for _, first, second, logical_left, logical_right in group:
            a, b = library.rows[first][1], library.rows[second][1]
            left, right = map(reordered_index, (logical_left, logical_right))
            terminal_weight = terminal_weights[logical_left] ^ terminal_weights[logical_right]
            child_weights = [0] * 4
            for physical in (left, right):
                child_weights[physical & 3] ^= parent_weights[physical >> 2]
            if kind in ("count", "wide"):
                for number, column in enumerate(counts):
                    difference = int(a[column] + b[column])
                    prefix = field.mul(terminal_weight, difference) << ((9 + number) * 192)
                    count_delta = field.mul(child_weights[child], difference)
                    prefix |= sum(field.mul(matrix[side][number], count_delta) << ((19 + 3 * child + side) * 192) for side in range(3))
                    polynomial = []
                    if column in lane_columns:
                        block = lane_columns.index(column)
                        polynomial = [(block * (1 << 18) + endpoint, difference) for endpoint in (left, right)]
                    result.append((polynomial, prefix))
            else:
                differences = [int(a[column] + b[column]) for column in selected]
                metadata = [field.mul(terminal_weight, value) for value in differences]
                form_delta = [int(form.evaluate(a.__getitem__) + form.evaluate(b.__getitem__)) for form in forms]
                children = [field.mul(weight, value) for weight in child_weights for value in form_delta]
                prefix = sum(value << (192 * index) for index, value in enumerate([*metadata, *children]))
                polynomial = [
                    (block * (1 << 18) + endpoint, int(a[column] + b[column]))
                    for block, column in enumerate(lane_columns)
                    if a[column] != b[column]
                    for endpoint in (left, right)
                ]
                result.append((polynomial, prefix))
    assert len(result) == 110588
    assert Counter(tuple(polynomial) for polynomial, _ in result if polynomial) == Counter(
        tuple(polynomial) for polynomial in query_sources(field, len(lane_columns))[0]
    )
    print(
        "All 110588 legal metadata bits retain nineteen terminal fields, twelve actual GKR children and the complete lane-59 query source.",
        flush=True,
    )
    return result


def query_map(field, verifier, arguments):
    rng = Random(arguments.seed)
    count = verifier.derive_config(28, arguments.rate).queries[0]
    queries = arguments.points if arguments.points is not None else [rng.randrange(1 << (22 + arguments.rate)) for _ in range(count)]
    if arguments.singletons:
        assert not arguments.joint_boundary
        queries = list(range(*arguments.singletons))
    if arguments.include_low:
        queries = [*queries, 0, 1, 32, 64, 4096, 8191]
    if arguments.region == "A":
        queries = [query for query in queries if 1 << 18 <= query < 1 << 19]
    queries = sorted(set(queries))
    assert queries, "no query in the selected region"
    if arguments.joint_boundary:
        sources = joint_query_sources(field, verifier, arguments.seed + 1)
    else:
        sources, labels = query_sources(field)
        if arguments.source_validity:
            source_certificate(verifier, sources, labels)
        sources = [(polynomial, 0) for polynomial in sources]
    if arguments.lowbank:
        from zk_flock_lowbank_audit import (
            decomposition_certificate,
            extra_joint_sources,
            extra_query_sources,
            positions,
        )

        blocks = positions()
        if arguments.joint_boundary:
            extra = extra_joint_sources(field, verifier, arguments.seed + 1, blocks)
            decomposition_certificate(field, verifier, sources, extra, arguments.public_prefix_log or 12)
            sources += extra
        else:
            sources += [(polynomial, 0) for polynomial in extra_query_sources(field, blocks)]
    if arguments.public_prefix_log is not None:
        assert arguments.joint_boundary and arguments.lowbank and not arguments.singletons
        from zk_flock_lowbank_audit import public_prefix_sources

        sources, public_prefix_bits = public_prefix_sources(sources, arguments.public_prefix_log)
    rng.shuffle(sources)
    pointer = [(reordered_index((96 << 11) + index), field.kmul(1 << index, 3)) for index in range(8)]
    alias = [(block * (1 << 18) + reordered_index((96 << 11) + 4 + index), field.kmul(1 << index, 17)) for block in range(4) for index in range(4)]
    prefix_words = 93 if arguments.joint_boundary else 0
    if arguments.public_prefix_log is not None:
        prefix_words += (public_prefix_bits + 63) // 64
    if arguments.singletons:
        bound = 1 << max(queries).bit_length()
        sources = list({(tuple((index, value) for index, value in polynomial if index < bound), prefix) for polynomial, prefix in sources})
        sources = [(polynomial, prefix) for polynomial, prefix in sources if polynomial or prefix]
        print(f"Exact prefix truncation leaves {len(sources)} distinct nonzero binary source polynomials.", flush=True)
    public = [index for index, query in enumerate(queries) if query < 1 << 13]
    payload = [len(queries), prefix_words, *queries, len(public), *public]
    if arguments.public_prefix_log is not None:
        payload.extend([prefix_words - 93, *range(93, prefix_words)])
    for polynomials in (sources, [] if arguments.joint_boundary else [(pointer, 0), (alias, 0)]):
        payload.append(len(polynomials))
        for polynomial, prefix in polynomials:
            payload.append(len(polynomial))
            payload.extend(value for term in polynomial for value in term)
            words = [(word, (prefix >> (64 * word)) & field.mask) for word in range(prefix_words) if (prefix >> (64 * word)) & field.mask]
            payload.append(len(words))
            payload.extend(value for term in words for value in term)
    mode = "Exhaustive singleton" if arguments.singletons else ("Explicit query" if arguments.points is not None else "Sampled query")
    print(f"{mode} diagnostic: rate {arguments.rate}, seed {arguments.seed}, region {arguments.region}, {len(queries)} distinct queries.", flush=True)
    certificate = "--query-singleton-certificate" if arguments.singletons else "--query-map-fiber-certificate"
    if arguments.public_prefix_log is not None:
        certificate = "--query-prefix-fiber-certificate"
    subprocess.run(
        [
            "cargo",
            "run",
            "--release",
            "-p",
            "lean_vm",
            "--example",
            "zk_flock_pair_opening_audit",
            "--",
            certificate,
        ],
        input=" ".join(map(str, payload)),
        text=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coset", type=int, nargs="*", default=[1 << 18])
    parser.add_argument("--query-map", action="store_true", help="diagnose the complete current lane-59 binary source at selected queries")
    parser.add_argument("--rate", type=int, choices=range(1, 5), default=1)
    parser.add_argument("--seed", type=int, default=601)
    parser.add_argument("--region", choices=("full", "A"), default="full")
    parser.add_argument("--points", type=int, nargs="+", help="use these explicit query indices instead of a sampled tape")
    parser.add_argument("--source-validity", action="store_true", help="compare every source polynomial with the complete valid library")
    parser.add_argument("--joint-boundary", action="store_true", help="also retain all nineteen terminal metadata fields and twelve GKR children")
    parser.add_argument("--include-low", action="store_true", help="append fixed low query points to check the public-prefix fiber")
    parser.add_argument("--lowbank", action="store_true", help="include the disjoint 3840-row long-chain low-coordinate bank")
    prefix_group = parser.add_mutually_exclusive_group()
    prefix_group.add_argument("--public-prefix9", dest="public_prefix_log", action="store_const", const=9, help="retain the 512-point public prefix")
    prefix_group.add_argument(
        "--public-prefix-log", type=int, choices=range(9, 13), help="retain the complete public prefix through its coefficient bits"
    )
    parser.add_argument(
        "--singletons", type=int, nargs=2, metavar=("START", "END"), help="exhaustively test individual points in this half-open interval"
    )
    arguments = parser.parse_args()
    verifier = verifier_module()
    field = Tower(64, verifier)
    if arguments.query_map:
        query_map(field, verifier, arguments)
        raise SystemExit
    polynomial_certificate(field)
    support_certificate()
    fiber_error_budget(verifier)
    six_query_obstruction(field, verifier)
    total = error_bound(128) + query_event_bound(verifier)
    assert total < Fraction(1, 1 << 155)
    assert total + joint_root_bound() < Fraction(1, 1 << 151)
    for coset in arguments.coset:
        shortest_invariant(field, coset)
        if 1 << 18 <= coset < 1 << 19:
            binary_coset_certificate(field, coset)
