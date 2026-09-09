"""Exact single-coset noise and its thirteen-query threshold, not a multi-coset proof."""

import argparse
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, prod

from zk_flock_children_audit import DENSE_FIXED, error_bound, pair
from zk_flock_coset_audit import novel_factors, reordered_index
from zk_flock_pair_opening_audit import evaluate
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import RightInverse, Tower, kdot, verifier_module
from zk_stacked_audit import binary_basis


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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coset", type=int, nargs="*", default=[1 << 18])
    arguments = parser.parse_args()
    verifier = verifier_module()
    field = Tower(64, verifier)
    polynomial_certificate(field)
    support_certificate()
    total = error_bound(128) + query_event_bound(verifier)
    assert total < Fraction(1, 1 << 155)
    assert total + joint_root_bound() < Fraction(1, 1 << 151)
    for coset in arguments.coset:
        shortest_invariant(field, coset)
        if 1 << 18 <= coset < 1 << 19:
            binary_coset_certificate(field, coset)
