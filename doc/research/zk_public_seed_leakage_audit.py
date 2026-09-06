"""Public-seed decoupling with nonlinear controls, not a simulator for those controls."""

from fractions import Fraction
from functools import reduce
from itertools import islice, pairwise, product
from operator import mul
from random import Random

from zk_bus_boundary_audit import final_evaluation
from zk_bytecode_frontier_audit import BANKS, CODE_BASES
from zk_bytecode_public_library_audit import (
    FRAME_BASE,
    MEMORY_FRAME,
    MEMORY_PC,
    set_library,
)
from zk_count_children_audit import SPARSE
from zk_gkr_first_packet_audit import fingerprint
from zk_pcs_audit import verifier_module

BITS, FIELDS = 3328, 12


def distance(counts, order, alphabet, samples):
    marginal = [sum(counts[root * alphabet + y] for root in range(order)) for y in range(alphabet)]
    return Fraction(
        sum(abs(order * counts[root * alphabet + y] - marginal[y]) for root in range(order) for y in range(alphabet)),
        2 * order * samples,
    )


def nonlinear_seed_bound():
    n, order = 6, 3
    bits = tuple(product((0, 1), repeat=n))
    observations = (
        (4, [a[0] * a[1] + 2 * a[2] * a[3] for a in bits]),
        (7, [sum(a) for a in bits]),
    )
    for seed_weights in ((1, 1, 1), (2, 1, 1)):
        averages, total = [Fraction() for _ in observations], sum(seed_weights) ** n
        for seed in product(range(order), repeat=n):
            roots = [sum(h * a for h, a in zip(seed, vector, strict=True)) % order for vector in bits]
            seed_probability = Fraction(reduce(mul, (seed_weights[value] for value in seed), 1), total)
            for index, (alphabet, values) in enumerate(observations):
                counts, relabeled, shifted = [[0] * (order * alphabet) for _ in range(3)]
                for root, y in zip(roots, values, strict=True):
                    counts[root * alphabet + y] += 1
                    relabeled[root * alphabet + (y + sum(seed)) % alphabet] += 1
                    shifted[((root + y + sum(seed)) % order) * alphabet + y] += 1
                delta = distance(counts, order, alphabet, len(bits))
                assert distance(relabeled, order, alphabet, len(bits)) == delta
                assert distance(shifted, order, alphabet, len(bits)) == delta
                averages[index] += seed_probability * delta**2
            dependent = [0] * order**2
            for root in roots:
                dependent[root * order + root] += 1
            assert distance(dependent, order, order, len(bits)) == Fraction(order - 1, order)
        bias = Fraction(seed_weights[0] - seed_weights[1], sum(seed_weights))
        for average, (alphabet, _) in zip(averages, observations, strict=True):
            bound = Fraction(alphabet * (order - 1), 4) * ((1 + bias) / 2) ** n
            assert average <= bound < 1
        invalid_bound = Fraction(order * (order - 1), 4) * ((1 + bias) / 2) ** n
        assert invalid_bound < Fraction(order - 1, order) ** 2
    print("Exact nonlinear side-information bounds pass for uniform/biased public seeds and seed-dependent relabeling", flush=True)
    print("Retaining the seed-dependent product itself has distance 2/3 for every seed and contradicts the inapplicable bound", flush=True)


def cross_bank_seed_bound():
    order, per_bank, alphabet = 3, 4, 4
    bits = tuple(product((0, 1), repeat=per_bank))
    seeds = tuple(product(range(order), repeat=per_bank))
    roots = {seed: [sum(h * a for h, a in zip(seed, vector, strict=True)) % order for vector in bits] for seed in seeds}
    for seed_weights in ((1, 1, 1), (2, 1, 1)):
        average, total = Fraction(), sum(seed_weights) ** (2 * per_bank)
        for left, right in product(seeds, repeat=2):
            counts = [0] * (order**2 * alphabet)
            for i, a in enumerate(bits):
                for j, other in enumerate(bits):
                    y = a[0] * other[0] + 2 * a[1] * other[1]
                    root = order * roots[left][i] + roots[right][j]
                    counts[root * alphabet + y] += 1
            delta = distance(counts, order**2, alphabet, len(bits) ** 2)
            average += Fraction(reduce(mul, (seed_weights[value] for value in (*left, *right)), 1), total) * delta**2
        bias = Fraction(seed_weights[0] - seed_weights[1], sum(seed_weights))
        bound = Fraction(alphabet, 4) * ((1 + (order - 1) * ((1 + bias) / 2) ** per_bank) ** 2 - 1)
        assert average <= bound < 1
    print("Exact two-bank averaging passes with nonlinear side information coupling the banks", flush=True)


def table_products(v, library, opcode, side, e, beta):
    return tuple(
        reduce(
            mul,
            (
                beta + v.dot(e[: len(block)], [form.evaluate(row.__getitem__) for form in block])
                for row_opcode, row in library.rows
                if row_opcode == opcode
            ),
            v.ONE,
        )
        for block in getattr(v.TABLES[opcode].flushes, side)
    )


def control_classification(v):
    rng = Random(174)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    points = [[sample() for _ in range(20)] for _ in range(2)]
    support = (0, 1, 64, 2048)
    seeds = [[[[0] * 3 for _ in range(2)] for _ in support]]
    seeds += [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support] for _ in range(2)]
    bit_vectors = ((0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 0, 0), (1, 1, 1, 1), (0, 1, 0, 1))
    controls, excluded_ratios, jump_rows = [], [], []
    for words in seeds:
        per_seed, excluded, reference_images, rows = [], [], None, []
        for bits in bit_vectors:
            library, indices = set_library(v, support, words, bits, compact=True)
            rows.append([tuple(row) for opcode, row in library.rows if opcode == v.OP_JUMP])
            if reference_images is None:
                reference_images = library.images
            assert library.images == reference_images
            jump = [table_products(v, library, v.OP_JUMP, side, e, beta) for side in ("push", "pull")]
            sets = [table_products(v, library, v.OP_SET, side, e, beta) for side in ("push", "pull")]
            assert len(jump[0]) == len(jump[1]) == 5 and len(sets[0]) == len(sets[1]) == 3
            assert sets[0][0] == jump[1][0] and sets[1][0] == jump[0][0]
            counters = tuple(final_evaluation(v, library, kind, indices[kind], point) for kind, point in zip(("memory", "code"), points, strict=True))
            per_seed.append((*jump[0], *jump[1], *counters))
            memory = reduce(
                mul,
                (
                    fingerprint(v, e, beta, v.SEP_MEM, address, v.GEN ** library.reads["memory", address], payload)
                    for address, payload in library.images["memory"].items()
                ),
                v.ONE,
            )
            excluded.append((memory, sets[0][1], sets[1][1], sets[0][2], sets[1][2]))
        assert all(len(view) == FIELDS for view in per_seed)
        controls.append(per_seed)
        jump_rows.append(rows)
        excluded_ratios.append(tuple(value / baseline for value, baseline in zip(excluded[1], excluded[0], strict=True)))
    assert controls[0] == controls[1] == controls[2]
    assert jump_rows[0] == jump_rows[1] == jump_rows[2]
    assert any(a + b + c + d != v.ZERO for a, b, c, d in zip(*controls[0][:4], strict=True))
    assert all(len({int(row[column]) for row in excluded_ratios}) > 1 for column in range(len(excluded_ratios[0])))
    print("Actual valid-cycle controls: ten JUMP products plus two counter evaluations are seed-independent and not jointly affine", flush=True)
    print(
        "SET state products repeat reversed JUMP state products; memory finalization and SET payload-product ratios depend on the public seeds",
        flush=True,
    )


def reservations(v):
    support = range(BITS)
    assert set(SPARSE) <= set(support)
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    bus, count = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22 and layout.stack_log == 24 and bus == v.bus_layout((0, 20, 20), layout.pull)
    assert bus.framework[2].index >> 18 == 4 and bus.framework[2].variables == 20
    assert all(place.index >> 20 == (place.index + (1 << place.variables) - 1) >> 20 for place in count.tables)
    for opcode, expected in ((v.OP_MUL, [8, 9, 10, 11, 12]), (v.OP_JUMP, [13, 13, 14, 14, 15]), (v.OP_SET, [15, 15, 15])):
        placements = [place for block, place in zip(layout.push, bus.tables, strict=True) if block.owner == opcode]
        assert [place.index >> 18 for place in placements] == expected
        assert all(place.index >> 18 == (place.index + (1 << place.variables) - 1) >> 18 for place in placements)
    counter_slots = {8 * ((bank << 12) + s) + low for bank in range(4) for s in SPARSE for low in range(8)}
    occupied = counter_slots | set(range(1536, 1544)) | set(range(60000, 60049))
    needed = 2 * BANKS * BITS + 2 * len(SPARSE)
    assert len(list(islice((row for row in range(1 << 17) if row not in occupied), needed))) == needed
    assert 2 * BANKS * BITS == 26624 < 1 << layout.table_log_heights[v.OP_SET]
    frames = [
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (1 << 17, (1 << 17) + 8 * 128),
        (3 << 16, (3 << 16) + 48 * 128),
        (FRAME_BASE, FRAME_BASE + 8 * BANKS * BITS),
        (1 << 19, (1 << 19) + 32),
        (MEMORY_FRAME, MEMORY_FRAME + (1 << 15)),
    ]
    assert all(left[1] <= right[0] for left, right in pairwise(frames)) and frames[-1][1] < 1 << 20
    holes = [(base, base + (1 << 14)) for base in CODE_BASES]
    assert 4096 + 2 * 5 * 4 * len(SPARSE) < holes[0][0]
    assert all(not (a <= pc < b) for a, b in holes for pc in (2048, 2049, 32768, 32769, MEMORY_PC))
    assert all(base <= base + 4 * s + offset < end for base, end in holes for s in support for offset in range(4))
    assert all((base + 4 * s + offset) >> 18 == bank for bank, base in enumerate(CODE_BASES) for s in support for offset in range(4))
    print("Four larger banks fit SET height 15 with unchanged frontier ownership and disjoint code, frame and JUMP reservations", flush=True)


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    bias = Fraction(4 * size, (base**2 - 2) ** 2)
    assert bias < Fraction(1, 1 << 61)
    term = (size - 2) * ((1 + bias) / 2) ** BITS
    assert term < Fraction(1, 4)
    mean_square_upper = 2 * size**FIELDS * term
    assert mean_square_upper < Fraction(1, 1 << 830)
    threshold, exceptional = Fraction(1, 1 << 160), Fraction(1, 1 << 255)
    assert Fraction(1, 1 << 415) / threshold == exceptional
    exclusions = Fraction((1 << 20) + 8 * BANKS * BITS + 8, size) + Fraction(base**2, (size - 2) ** 2)
    assert threshold + exclusions < Fraction(1, 1 << 159)
    print("Rational bounds: mean decoupling below 2^-415; threshold 2^-160 except for fewer than a 2^-255 fraction of libraries", flush=True)
    print("Including rank and zero exclusions gives decoupling below 2^-159; the actual control law is retained, not simulated", flush=True)


if __name__ == "__main__":
    nonlinear_seed_bound()
    cross_bank_seed_bound()
    verifier = verifier_module()
    control_classification(verifier)
    reservations(verifier)
    concrete_bound()
