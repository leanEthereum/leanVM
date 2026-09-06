"""Setup-dependent bytecode residual hiding, not fixed-library or full VM ZK."""

from fractions import Fraction
from functools import reduce
from itertools import islice, pairwise, product
from operator import mul
from random import Random

from zk_bus_boundary_audit import final_evaluation
from zk_bus_packet_audit import weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE
from zk_gkr_first_packet_audit import fingerprint
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

BITS, CODE_BASE, FRAME_BASE = 1024, 1 << 16, 1 << 18
MEMORY_PC, MEMORY_FRAME = 5 << 14, 3 << 18
SUPPORT = tuple(sorted({*SPARSE, *islice((s for s in range(4096) if s not in set(SPARSE)), BITS - len(SPARSE))}))


def public_seed_mixing():
    n, order, dimension = 6, 3, 4
    for coefficients in ((1, 2, 3, 1, 2, 3), (1,) * n):
        for seed_weights in ((1, 1, 1), (2, 1, 1)):
            average_squared, total = Fraction(), sum(seed_weights) ** n
            for seed in product(range(order), repeat=n):
                counts = [0] * (order * dimension)
                counts[0] = 1
                for ratio, coefficient in zip(seed, coefficients, strict=True):
                    following = counts[:]
                    for state, count in enumerate(counts):
                        root, observation = divmod(state, dimension)
                        following[((root + ratio) % order) * dimension + (observation ^ coefficient)] += count
                    counts = following
                marginal = [sum(counts[root * dimension + y] for root in range(order)) for y in range(dimension)]
                distance = Fraction(
                    sum(abs(order * counts[root * dimension + y] - marginal[y]) for root in range(order) for y in range(dimension)),
                    2 * order * (1 << n),
                )
                multiplicity = reduce(mul, (seed_weights[value] for value in seed), 1)
                average_squared += multiplicity * distance**2 / total
                if seed == (0,) * n:
                    assert distance == Fraction(order - 1, order)
                if coefficients == (1,) * n:
                    assert marginal[2:] == [0, 0]
            bias = Fraction(seed_weights[0] - seed_weights[1], sum(seed_weights))
            bound = Fraction((order - 1) * dimension, 4) * ((1 + bias) / 2) ** n
            assert average_squared <= bound < 1
    print(
        "Exact public-seed averages satisfy the joint Fourier bound; a bad fixed seed leaks and nonuniform linear marginals are retained", flush=True
    )


def set_library(v, support, words, bits):
    library, indices = Library(v), {"memory": set(), "code": set()}
    for ordinal, (s, alternatives_words, choice) in enumerate(zip(support, words, bits, strict=True)):
        alternatives = []
        for alternative, payload in enumerate(alternatives_words):
            pc, frame = CODE_BASE + 4 * s + 2 * alternative, FRAME_BASE + 256 * ordinal + 128 * alternative
            templates = library.templates((v.OP_SET, pc, [], True), v.GEN**frame)
            for lane, value in enumerate(payload):
                templates[0][1][v.SET_COLUMNS.index(f"k_{lane}")] = v.E(value)
            library.register(templates)
            alternatives.append(templates)
            indices["code"].update((pc, pc + 1))
            indices["memory"].update(frame + offset for offset in (0, 64, 65, 66))
        library.append(alternatives[choice])
        library.append(alternatives[choice])
    library.verify()
    return library, indices


def actual_formulas(v):
    rng = Random(167)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    alpha, beta, point = [sample() for _ in range(4)], sample(), [sample() for _ in range(20)]
    e = v.eq_kernel(alpha)
    delta = e[2] * (v.ONE + v.GEN**2)
    t = [value / (v.ONE + value) for value in alpha]
    assert [e[j] / e[7] for j in (5, 6, 7)] == [v.ONE / t[1], v.ONE / t[0], v.ONE]
    support = (0, 1, 64, 2048)
    words = [[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support]
    baseline, indices = set_library(v, support, words, [0] * len(support))

    def at(library, pc, count):
        address = int(v.GEN**pc)
        return fingerprint(v, e, beta, v.SEP_BYTECODE, address, count, library.images["code"][address])

    def root(library):
        return reduce(mul, (at(library, pc, v.GEN ** library.reads["code", int(v.GEN**pc)]) for pc in indices["code"]), v.ONE)

    initial = root(baseline), final_evaluation(v, baseline, "code", indices["code"], point)
    ratios, coefficients = [], []
    for s, payloads in zip(support, words, strict=True):
        seeds = [at(baseline, CODE_BASE + 4 * s + offset, v.ONE) for offset in range(4)]
        set_ratio = seeds[0] * (seeds[2] + delta) / ((seeds[0] + delta) * seeds[2])
        jump_ratio = seeds[1] * (seeds[3] + delta) / ((seeds[1] + delta) * seeds[3])
        for alternative, payload in enumerate(payloads):
            pc = CODE_BASE + 4 * s + 2 * alternative
            constant = beta + e[0] * v.SEP_BYTECODE + e[1] * v.GEN**pc + e[2] + e[3] * v.GEN**v.OP_SET + e[4]
            assert seeds[2 * alternative] == constant + v.dot(e[5:8], [v.E(value) for value in payload])
        ratios.append(set_ratio * jump_ratio)
        coefficients.append((v.ONE + v.GEN**2) * weight(v, point[2:], (CODE_BASE >> 2) + s))
    for bits in product((0, 1), repeat=len(support)):
        library, current_indices = set_library(v, support, words, bits)
        assert library.images == baseline.images and current_indices == indices
        assert dict(library.exponents) == dict(baseline.exponents)
        for (opcode, row), (old_opcode, old_row) in zip(library.rows, baseline.rows, strict=True):
            assert opcode == old_opcode
            assert [row[column] for column in v.TABLES[opcode].count_columns] == [old_row[column] for column in v.TABLES[opcode].count_columns]
        assert root(library) == initial[0] * reduce(mul, (ratio for ratio, bit in zip(ratios, bits, strict=True) if bit), v.ONE)
        assert final_evaluation(v, library, "code", indices["code"], point) == initial[1] + v.E.sum(
            coefficient for coefficient, bit in zip(coefficients, bits, strict=True) if bit
        )
    rank = binary_basis([int((v.ONE + v.GEN**2) * weight(v, point[2:], (CODE_BASE >> 2) + s)) for s in SPARSE])
    assert len(rank) == 192
    print(
        "Actual SET/JUMP alternatives preserve images and all count leaves; fingerprints, product ratios and evaluation changes match the formulas",
        flush=True,
    )
    print("The retained sparse support has evaluation rank 192 at the audited honest-coin instance", flush=True)


def reservations(v):
    assert len(SUPPORT) == BITS and set(SPARSE) <= set(SUPPORT)
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 12, 4, 17, 3))
    bus, count = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22 and layout.stack_log == 24 and bus == v.bus_layout((0, 20, 20), layout.pull)
    assert [p.index for block, p in zip(layout.push, bus.tables, strict=True) if block.owner == v.OP_MUL] == [(8 + i) << 18 for i in range(5)]
    assert all(p.index >> 20 == (p.index + (1 << p.variables) - 1) >> 20 for p in count.tables)
    counter_slots = {8 * ((bank << 12) + s) + low for bank in range(4) for s in SPARSE for low in range(8)}
    xor_returns, mul_returns = set(range(1536, 1544)), set(range(60000, 60049))
    occupied = counter_slots | xor_returns | mul_returns
    assert len(occupied) == len(counter_slots) + len(xor_returns) + len(mul_returns)
    available = list(islice((row for row in range(1 << 17) if row not in occupied), 2 * len(SPARSE) + 2 * BITS))
    assert len(available) == 2 * len(SPARSE) + 2 * BITS
    assert 2 * BITS < 1 << layout.table_log_heights[v.OP_SET]
    intervals = [
        (32, 99),
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (1 << 17, (1 << 17) + 8 * 128),
        (3 << 16, (3 << 16) + 48 * 128),
        (FRAME_BASE, FRAME_BASE + 256 * BITS),
        (1 << 19, (1 << 19) + 32),
        (MEMORY_FRAME, MEMORY_FRAME + (1 << 15)),
    ]
    assert all(a[1] <= b[0] for a, b in pairwise(intervals)) and intervals[-1][1] < 1 << 20
    codes = [
        (2048, 2050),
        (4096, 4096 + 2 * 5 * 4 * len(SPARSE)),
        (32768, 32770),
        (CODE_BASE, CODE_BASE + (1 << 14)),
        (MEMORY_PC, MEMORY_PC + 1),
        (1 << 19, (1 << 19) + (1 << 18)),
    ]
    assert all(a[1] <= b[0] for a, b in pairwise(codes)) and codes[-1][1] <= 1 << 20
    print(
        "Supported extended layout: all existing first-packet identities persist; SET/JUMP slots, public code and memory reservations are disjoint",
        flush=True,
    )


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    bias = Fraction(4 * size, (base**2 - 2) ** 2)
    eta_squared = Fraction((size - 2) * size, 4) * ((1 + bias) / 2) ** BITS
    assert bias < Fraction(1, 1 << 61)
    assert eta_squared < Fraction(1, 1 << 640)
    fixed_errors = Fraction((1 << 20) + 8 * BITS + 8, size) + Fraction(base**2, (size - 2) ** 2)
    evaluation = Fraction(1, 1 << 158) + Fraction(18, size)
    assert Fraction(1, 1 << 155) + Fraction(1, 1 << 160) + fixed_errors + evaluation < Fraction(1, 1 << 154)
    print(
        "Exact bounds: average setup-dependent error below 2^-320; Markov threshold 2^-160 fails for fewer than a 2^-160 fraction of libraries",
        flush=True,
    )
    print(
        "For the remaining libraries, first-packet/boundary error is below 2^-154 under the stated normalization and honest-coin assumptions",
        flush=True,
    )


if __name__ == "__main__":
    public_seed_mixing()
    verifier = verifier_module()
    actual_formulas(verifier)
    reservations(verifier)
    concrete_bound()
