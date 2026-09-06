"""A setup-dependent bytecode frontier simulator, excluding mixed GKR messages."""

from fractions import Fraction
from functools import reduce
from itertools import islice, pairwise, product
from operator import mul
from random import Random

from zk_bus_boundary_audit import final_evaluation
from zk_bus_packet_audit import weight
from zk_bytecode_public_library_audit import (
    BITS,
    FRAME_BASE,
    MEMORY_FRAME,
    MEMORY_PC,
    SUPPORT,
    set_library,
)
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE, gkr_replay
from zk_gkr_first_packet_audit import fingerprint
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

BANKS = 4
CODE_BASES = tuple((bank << 18) + (1 << 16) for bank in range(BANKS))


def multi_seed_bound():
    banks, per_bank, order, dimension = 2, 4, 3, 4
    for seed_weights in ((1, 1, 1), (2, 1, 1)):
        average, total = Fraction(), sum(seed_weights) ** (banks * per_bank)
        for seed in product(range(order), repeat=banks * per_bank):
            counts = [0] * (order**banks * dimension)
            counts[0] = 1
            for index, ratio in enumerate(seed):
                following = counts[:]
                for state, count in enumerate(counts):
                    roots, observed = divmod(state, dimension)
                    left, right = divmod(roots, order)
                    new_roots = ((left + ratio) % order) * order + right if index < per_bank else left * order + (right + ratio) % order
                    following[new_roots * dimension + (observed ^ (1 + index % 3))] += count
                counts = following
            marginal = [sum(counts[root * dimension + y] for root in range(order**banks)) for y in range(dimension)]
            distance = Fraction(
                sum(abs(order**banks * counts[root * dimension + y] - marginal[y]) for root in range(order**banks) for y in range(dimension)),
                2 * order**banks * (1 << (banks * per_bank)),
            )
            average += reduce(mul, (seed_weights[value] for value in seed), 1) * distance**2 / total
            if seed == (0,) * (banks * per_bank):
                assert distance == Fraction(order**banks - 1, order**banks)
        bias = Fraction(seed_weights[0] - seed_weights[1], sum(seed_weights))
        bound = Fraction(dimension, 4) * ((1 + (order - 1) * ((1 + bias) / 2) ** per_bank) ** banks - 1)
        assert average <= bound < 1
    print(
        "Exact public-seed averaging verifies the multi-product/linear-view Fourier bound, including the all-trivial public-ratio failure", flush=True
    )


def code_frontier(v, library, indices, e, beta):
    values = [v.ONE] * BANKS
    for pc in indices:
        address = int(v.GEN**pc)
        values[pc >> 18] *= fingerprint(v, e, beta, v.SEP_BYTECODE, address, v.GEN ** library.reads["code", address], library.images["code"][address])
    return values


def single_bank_limitation(v):
    rng = Random(170)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    code = (3 << 18) + 32
    examples, roots = [], []
    for choice in (0, 1):
        library, alternatives = Library(v), []
        for bit in (0, 1):
            row = library.row(v.OP_JUMP, code + bit, v.GEN ** (900000 + 4 * bit), code + bit)
            templates = [(v.OP_JUMP, row)]
            library.register(templates)
            alternatives.append(templates)
        library.append(alternatives[choice])
        library.append(alternatives[choice])
        library.verify()
        roots.append(code_frontier(v, library, (code, code + 1), e, beta)[3])
        examples.append(library)
    assert examples[0].images == examples[1].images and dict(examples[0].exponents) == dict(examples[1].exponents)
    seeds = [
        fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN ** (code + bit)), v.ONE, examples[0].images["code"][int(v.GEN ** (code + bit))])
        for bit in (0, 1)
    ]
    difference = e[2] * (v.ONE + v.GEN**2) * (seeds[0] + seeds[1])
    assert roots[0] + roots[1] == difference != v.ZERO
    print("A valid private JUMP occupancy pair changes an unmasked quarter-3 product with images/count-column products fixed", flush=True)
    print("This is a limitation for the strengthened frontier view, not a distinguisher for the actual mixed second-layer transcript", flush=True)


def compact_banks(v):
    rng = Random(171)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta, point = v.eq_kernel([sample() for _ in range(4)]), sample(), [sample() for _ in range(20)]
    support = (0, 64)
    words = [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support] for _ in range(BANKS)]

    def combine(bits):
        combined, indices = Library(v), {"memory": set(), "code": set()}
        for bank in range(BANKS):
            library, local = set_library(
                v,
                support,
                words[bank],
                bits[bank * len(support) : (bank + 1) * len(support)],
                code_base=CODE_BASES[bank],
                frame_base=FRAME_BASE + 8 * BITS * bank,
                compact=True,
            )
            for kind, selected_indices in indices.items():
                assert combined.images[kind].keys().isdisjoint(library.images[kind])
                combined.images[kind].update(library.images[kind])
                selected_indices.update(local[kind])
            combined.append(library.rows)
        combined.verify()
        return combined, indices

    baseline, indices = combine([0] * (BANKS * len(support)))
    initial_roots = code_frontier(v, baseline, indices["code"], e, beta)
    initial_eval = final_evaluation(v, baseline, "code", indices["code"], point)
    ratios, coefficients = [], []
    for bank in range(BANKS):
        for s in support:
            seeds = [
                fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN**pc), v.ONE, baseline.images["code"][int(v.GEN**pc)])
                for pc in range(CODE_BASES[bank] + 4 * s, CODE_BASES[bank] + 4 * s + 4)
            ]
            delta = e[2] * (v.ONE + v.GEN**2)
            ratios.append(reduce(mul, (seeds[a] * (seeds[a + 2] + delta) / ((seeds[a] + delta) * seeds[a + 2]) for a in (0, 1)), v.ONE))
            coefficients.append((v.ONE + v.GEN**2) * weight(v, point[2:], (CODE_BASES[bank] >> 2) + s))
    bit_vectors = [[int(i == selected) for i in range(BANKS * len(support))] for selected in range(BANKS * len(support))]
    bit_vectors += [[1] * (BANKS * len(support)), [i % 2 for i in range(BANKS * len(support))]]
    for bits in bit_vectors:
        library, current_indices = combine(bits)
        assert library.images == baseline.images and current_indices == indices
        assert dict(library.exponents) == dict(baseline.exponents)
        for (opcode, row), (old_opcode, old) in zip(library.rows, baseline.rows, strict=True):
            assert opcode == old_opcode
            assert [row[column] for column in v.TABLES[opcode].count_columns] == [old[column] for column in v.TABLES[opcode].count_columns]
        expected = initial_roots[:]
        for i, bit in enumerate(bits):
            if bit:
                expected[i // len(support)] *= ratios[i]
        assert code_frontier(v, library, indices["code"], e, beta) == expected
        assert final_evaluation(v, library, "code", indices["code"], point) == initial_eval + v.E.sum(
            coefficient for coefficient, bit in zip(coefficients, bits, strict=True) if bit
        )
    assert len(binary_basis([int((v.ONE + v.GEN**2) * weight(v, point[2:], (CODE_BASES[0] >> 2) + s)) for s in SPARSE])) == 192
    print(
        "Four compact SET/JUMP banks preserve all images/count leaves; actual quarter products and their shared evaluation obey the joint formulas",
        flush=True,
    )


def layout_and_gkr(v):
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 14, 4, 17, 3))
    bus, count = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22 and layout.stack_log == 24
    assert bus == v.bus_layout((0, 20, 20), layout.pull)
    assert bus.framework[2].index >> 18 == 4 and bus.framework[2].variables == 20
    assert [p.index for block, p in zip(layout.push, bus.tables, strict=True) if block.owner == v.OP_MUL] == [(8 + i) << 18 for i in range(5)]
    assert all(p.index >> 20 == (p.index + (1 << p.variables) - 1) >> 20 for p in count.tables)
    slots = (
        {8 * ((bank << 12) + s) + low for bank in range(4) for s in SPARSE for low in range(8)} | set(range(1536, 1544)) | set(range(60000, 60049))
    )
    needed = 2 * BANKS * BITS + 2 * len(SPARSE)
    assert len(list(islice((row for row in range(1 << 17) if row not in slots), needed))) == needed
    assert 2 * BANKS * BITS < 1 << layout.table_log_heights[v.OP_SET]
    frames = [
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (1 << 17, (1 << 17) + 8 * 128),
        (3 << 16, (3 << 16) + 48 * 128),
        (FRAME_BASE, FRAME_BASE + 8 * BANKS * BITS),
        (1 << 19, (1 << 19) + 32),
        (MEMORY_FRAME, MEMORY_FRAME + (1 << 15)),
    ]
    assert all(a[1] <= b[0] for a, b in pairwise(frames)) and frames[-1][1] < 1 << 20
    holes = [(base, base + (1 << 14)) for base in CODE_BASES]
    assert 4096 + 2 * 5 * 4 * len(SPARSE) < holes[0][0]
    assert all(a[1] <= b[0] for a, b in pairwise(holes))
    assert all(not (a <= pc < b) for a, b in holes for pc in (2048, 2049, 32768, 32769, MEMORY_PC))
    assert all((base + 4 * s + offset) >> 18 == bank for bank, base in enumerate(CODE_BASES) for s in SUPPORT for offset in range(4))
    rng = Random(172)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    push, pull = [[sample() for _ in range(16)] for _ in range(2)]
    pull[-1] = reduce(mul, push, v.ONE) / reduce(mul, pull[:-1], v.ONE)
    replay = gkr_replay(v, [v.GEN**i for i in range(16)], seed=173, details=True, bus_leaves=(push, pull))
    x, children = replay["challenge"], replay["children"][1]
    assert tuple(children) == tuple(v.dot(v.eq_kernel(x), pull[j::4]) for j in range(4))
    print("Supported layout and compact reservations checked; bytecode nodes are frontier entries 4..7", flush=True)
    print(
        "Reference GKR replay verifies their placement in the second packet on sixteen compressed nodes; deeper VM trees are not instantiated",
        flush=True,
    )


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    bias = Fraction(4 * size, (base**2 - 2) ** 2)
    term = (size - 2) * ((1 + bias) / 2) ** BITS
    assert term < Fraction(1, 4)
    mean_square_upper = 2 * size * term
    assert mean_square_upper < Fraction(1, 1 << 638)
    errors = Fraction((1 << 20) + 8 * BANKS * BITS + 8 + 18, size) + Fraction(base**2, (size - 2) ** 2)
    assert Fraction(1, 1 << 155) + Fraction(1, 1 << 159) + Fraction(1, 1 << 158) + errors < Fraction(1, 1 << 154)
    print("Rational bounds: multi-bank mean error below 2^-319; fixed-library threshold 2^-159 has exceptional fraction below 2^-160", flush=True)
    print(
        "Joint first-packet/boundary/bytecode-frontier error below 2^-154 in the optional setup model; mixed GKR messages remain unproved", flush=True
    )


if __name__ == "__main__":
    multi_seed_bound()
    verifier = verifier_module()
    single_bank_limitation(verifier)
    compact_banks(verifier)
    layout_and_gkr(verifier)
    concrete_bound()
