"""Close the first-two-layer/boundary residual; intermediate GKR remains open."""

from fractions import Fraction
from functools import reduce
from itertools import islice, product
from operator import mul
from random import Random
from types import FunctionType

from zk_bus_boundary_audit import error_bound, final_evaluation, switch_library
from zk_bus_packet_audit import weight
from zk_bytecode_frontier_audit import CODE_BASES
from zk_bytecode_public_library_audit import FRAME_BASE as SET_FRAMES
from zk_bytecode_public_library_audit import MEMORY_FRAME, MEMORY_PC, set_library
from zk_column_count_audit import Library
from zk_control_composition_audit import frontier
from zk_count_children_audit import SPARSE, gkr_replay
from zk_frame_gauge_audit import root_exceptions
from zk_frontier_entropy_audit import SPREAD_FRAMES, spread_reservations
from zk_gkr_second_wire_audit import full_depth_prefix, stage_wire
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import table_products
from zk_set_payload_products_audit import BITS
from zk_stacked_audit import binary_basis

CODE_BASE, FRAME_BASE = 131072, 589824
CONDITIONS = 48


def mul_library(v, support, gauges, bits, conditions=None):
    library, indices = Library(v), {"memory": set(), "code": set()}
    for ordinal, (index, scales, choice) in enumerate(zip(support, gauges, bits, strict=True)):
        alternatives = []
        for alternative, scale in enumerate(scales):
            pc, frame = CODE_BASE + 4 * index + 2 * alternative, FRAME_BASE + 16 * ordinal + 8 * alternative
            gauge, physical = v.E(scale), v.GEN**frame
            inverse = gauge.inv()
            templates = library.templates((v.OP_MUL, pc, [], True), physical * gauge)
            for name, offset in zip(("o_a", "o_b", "o_c"), (0, 1, 2), strict=True):
                templates[0][1][v.ARITH_COLUMNS.index(name)] = v.GEN**offset * inverse
            templates[0][1][v.ARITH_COLUMNS.index("va_0")] = v.ONE
            templates[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.ONE
            for name, offset in zip(("o_c", "o_d", "o_f"), (3, 4, 5), strict=True):
                templates[1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**offset * inverse
            condition = v.E(conditions[ordinal][alternative]) if conditions is not None else v.ONE
            assert condition
            templates[1][1][v.JUMP_COLUMNS.index("v_cond")] = condition
            templates[1][1][v.JUMP_COLUMNS.index("w")] = condition.inv()
            library.register(templates)
            alternatives.append(templates)
            indices["memory"].update(frame + offset for offset in range(6))
            indices["code"].update((pc, pc + 1))
        library.append(alternatives[choice])
        library.append(alternatives[choice])
    library.verify()
    return library, indices


def four_products(v, library, e, beta):
    push, pull = [table_products(v, library, v.OP_MUL, side, e, beta) for side in ("push", "pull")]
    return push[0], pull[0], push[1], pull[1]


def retained_view(v, library, indices, e, beta, points):
    jump = [table_products(v, library, v.OP_JUMP, side, e, beta) for side in ("push", "pull")]
    counters = [final_evaluation(v, library, kind, indices[kind], point) for kind, point in zip(("memory", "code"), points, strict=True)]
    return jump[0][2] * jump[0][3], jump[1][2] * jump[1][3], *counters


def character_injection():
    for order in (3, 5, 9, 15):
        for a, b, c, d in product(range(order), repeat=4):
            roots = (2 * b, 2 * a, d, c + d, c, -2 * c - 2 * d)
            assert all(exponent % order == 0 for exponent in roots) == (a == b == c == d == 0)
    print("Five roots plus zero give character exponents (2b,2a,d,c+d,c,-2c-2d); odd character orders retain every target character", flush=True)


def actual_formulas(v):
    rng = Random(196)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    points = [[sample() for _ in range(20)] for _ in range(2)]
    support = (0, 1, 64, 2048)
    banks = [[[1, 1] for _ in support], [[rng.getrandbits(64) or 1 for _ in range(2)] for _ in support]]
    choices = ((0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 1, 1), (0, 1, 0, 1))
    conditions = [[[1, 1] for _ in support], [[rng.getrandbits(64) or 1 for _ in range(2)] for _ in support]]
    retained, targets, labels, seeds = {}, {}, None, {}
    condition_cofactors = {}
    for bank, noise, choice in product(range(2), range(2), range(len(choices))):
        library, indices = mul_library(v, support, banks[bank], choices[choice], conditions[noise])
        current = [(opcode, tuple(row[column] for column in v.TABLES[opcode].count_columns)) for opcode, row in library.rows]
        if labels is None:
            labels = current
        assert current == labels
        if (bank, noise) not in seeds:
            seeds[bank, noise] = library.images
        assert library.images == seeds[bank, noise]
        retained[bank, noise, choice] = retained_view(v, library, indices, e, beta, points)
        targets[bank, noise, choice] = four_products(v, library, e, beta)
        expected = [v.ONE] * 4
        condition_products = [v.ONE, v.ONE]
        for ordinal, (index, alternative) in enumerate(zip(support, choices[choice], strict=True)):
            pc, frame = CODE_BASE + 4 * index + 2 * alternative, FRAME_BASE + 16 * ordinal + 8 * alternative
            gauge, physical = v.E(banks[bank][ordinal][alternative]), v.GEN**frame
            states = [beta + e[0] * v.SEP_STATE + e[1] * v.GEN**address for address in (pc, pc + 1)]
            reciprocal = e[4] + e[5] * v.GEN + e[6] * v.GEN**2
            code = [beta + e[0] * v.SEP_BYTECODE + e[1] * v.GEN**pc + e[2] * v.GEN**label + e[3] * v.GEN**v.OP_MUL for label in range(3)]
            roots = [constant / (e[2] * physical) for constant in states] + [reciprocal / constant for constant in code]
            assert all(root ** (1 << 64) != root for root in roots)
            assert all(left ** (1 << (64 * h)) != right for i, left in enumerate(roots) for right in roots[i + 1 :] for h in (0, 1, 2))
            states = [constant + e[2] * physical * gauge for constant in states]
            code = [constant + reciprocal / gauge for constant in code]
            factors = states[1] ** 2, states[0] ** 2, code[1] * code[2], code[0] * code[1]
            expected = [a * b for a, b in zip(expected, factors, strict=True)]
            constants = [beta + e[0] * v.SEP_MEM + e[1] * physical * v.GEN**3 + e[2] * v.GEN**label for label in range(3)]
            roots = [constant / e[3] for constant in constants]
            assert all(root ** (1 << 64) != root for root in roots)
            assert all(left ** (1 << (64 * h)) != right for i, left in enumerate(roots) for right in roots[i + 1 :] for h in (0, 1, 2))
            values = [constant + e[3] * v.E(conditions[noise][ordinal][alternative]) for constant in constants]
            condition_products[0] *= values[1] * values[2]
            condition_products[1] *= values[0] * values[1]
        assert tuple(expected) == targets[bank, noise, choice]
        condition_cofactors[bank, noise, choice] = tuple(a / b for a, b in zip(retained[bank, noise, choice][:2], condition_products, strict=True))
        push, pull, count = frontier(v, library, indices, e, beta, xor_log=6)
        assert targets[bank, noise, choice] == (push[8], pull[8], push[9], pull[9])
        assert retained[bank, noise, choice][:2] == (push[14], pull[14])
        full_depth_prefix(v, gkr_replay(v, count, seed=198, details=True, bus_leaves=(push, pull)), 198)
    assert all(retained[0, noise, choice] == retained[1, noise, choice] for noise, choice in product(range(2), range(len(choices))))
    assert all(targets[0, noise, choice] != targets[1, noise, choice] for noise, choice in product(range(2), range(len(choices))))
    assert all(len({targets[1, 0, choice][column] for choice in range(len(choices))}) > 1 for column in range(4))
    for bank, choice in product(range(2), range(len(choices))):
        assert targets[bank, 0, choice] == targets[bank, 1, choice]
        assert retained[bank, 0, choice][2:] == retained[bank, 1, choice][2:]
        assert retained[bank, 0, choice][:2] != retained[bank, 1, choice][:2]
        assert condition_cofactors[bank, 0, choice] == condition_cofactors[0, 1, choice]
    assert seeds[0, 0] != seeds[1, 0] and all(seeds[0, 0][kind].keys() == seeds[1, 0][kind].keys() for kind in seeds[0, 0])
    assert all(seeds[bank, 0]["code"] == seeds[bank, 1]["code"] for bank in range(2))
    print(
        "Valid gauged MUL/JUMP cycles preserve physical addresses, count leaves and the four retained fields while changing all four MUL control products",
        flush=True,
    )
    print("Actual state and reciprocal bytecode factors match the five-root formulas on regular extension-field coins", flush=True)
    print(
        "Private nonzero JUMP conditions preserve branches, MUL controls and final counters; their three-factor products match both node-14 channels",
        flush=True,
    )


def enlarged_sampler(v):
    rng = Random(197)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    count = [v.GEN**index for index in range(16)]
    for fixed_indices in ((4, 5, 6, 7, 14, 30), (4, 5, 6, 7)):
        nodes = [sample() for _ in range(32)]
        fixed = [nodes[index] for index in fixed_indices]
        nodes[-1] = reduce(mul, nodes[:16]) / reduce(mul, nodes[16:31])
        push, pull = nodes[:16], nodes[16:]
        replay = gkr_replay(v, count, seed=198, details=True, bus_leaves=(push, pull))
        full_depth_prefix(v, replay, 198)
        assert stage_wire(v, (push, pull, count), replay["equality"], replay["challenge"], replay["combiner"]) == replay["view"][3]
        assert [nodes[index] for index in fixed_indices] == fixed
    print("The intermediate 25-coordinate and final 27-coordinate balanced-frontier samplers replay both complete layers", flush=True)


def counter_marginal(v):
    rng = Random(199)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    point = [sample() for _ in range(20)]
    delta = v.ONE + v.GEN**2
    code = [delta * weight(v, point[2:], (CODE_BASES[0] >> 2) + s) for s in SPARSE]
    memory = [delta * (v.ONE + point[0] * point[1]) * weight(v, point[3:], (MEMORY_FRAME >> 3) + s) for s in SPARSE]
    set_memory = [delta * weight(v, point[3:], (SET_FRAMES >> 3) + s) for s in SPARSE]
    assert len(binary_basis([int(value) for value in code])) == 192
    assert len(binary_basis([int(value) for value in memory])) == 192
    assert len(binary_basis([int(a) | (int(b) << 192) for a, b in zip(set_memory, code, strict=True)] + [int(value) for value in memory])) == 384
    switch = FunctionType(switch_library.__code__, {**switch_library.__globals__, "MEMORY_FRAMES": MEMORY_FRAME, "MEMORY_PC": MEMORY_PC})
    support, values = (0, 1, 64), [[[1, 0, 0], [2, 0, 0]] for _ in range(3)]
    sets, memories = [], []
    for bits in ((0, 0, 0), (1, 0, 1)):
        library, indices = set_library(v, support, values, bits, code_base=CODE_BASES[0], frame_base=SET_FRAMES, compact=True)
        sets.append(final_evaluation(v, library, "code", indices["code"], point))
        library, indices = switch(v, "memory", support, bits)
        memories.append(tuple(final_evaluation(v, library, kind, indices[kind], point) for kind in ("memory", "code")))
    assert sets[0] + sets[1] == v.E.sum(delta * weight(v, point[2:], (CODE_BASES[0] >> 2) + s) for s in (0, 64))
    assert memories[0][0] + memories[1][0] == v.E.sum(
        delta * (v.ONE + point[0] * point[1]) * weight(v, point[3:], (MEMORY_FRAME >> 3) + s) for s in (0, 64)
    )
    assert memories[0][1] == memories[1][1]
    print(
        "Existing SET occupancy and independent memory occupancy retain the exact triangular final-counter formulas and a 384-bit rank certificate",
        flush=True,
    )


def layout_reservations(v):
    spread_reservations(v)
    code_end, frame_end = CODE_BASE + 4 * BITS, FRAME_BASE + 16 * BITS
    assert code_end < 1 << 18 and FRAME_BASE >> 18 == (frame_end - 1) >> 18 == 2
    assert all(code_end <= base or base + (1 << 14) <= CODE_BASE for base in CODE_BASES)
    assert all(frame_end <= base or base + 48 * 128 <= FRAME_BASE for base in SPREAD_FRAMES)
    assert (1 << 19) + 32 <= FRAME_BASE and frame_end <= 786432
    assert 32 < (1 << 18) - 240 - 2 * BITS
    occupied = {8 * ((bank << 12) + s) + low for bank in range(4) for s in SPARSE for low in range(8)}
    occupied.update(range(1536, 1536 + 44))
    occupied.update(range(60000, 60241))
    needed = 2 * 4 * BITS + 2 * len(SPARSE) + 2 * BITS
    assert len(list(islice((slot for slot in range(1 << 17) if slot not in occupied), needed))) == needed
    print("The 3840-bit MUL scale bank fits fresh code and memory ranges with unchanged MUL/JUMP heights and frontier ownership", flush=True)


def concrete_bound():
    base, size, total = 1 << 64, 1 << 192, BITS
    kappa = Fraction(15 * (1 << 32), base - 1)
    bias = kappa**2
    assert bias < Fraction(1, 1 << 56)
    mean_square = Fraction(size**4 * ((size - 1) ** 4 - 1), 4) * ((1 + bias) / 2) ** (total - 4)
    assert mean_square < Fraction(1, 1 << 2300)
    bad = Fraction(8 + 6 * total, size) + Fraction(1 + 52 * total, size - 2) + Fraction(4 * base**2, size * (size - 2))
    zeros = Fraction((1 << 24) + 10 * total, size)
    assert Fraction(1, 1 << 160) + bad + zeros < Fraction(1, 1 << 159)
    joint_mean = Fraction(1, 1 << 383) + Fraction(1, 1 << 571) + Fraction(1, 1 << 1150)
    assert joint_mean / Fraction(1, 1 << 160) < Fraction(1, 1 << 222)
    rank = Fraction(base**2, (size - 2) ** 2)
    mul_error = Fraction((1 << 23) + 8 * 48 + 8, size) + rank + Fraction(1, 1 << 384)
    xor_error = Fraction((1 << 23) + 8 * 36 + 8, size) + rank + Fraction(1, 1 << 216)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary, _ = error_bound()
    assert 5 * mul_error + xor_error + unused_error + boundary + Fraction(1, 1 << 158) < Fraction(1, 1 << 155)
    condition_kappa = Fraction(8 * (1 << 32) + 1, base - 1)
    condition_square = Fraction((size - 1) ** 2 - 1, 4) * condition_kappa ** (2 * (CONDITIONS - 3))
    assert condition_square < Fraction(1, 1 << 2180)
    condition_bad = Fraction(8, size) + Fraction(12 * CONDITIONS, size - 2) + Fraction(3 * base**2, size * (size - 2))
    condition_error = condition_bad + Fraction((1 << 24) + 6 * CONDITIONS, size) + Fraction(1, 1 << 1090)
    assert condition_error < Fraction(1, 1 << 167)
    span = boundary - Fraction(4 * 40 - 17 + 11, size) - Fraction(6, 1 << 256)
    counters = 2 * span + Fraction(37, size)
    assert 5 * mul_error + xor_error + unused_error + boundary + Fraction(1, 1 << 158) + condition_error + counters < Fraction(1, 1 << 155)
    print(
        "Mean four-product mixing below 2^-1150; all public libraries share an exception below 2^-222 and the joint view error stays below 2^-155",
        flush=True,
    )
    print(
        "Private-condition product mixing is below 2^-1090, with exclusions below 2^-167; counter uniformization closes the remaining residual",
        flush=True,
    )
    print(
        "First two GKR layers and the final boundary now have a public-data simulator below 2^-155; intermediate GKR, later proofs and Fiat-Shamir remain open",
        flush=True,
    )


if __name__ == "__main__":
    character_injection()
    root_exceptions()
    verifier = verifier_module()
    actual_formulas(verifier)
    enlarged_sampler(verifier)
    counter_marginal(verifier)
    layout_reservations(verifier)
    concrete_bound()
