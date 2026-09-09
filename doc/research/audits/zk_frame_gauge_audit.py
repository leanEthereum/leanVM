"""Address-preserving frame gauges, requiring raw field-valued bytecode support."""

from fractions import Fraction
from functools import reduce
from itertools import product
from random import Random

from zk_bus_boundary_audit import final_evaluation
from zk_bytecode_frontier_audit import CODE_BASES
from zk_bytecode_public_library_audit import CODE_BASE, FRAME_BASE, set_library
from zk_column_count_audit import Library
from zk_control_residual_audit import add_library
from zk_count_children_audit import gkr_replay
from zk_gkr_coarse_audit import PAD_FRAME, PAD_PC, REAL_FRAME, REAL_PC, cycles
from zk_gkr_first_packet_audit import fingerprint
from zk_gkr_second_wire_audit import full_depth_prefix
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations, table_products
from zk_set_payload_products_audit import BANKS, BITS


def root_exceptions():
    f, base = Field(6, 0b1000011), 4
    multiply = lambda *values: reduce(lambda a, b: f.mul[a][b], values, 1)
    frobenius = [multiply(a, a, a, a) for a in range(f.size)]
    subfield = {a for a in range(f.size) if frobenius[a] == a}
    assert len(subfield) == base
    exceptional = 0
    for ratio, shift in product(range(f.size), repeat=2):
        small = sum((shift ^ multiply(ratio, pc)) in subfield for pc in subfield)
        all_small = ratio in subfield and shift in subfield
        exceptional += all_small
        assert small <= 1 or all_small
        if all_small:
            assert small == base
    assert Fraction(exceptional, f.size**2) == Fraction(base**2, f.size**2)
    generator = next(a for a in subfield if a not in (0, 1))
    for h in (1, 2):
        collisions = 0
        for ratio, shift in product(range(1, f.size), range(f.size)):
            left, right = shift ^ ratio, shift ^ multiply(ratio, generator)
            for _ in range(h):
                left = frobenius[left]
            collisions += left == right
        assert Fraction(collisions, (f.size - 1) * f.size) <= Fraction(1, f.size - 1)
    print("Exact GF(4)/GF(64) root exceptions: at most one small-field root outside the joint bad event; paired conjugacy bounds pass", flush=True)
    norm = lambda value: multiply(*([value] * ((f.size - 1) // (base - 1))))
    inverse = {a: next(b for b in range(1, f.size) if multiply(a, b) == 1) for a in range(1, f.size)}
    for shift in range(1, f.size):
        eligible = [z for z in range(1, f.size) if z != shift and norm(z) == norm(z ^ shift)]
        assert len(eligible) == base**2 + base
        for h in (1, 2):
            collisions = 0
            for z, scale in product(eligible, range(1, f.size)):
                left, right = multiply(scale, inverse[z]), multiply(scale, inverse[z ^ shift])
                for _ in range(h):
                    left = frobenius[left]
                collisions += left == right
            assert collisions == (base**2 + base) * (base - 1)
            assert Fraction(collisions, f.size * (f.size - 2)) < Fraction(1, f.size - 2)
    print("Exact reciprocal-root conjugacy counts use the norm-one subgroup and satisfy the extension-field error bound", flush=True)
    state_tag, memory_tag, pc, frame = 1, generator, generator, 1
    for t0 in range(2, f.size):
        constant = state_tag ^ memory_tag ^ multiply(t0, multiply(frame, generator, generator, generator) ^ pc)
        if not constant:
            continue
        for state in range(f.size):
            matches = [0, 0, 0]
            for t1 in range(2, f.size):
                z = multiply(state, t1, frame) ^ state_tag ^ multiply(t0, pc)
                root = multiply(
                    z ^ memory_tag ^ multiply(t0, frame, generator, generator, generator) ^ t1,
                    inverse[t0],
                    inverse[t1],
                    inverse[frame],
                )
                assert root == multiply(state, inverse[t0]) ^ multiply(constant, inverse[t0], inverse[t1], inverse[frame]) ^ multiply(
                    inverse[t0], inverse[frame]
                )
                conjugate = state
                for h in range(3):
                    matches[h] += conjugate == root
                    conjugate = frobenius[conjugate]
            assert all(count <= 1 for count in matches)
    print("Exact state/frame cross-family equations have at most one remaining challenge solution after the stated degeneracy exclusion", flush=True)


def actual_gauges(v):
    rng = Random(180)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    points = [[sample() for _ in range(20)] for _ in range(2)]
    support = (0, 1, 64, 2048)
    words = [[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support]
    gauges = [[[1, 1] for _ in support], [[rng.getrandbits(64) or 1 for _ in range(2)] for _ in support]]
    gauge_exponent = 1 << 40
    gauges[1][0][0] = int(v.GEN**gauge_exponent)
    bits = ((0, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (1, 1, 1, 1), (0, 1, 0, 1))
    retained, controls, excluded, images, labels = [], [], [], [], None
    for bank in gauges:
        views, products_, remaining, reference = [], [], [], None
        for vector in bits:
            library, indices = set_library(v, support, words, vector, compact=True, gauges=bank)
            current_labels = [(opcode, tuple(row[column] for column in v.TABLES[opcode].count_columns)) for opcode, row in library.rows]
            if labels is None:
                labels = current_labels
            assert current_labels == labels
            if reference is None:
                reference = library.images
            assert library.images == reference
            jump = [table_products(v, library, v.OP_JUMP, side, e, beta) for side in ("push", "pull")]
            sets = [table_products(v, library, v.OP_SET, side, e, beta) for side in ("push", "pull")]
            counters = [final_evaluation(v, library, kind, indices[kind], point) for kind, point in zip(("memory", "code"), points, strict=True)]
            views.append((*jump[0][2:4], *jump[1][2:4], sets[0][2], sets[1][2], *counters))
            products_.append((jump[0][0], jump[1][0], jump[0][1], jump[1][1], jump[0][4], jump[1][4]))
            remaining.append((sets[0][1], sets[1][1]))
            assert sets[0][0] == jump[1][0] and sets[1][0] == jump[0][0]
            expected = [v.ONE] * 6
            for ordinal, (s, choice) in enumerate(zip(support, vector, strict=True)):
                pc, physical = CODE_BASE + 4 * s + 2 * choice, FRAME_BASE + 8 * ordinal + 4 * choice
                gauge, address = v.E(bank[ordinal][choice]), v.GEN**physical
                roots = []
                for side, exponent in enumerate((pc, pc + 1)):
                    constant = beta + e[0] * v.SEP_STATE + e[1] * v.GEN**exponent
                    value = constant + e[2] * address * gauge
                    expected[side] *= value**2
                    roots.append(constant / (e[2] * address))
                reciprocal = e[4] * v.GEN + e[5] * v.GEN**2 + e[6] * v.GEN**3
                bytecode = []
                for label in range(3):
                    constant = beta + e[0] * v.SEP_BYTECODE + e[1] * v.GEN ** (pc + 1) + e[2] * v.GEN**label + e[3] * v.GEN**v.OP_JUMP
                    bytecode.append(constant + reciprocal / gauge)
                    roots.append(reciprocal / constant)
                expected[2] *= bytecode[1] * bytecode[2]
                expected[3] *= bytecode[0] * bytecode[1]
                memory = []
                for label in range(3):
                    constant = beta + e[0] * v.SEP_MEM + e[1] * address * v.GEN**3 + e[2] * v.GEN**label
                    memory.append(constant + e[3] * address * gauge)
                    roots.append(constant / (e[3] * address))
                expected[4] *= memory[1] * memory[2]
                expected[5] *= memory[0] * memory[1]
                assert all(root ** (1 << 64) != root for root in roots)
                assert all(left ** (1 << (64 * h)) != right for i, left in enumerate(roots) for right in roots[i + 1 :] for h in (0, 1, 2))
            assert tuple(expected) == products_[-1]
            if bank is gauges[1] and vector == bits[0]:
                row = library.rows[0][1]
                assert row[v.SET_COLUMNS.index("fp")] == v.GEN ** (FRAME_BASE + gauge_exponent)
                assert row[v.SET_COLUMNS.index("o")] == v.GEN ** ((1 << 64) - 1 - gauge_exponent)
                assert row[v.SET_COLUMNS.index("fp")] * row[v.SET_COLUMNS.index("o")] == v.GEN**FRAME_BASE
        retained.append(views)
        assert all(len({view[column] for view in products_}) > 1 for column in range(6))
        controls.append(products_)
        excluded.append(remaining)
        images.append(reference)
    assert retained[0] == retained[1]
    assert all(left != right for left, right in zip(controls[0], controls[1], strict=True))
    assert all(excluded[0][0][column] != excluded[1][0][column] for column in range(2))
    assert all(images[0][kind].keys() == images[1][kind].keys() for kind in images[0])
    assert images[0] != images[1]
    assert FRAME_BASE + gauge_exponent > (1 << 32) - 1
    assert (1 << 64) - 1 - gauge_exponent > (1 << 32) - 1
    print(
        "Valid gauged SET/JUMP cycles preserve physical address sets, count leaves and eight retained fields; six state/bytecode/frame product formulas pass",
        flush=True,
    )
    print(
        "SET-bytecode products remain excluded; a valid encoded cycle exceeds native u32 frame/offset representations",
        flush=True,
    )
    return v, e, beta, words


def packet_incidence(v, e, beta, words):
    support, bits = (0, 1, 64, 2048), (0, 1, 0, 1)
    library, indices = set_library(v, support, words, bits, code_base=CODE_BASES[1], compact=True)
    assert all(index >> 18 == 1 for index in indices["memory"])
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    count_layout = v.bus_layout((), layout.count)
    selected = [block for block, place in zip(layout.push, bus.tables, strict=True) if place.index >> 18 == 13]
    assert len(selected) == 2 and all(block.owner == v.OP_JUMP for block in selected)
    rng, frontiers, packets = Random(181), [], []
    for randomize in (False, True):
        payload = lambda randomize=randomize: rng.getrandbits(64) if randomize else 0
        combined = cycles(v, 1, [[payload() for _ in range(3)] for _ in range(48)])[0]
        add_library(combined, library)
        xor = Library(v)
        xor.pc, xor.frame = 2048, 1 << 17
        block = xor.block(v.OP_XOR)
        for _ in range(8):
            templates = xor.templates(block, xor.fresh_frame())
            templates[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(payload())
            xor.append(templates)
        xor.verify()
        add_library(combined, xor)
        unused = set(range(1 << 19, (1 << 19) + 32))
        for index in unused:
            combined.images["memory"][int(v.GEN**index)] = tuple(payload() for _ in range(3))
        combined.verify()
        frames = [REAL_FRAME, *(PAD_FRAME + 128 * i for i in range(48)), *((1 << 17) + 128 * i for i in range(8))]
        physical = {
            "memory": indices["memory"] | unused | {frame + offset for frame in frames for offset in (0, 1, 2, 64, 65, 66)},
            "code": indices["code"] | set(range(REAL_PC, REAL_PC + 33)) | {PAD_PC, PAD_PC + 1, 2048, 2049},
        }
        assert all({int(v.GEN**index) for index in physical[kind]} == combined.images[kind].keys() for kind in physical)
        push, pull, count = ([v.ONE] * 16 for _ in range(3))
        for side, nodes, blocks in (("push", push, layout.push), ("pull", pull, layout.pull)):
            products_ = [iter(table_products(v, combined, opcode, side, e, beta)) for opcode in range(len(v.TABLES))]
            for block, place in zip(blocks, bus.tables, strict=True):
                assert place.index >> 18 == (place.index + (1 << place.variables) - 1) >> 18
                nodes[place.index >> 18] *= next(products_[block.owner])
        for kind, start, separator in (("memory", 0, v.SEP_MEM), ("code", 4, v.SEP_BYTECODE)):
            for index in physical[kind]:
                address = int(v.GEN**index)
                value = combined.images[kind][address]
                push[start + (index >> 18)] *= fingerprint(v, e, beta, separator, address, v.ONE, value)
                pull[start + (index >> 18)] *= fingerprint(v, e, beta, separator, address, v.GEN ** combined.reads[kind, address], value)
        for block, place in zip(layout.count, count_layout.tables, strict=True):
            ((column,),) = block.coordinates[0].terms
            count[place.index >> 18] *= v.GEN ** combined.exponents[block.owner, column]
        replay = gkr_replay(v, count, seed=182, details=True, bus_leaves=(push, pull))
        full_depth_prefix(v, replay, 182)
        assert replay["children"][0][1] == v.dot(v.eq_kernel(replay["challenge"]), push[1::4])
        frontiers.append((push, pull))
        packets.append(replay["children"][:2])
    assert all(frontiers[0][side][index] == frontiers[1][side][index] for side in (0, 1) for index in (1, 5, 9, 13))
    assert all(packets[0][side][1] == packets[1][side][1] for side in (0, 1)) and packets[0] != packets[1]
    print(
        "Actual depth-22 GKR prefix accepts sparse valid-cycle products: second push/pull child 1 is unchanged by all three private payload families at fixed occupancy",
        flush=True,
    )


def concrete_bound():
    base, size, total = 1 << 64, 1 << 192, BANKS * BITS
    coefficient = Fraction(24 * (1 << 32), base - 1)
    bias = coefficient**2
    assert bias < Fraction(1, 1 << 54)
    group = (size - 1) ** 6
    term = (group - 1) * ((1 + bias) / 2) ** (BITS - 7)
    assert term < Fraction(1, 4)
    assert 2 * size**8 * term < Fraction(1, 1 << 1142)
    bad_coins = Fraction(8 + 6 * total, size) + Fraction(1 + 158 * total, size - 2) + Fraction(7 * base**2, size * (size - 2))
    zeros = Fraction((1 << 24) + 16 * total, size)
    assert Fraction(1, 1 << 160) + bad_coins + zeros < Fraction(1, 1 << 159)
    assert Fraction(1, 1 << 571) / Fraction(1, 1 << 160) == Fraction(1, 1 << 411)
    print("Rational six-product decoupling: mean below 2^-571; setup exception below 2^-411 at threshold 2^-160", flush=True)
    print(
        "With all stated exclusions, six JUMP control products decouple below 2^-159 while retaining eight actual fields, not the remaining gauge-dependent view",
        flush=True,
    )


if __name__ == "__main__":
    root_exceptions()
    verifier = verifier_module()
    packet_incidence(*actual_gauges(verifier))
    reservations(verifier, BITS)
    concrete_bound()
