"""Compose public words and frame gauges, retaining seven actual residual fields."""

from fractions import Fraction
from functools import reduce
from itertools import product
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound, final_evaluation
from zk_bytecode_frontier_audit import BANKS, CODE_BASES, code_frontier
from zk_bytecode_public_library_audit import FRAME_BASE, set_library
from zk_column_count_audit import Library
from zk_control_residual_audit import add_library, outside_ratio
from zk_count_children_audit import gkr_replay
from zk_gkr_coarse_audit import check_first_packet
from zk_gkr_first_packet_audit import fingerprint
from zk_gkr_second_wire_audit import full_depth_prefix
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations, table_products
from zk_set_payload_products_audit import BITS

SUPPORT = (0, 64)
OUTSIDE_PC, OUTSIDE_FRAME = 900000, 32


def combine(v, words, gauges, bits, outside):
    library, alternatives = Library(v), []
    indices = {"code": set(), "memory": set()}
    for choice in (0, 1):
        pc, frame = OUTSIDE_PC + 2 * choice, OUTSIDE_FRAME + 128 * choice
        templates = library.templates((v.OP_MUL, pc, [], True), v.GEN**frame)
        library.register(templates)
        alternatives.append(templates)
        indices["code"].update((pc, pc + 1))
        indices["memory"].update(frame + offset for offset in (0, 1, 2, 64, 65, 66))
    library.append(alternatives[outside])
    library.append(alternatives[outside])
    for bank in range(BANKS):
        local, selected = set_library(
            v,
            SUPPORT,
            words[bank],
            bits[bank * len(SUPPORT) : (bank + 1) * len(SUPPORT)],
            code_base=CODE_BASES[bank],
            frame_base=FRAME_BASE + 8 * BITS * bank,
            compact=True,
            gauges=gauges[bank],
        )
        add_library(library, local)
        for kind, values in indices.items():
            values.update(selected[kind])
    library.verify()
    return library, indices


def view(v, library, indices, e, beta, points):
    sets = [table_products(v, library, v.OP_SET, side, e, beta) for side in ("push", "pull")]
    jumps = [table_products(v, library, v.OP_JUMP, side, e, beta) for side in ("push", "pull")]
    counters = [final_evaluation(v, library, kind, indices[kind], point) for kind, point in zip(("memory", "code"), points, strict=True)]
    residual = (*jumps[0][2:4], *jumps[1][2:4], *counters, outside_ratio(v, library, e, beta))
    free = (
        *code_frontier(v, library, indices["code"], e, beta),
        sets[1][1],
        sets[0][2],
        sets[1][2],
        jumps[0][0],
        jumps[1][0],
        jumps[0][1],
        jumps[1][1],
        jumps[0][4],
        jumps[1][4],
    )
    seed = reduce(
        mul,
        (fingerprint(v, e, beta, v.SEP_BYTECODE, address, v.ONE, payload) for address, payload in library.images["code"].items()),
        v.ONE,
    )
    reconstructed, controls = reconstruct(free, residual, seed)
    assert reconstructed == (sets[0][1], sets[1][1], sets[0][2], sets[1][2])
    assert controls == (*jumps[0], *jumps[1])
    return free, residual, controls, seed


def reconstruct(free, residual, public_seed):
    d = reduce(mul, free[:4])
    c_minus, m_plus, m_minus = free[4:7]
    state_plus, state_minus, code_plus, code_minus, frame_plus, frame_minus = free[7:]
    c_plus = d * c_minus * code_minus / (public_seed * residual[-1] * code_plus)
    controls = (
        state_plus,
        code_plus,
        *residual[:2],
        frame_plus,
        state_minus,
        code_minus,
        *residual[2:4],
        frame_minus,
    )
    return (c_plus, c_minus, m_plus, m_minus), controls


def word_coefficients(v, library, words, gauges, e, beta):
    for bank, index, alternative in product(range(BANKS), range(len(SUPPORT)), (0, 1)):
        pc = CODE_BASES[bank] + 4 * SUPPORT[index] + 2 * alternative
        frame = FRAME_BASE + 8 * BITS * bank + 8 * index + 4 * alternative
        gauge = v.E(gauges[bank][index][alternative])
        word = words[bank][index][alternative]
        for label in range(3):
            code = fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN**pc), v.GEN**label, library.images["code"][int(v.GEN**pc)])
            memory = fingerprint(v, e, beta, v.SEP_MEM, int(v.GEN**frame), v.GEN**label, library.images["memory"][int(v.GEN**frame)])
            code_constant = beta + e[0] * v.SEP_BYTECODE + e[1] * v.GEN**pc + e[2] * v.GEN**label + e[3] * v.GEN**v.OP_SET + e[4] / gauge
            memory_constant = beta + e[0] * v.SEP_MEM + e[1] * v.GEN**frame + e[2] * v.GEN**label
            assert code == code_constant + v.dot(e[5:8], [v.E(value) for value in word])
            assert memory == memory_constant + v.dot(e[3:6], [v.E(value) for value in word])


def frontier(v, library, indices, e, beta):
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    bus, counts = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus == v.bus_layout((0, 20, 20), layout.pull)
    channels = [[v.ONE] * 16 for _ in range(3)]
    for side, nodes, blocks in (("push", channels[0], layout.push), ("pull", channels[1], layout.pull)):
        products_ = [iter(table_products(v, library, opcode, side, e, beta)) for opcode in range(len(v.TABLES))]
        for block, place in zip(blocks, bus.tables, strict=True):
            assert place.index >> 18 == (place.index + (1 << place.variables) - 1) >> 18
            nodes[place.index >> 18] *= next(products_[block.owner])
    for kind, start, separator in (("memory", 0, v.SEP_MEM), ("code", 4, v.SEP_BYTECODE)):
        assert {int(v.GEN**index) for index in indices[kind]} == library.images[kind].keys()
        for index in indices[kind]:
            address = int(v.GEN**index)
            payload = library.images[kind][address]
            channels[0][start + (index >> 18)] *= fingerprint(v, e, beta, separator, address, v.ONE, payload)
            channels[1][start + (index >> 18)] *= fingerprint(v, e, beta, separator, address, v.GEN ** library.reads[kind, address], payload)
    for block, place in zip(layout.count, counts.tables, strict=True):
        assert place.index >> 18 == (place.index + (1 << place.variables) - 1) >> 18
        ((column,),) = block.coordinates[0].terms
        channels[2][place.index >> 18] *= v.GEN ** library.exponents[block.owner, column]
    return channels


def second_child(v, library, indices, e, beta, free, residual, sample):
    push, pull, count = frontier(v, library, indices, e, beta)
    replay = gkr_replay(v, count, seed=184, details=True, bus_leaves=(push, pull))
    full_depth_prefix(v, replay, 184)
    weights = v.eq_kernel(replay["challenge"])
    assert push[13] == free[7] * free[9] and pull[13] == free[8] * free[10]
    assert pull[5] == free[1]
    ratio = free[5] / free[6] * free[11] / free[12] * residual[0] * residual[1] / (residual[2] * residual[3])
    cofactors = push[1], pull[1] / ratio, push[9], pull[9]
    offsets = (
        weights[0] * cofactors[0] + weights[1] * push[5] + weights[2] * cofactors[2],
        weights[0] * cofactors[1] * ratio + weights[1] * free[1] + weights[2] * cofactors[3],
    )
    actual = replay["children"][0][1], replay["children"][1][1]
    assert actual == (offsets[0] + weights[3] * free[9] * free[7], offsets[1] + weights[3] * free[10] * free[8])
    for side in range(2):
        desired = sample()
        slope = weights[3] * free[9 + side]
        state = (desired + offsets[side]) / slope
        assert offsets[side] + slope * state == desired
        assert (offsets[side] + slope * v.ZERO) == offsets[side]
    return cofactors


def joint_dependencies(v):
    rng = Random(183)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta, points = v.eq_kernel([sample() for _ in range(4)]), sample(), [[sample() for _ in range(20)] for _ in range(2)]
    word_seeds = [[[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in SUPPORT] for _ in range(BANKS)] for _ in range(2)]
    scale_seeds = [[[[rng.getrandbits(64) or 1 for _ in range(2)] for _ in SUPPORT] for _ in range(BANKS)] for _ in range(2)]
    vectors = ((0,) * 8, (1,) * 8, (0, 1) * 4, (1, 0, 0, 0, 0, 0, 0, 0))
    results, images, cofactors, counts = {}, {}, {}, None
    for w, a, outside, choice in product(range(2), range(2), range(2), range(len(vectors))):
        library, indices = combine(v, word_seeds[w], scale_seeds[a], vectors[choice], outside)
        key = w, a
        if key not in images:
            images[key] = library.images
        assert library.images == images[key]
        if counts is None:
            counts = dict(library.exponents)
        assert dict(library.exponents) == counts
        word_coefficients(v, library, word_seeds[w], scale_seeds[a], e, beta)
        free, residual, controls, seed = view(v, library, indices, e, beta, points)
        results[w, a, outside, choice] = free, residual, controls, seed
        current = second_child(v, library, indices, e, beta, free, residual, sample)
        cofactor_key = w, a, outside
        if cofactor_key not in cofactors:
            cofactors[cofactor_key] = current
        assert current == cofactors[cofactor_key]
        random_free = tuple(sample() for _ in range(13))
        sets, random_controls = reconstruct(random_free, residual, seed)
        assert reduce(mul, random_free[:4]) == seed * residual[-1] * sets[0] / sets[1] * random_controls[1] / random_controls[6]
        p0, p2, p3, q2, q3 = [sample() for _ in range(5)]
        d = reduce(mul, random_free[:4])
        q0 = seed * p0 * p2 * p3 / (d * q2 * q3)
        check_first_packet(v, [p0, seed, p2, p3], [q0, d, q2, q3], [v.GEN ** sum(counts.values()), v.ONE, v.ONE, v.ONE])
    for a, outside, choice in product(range(2), range(2), range(len(vectors))):
        left, right = [results[w, a, outside, choice] for w in range(2)]
        assert left[1:3] == right[1:3]
        assert left[0][:7] != right[0][:7] and left[0][7:] == right[0][7:]
    for w, outside, choice in product(range(2), range(2), range(len(vectors))):
        left, right = [results[w, a, outside, choice] for a in range(2)]
        assert left[1] == right[1]
        assert left[0][7:] != right[0][7:] and left[0][:7] != right[0][:7]
    for outside in range(2):
        assert len({results[w, a, outside, choice][1][-1] for w, a, choice in product(range(2), range(2), range(len(vectors)))}) == 1
    assert results[0, 0, 0, 0][1][-1] != results[0, 0, 1, 0][1][-1]
    print("Scaled SET offsets change only the word-independent fingerprint constants; the previous joint word coefficients remain exact", flush=True)
    print(
        "The joint dependency pattern is triangular: words preserve ten JUMP products and counters; scales preserve the six-field residual",
        flush=True,
    )
    print(
        "Common images and count products survive every private choice; the outside MUL bytecode ratio remains a genuine seventh residual", flush=True
    )
    print("Thirteen free products reconstruct all SET/JUMP products and consistent first packets through the reference verifier", flush=True)
    print(
        "Actual second push/pull child 1 is affine in the two state products; all remaining offsets factor through retained products and fixed cofactors",
        flush=True,
    )
    print(
        "Both layers replay through the depth-22 verifier on valid local-cycle products; the affine sampler omits the two state products and other second-layer messages",
        flush=True,
    )


def concrete_bound():
    base, size, total = 1 << 64, 1 << 192, BANKS * BITS
    word_mean, gauge_mean = Fraction(1, 1 << 383), Fraction(1, 1 << 571)
    threshold = Fraction(1, 1 << 160)
    assert (word_mean + gauge_mean) / threshold < Fraction(1, 1 << 222)
    word_bad = Fraction(8, size) + Fraction(1, size - 2) + Fraction(2 * base**2 + 2 * base, (size - 2) ** 2)
    gauge_bad = Fraction(8 + 6 * total, size) + Fraction(1 + 158 * total, size - 2) + Fraction(7 * base**2, size * (size - 2))
    zeros = Fraction(2 * (1 << 24) + 56 * total, size)
    products_error = threshold + word_bad + gauge_bad + zeros
    assert products_error < Fraction(1, 1 << 159)
    rank = Fraction(base**2, (size - 2) ** 2)
    mul_error = Fraction((1 << 23) + 8 * 48 + 8, size) + rank + Fraction(1, 1 << 384)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary_error, _ = error_bound()
    assert mul_error + unused_error + boundary_error + products_error + Fraction(4, size) < Fraction(1, 1 << 155)
    print("Combined public-seed exception below 2^-222; thirteen-product decoupling below 2^-159", flush=True)
    print(
        "First-packet/boundary plus second child-1 pair reduce below 2^-155 to seven actual fields; state products and other second-layer messages are omitted",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    joint_dependencies(verifier)
    reservations(verifier, BITS)
    concrete_bound()
