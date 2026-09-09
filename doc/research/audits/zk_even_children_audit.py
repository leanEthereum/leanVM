"""Joint children 1, 2, 3 using both MUL inputs; child 0 and GKR rounds remain open."""

from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_bytecode_frontier_audit import CODE_BASES
from zk_bytecode_public_library_audit import FRAME_BASE, set_library
from zk_control_composition_audit import frontier, view
from zk_control_residual_audit import add_library
from zk_count_children_audit import gkr_replay
from zk_gkr_coarse_audit import (
    PAD_FRAME,
    PAD_PC,
    REAL_FRAME,
    REAL_PC,
    check_first_packet,
    cycles,
)
from zk_gkr_first_packet_audit import fingerprint, linear_view
from zk_gkr_second_wire_audit import full_depth_prefix, parent_products, stage_wire
from zk_odd_children_audit import NOISE as XOR_NOISE
from zk_odd_children_audit import OLD_ROWS, xor_library
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations
from zk_set_payload_products_audit import BANKS, BITS

MUL_NOISE, UNUSED = 48, 1 << 19


def two_inputs(v, first, second, unused):
    library, positions, a_rows = cycles(v, 1, first)
    b_rows = []
    for index, word in enumerate(second):
        templates = library.templates((v.OP_MUL, PAD_PC, [], True), library.fresh_frame())
        templates[0][1][v.ARITH_COLUMNS.index("va_0")] = v.ONE
        for limb, value in enumerate(word):
            templates[0][1][v.ARITH_COLUMNS.index(f"vb_{limb}")] = v.E(value)
        row, closing = library.append(templates)
        positions[row], positions[closing] = (1 << 18) - 2 * MUL_NOISE + index, 60001 + MUL_NOISE + index
        b_rows.append(row)
    frames = [REAL_FRAME, *(PAD_FRAME + 128 * i for i in range(2 * MUL_NOISE))]
    indices = {
        "memory": {frame + offset for frame in frames for offset in (0, 1, 2, 64, 65, 66)} | set(range(UNUSED, UNUSED + 32)),
        "code": set(range(REAL_PC, REAL_PC + 33)) | {PAD_PC, PAD_PC + 1},
    }
    for index, word in enumerate(unused):
        library.images["memory"][int(v.GEN ** (UNUSED + index))] = tuple(word)
    assert len({positions[row] for row in (*a_rows, *b_rows)}) == 2 * MUL_NOISE
    library.verify()
    return library, positions, indices, a_rows, b_rows


def four_products(v, library, rows, input_block, e, beta):
    quads = []
    for row_id in rows:
        opcode, row = library.rows[row_id]
        flushes = v.TABLES[opcode].flushes
        factors = [
            beta + v.dot(e[:6], [form.evaluate(row.__getitem__) for form in getattr(flushes, side)[block]])
            for side, block in (("pull", input_block), ("push", input_block), ("pull", 4), ("push", 4))
        ]
        address, output = [flushes.pull[block][1].evaluate(row.__getitem__) for block in (input_block, 4)]
        d, h = e[2] * (v.ONE + v.GEN), e[1] * (address + output)
        assert factors == [factors[0], factors[0] + d, factors[0] + h, factors[0] + d + h]
        assert len(set(factors)) == 4
        quads.append(factors)
    return tuple(reduce(mul, column, v.ONE) for column in zip(*quads, strict=True))


def inverse_coordinates(prefix, free, cofactors):
    p0, p2, p3, q2, q3 = prefix
    a1, ag, xp, xm = free
    k0, k2, k3, l2, l3 = cofactors
    b1, bg = q2 / (l2 * a1), p2 / (k2 * ag)
    c1, cg = q3 / (l3 * xm), p3 / (k3 * xp)
    unused = p0 * l2 * l3 / (k0 * q2 * q3)
    return a1, ag, b1, bg, c1, cg, xp, xm, unused


def payload_factors(v, raw):
    a1, ag, b1, bg, c1, cg, xp, xm, unused = raw
    push, pull = [[v.ONE] * 16 for _ in range(2)]
    for nodes, assignments in (
        (push, {0: a1 * b1 * c1 * xm, 2: unused, 10: ag, 11: bg, 12: cg, 15: xp}),
        (pull, {0: ag * bg * cg * xp, 2: unused, 10: a1, 11: b1, 12: c1, 15: xm}),
    ):
        for index, value in assignments.items():
            nodes[index] = value
    return push, pull


def recover_from_children(v, prefix, cofactors, coefficients, children):
    p0, p2, _, q2, q3 = prefix
    k0, k2, _, l2, l3 = cofactors
    unused = p0 * l2 * l3 / (k0 * q2 * q3)
    free = []
    for side in range(2):
        offset2, slope_w, slope_a, offset3, slope_b, slope_x = coefficients[6 * side : 6 * side + 6]
        input_a = (children[side][2] + offset2 + slope_w * unused) / slope_a
        input_b = (p2 / k2 if side == 0 else q2 / l2) / input_a
        xor_product = (children[side][3] + offset3 + slope_b * input_b) / slope_x
        free.append((input_a, xor_product))
    return inverse_coordinates(prefix, (free[1][0], free[0][0], free[0][1], free[1][1]), cofactors)


def actual_joint_map(v):
    rng = Random(187)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    point, y = [sample() for _ in range(20)], [sample(), sample()]
    points = [[sample() for _ in range(20)] for _ in range(2)]
    words = [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in range(2)] for _ in range(BANKS)]
    gauges = [[[rng.getrandbits(64) or 1 for _ in range(2)] for _ in range(2)] for _ in range(BANKS)]
    old_xor = [rng.getrandbits(64) for _ in range(OLD_ROWS)]
    sizes = (MUL_NOISE, MUL_NOISE, XOR_NOISE, 32)
    generate = lambda: [[[rng.getrandbits(64) for _ in range(3)] for _ in range(size)] for size in sizes]
    left, right = generate(), generate()
    zero = [[[0] * 3 for _ in range(size)] for size in sizes]
    both = [[[a ^ b for a, b in zip(x, z, strict=True)] for x, z in zip(xs, zs, strict=True)] for xs, zs in zip(left, right, strict=True)]
    cases = [zero, *[[left[j] if j == i else zero[j] for j in range(4)] for i in range(4)], left, right, both]
    invariants, retained, boundaries, children, frontier_cofactors = [], [], [], [], []
    for a_words, b_words, x_words, u_words in cases:
        library, positions, indices, a_rows, b_rows = two_inputs(v, a_words, b_words, u_words)
        a1, ag, c1a, cga = four_products(v, library, a_rows, 2, e, beta)
        b1, bg, c1b, cgb = four_products(v, library, b_rows, 3, e, beta)
        c1, cg = c1a * c1b, cga * cgb
        unused = reduce(mul, (fingerprint(v, e, beta, v.SEP_MEM, int(v.GEN ** (UNUSED + i)), v.ONE, word) for i, word in enumerate(u_words)), v.ONE)
        boundary = linear_view(v, library, positions, layout, bus, point, y, e, indices["memory"])
        xor, x_positions, x_indices = xor_library(v, old_xor, x_words)
        xa1, xag, xc1, xcg = four_products(v, xor, [2 * (OLD_ROWS + i) for i in range(XOR_NOISE)], 2, e, beta)
        xp, xm = xag * xcg, xa1 * xc1
        x_boundary = linear_view(v, xor, x_positions, layout, bus, point, y, e, x_indices["memory"])
        boundaries.append([a + b for a, b in zip(boundary, x_boundary, strict=True)])
        add_library(library, xor)
        for kind, values in indices.items():
            values.update(x_indices[kind])
        for bank in range(BANKS):
            local, local_indices = set_library(
                v,
                (0, 64),
                words[bank],
                (0, 1),
                code_base=CODE_BASES[bank],
                frame_base=FRAME_BASE + 8 * BITS * bank,
                compact=True,
                gauges=gauges[bank],
            )
            add_library(library, local)
            for kind, values in indices.items():
                values.update(local_indices[kind])
        library.verify()
        retained.append((*view(v, library, indices, e, beta, points), dict(library.reads), dict(library.exponents)))
        push, pull, count = frontier(v, library, indices, e, beta, xor_log=6)
        first_p, first_q = parent_products(push), parent_products(pull)
        cofactors = (
            first_p[0] / (unused * a1 * b1 * c1 * xm),
            first_p[2] / (ag * bg),
            first_p[3] / (cg * xp),
            first_q[2] / (a1 * b1),
            first_q[3] / (c1 * xm),
        )
        prefix = first_p[0], first_p[2], first_p[3], first_q[2], first_q[3]
        raw = a1, ag, b1, bg, c1, cg, xp, xm, unused
        assert inverse_coordinates(prefix, (a1, ag, xp, xm), cofactors) == raw
        factors = payload_factors(v, raw)
        node_cofactors = [
            [node / factor for node, factor in zip(nodes, masks, strict=True)] for nodes, masks in zip((push, pull), factors, strict=True)
        ]
        frontier_cofactors.append(node_cofactors)
        replay = gkr_replay(v, count, seed=188, details=True, bus_leaves=(push, pull))
        full_depth_prefix(v, replay, 188)
        weights = v.eq_kernel(replay["challenge"])
        child_coefficients = []
        for side, nodes, input_a, input_b, xor_product in ((0, push, ag, bg, xp), (1, pull, a1, b1, xm)):
            offset2 = weights[1] * nodes[6] + weights[3] * nodes[14]
            slope_w, slope_a = weights[0] * nodes[2] / unused, weights[2] * nodes[10] / input_a
            offset3 = weights[0] * nodes[3] + weights[1] * nodes[7]
            slope_b, slope_x = weights[2] * nodes[11] / input_b, weights[3] * nodes[15] / xor_product
            assert replay["children"][side][2] == offset2 + slope_w * unused + slope_a * input_a
            assert replay["children"][side][3] == offset3 + slope_b * input_b + slope_x * xor_product
            child_coefficients.extend((offset2, slope_w, slope_a, offset3, slope_b, slope_x))
        assert recover_from_children(v, prefix, cofactors, child_coefficients, replay["children"]) == raw
        for side, nodes, xor_product, output in ((0, push, xp, cg), (1, pull, xm, c1)):
            offset0 = v.dot(weights[:3], nodes[0:12:4])
            numerator = weights[3] * node_cofactors[side][12] * output * xor_product
            assert replay["children"][side][0] == offset0 + numerator / xor_product
        invariants.append((*cofactors, *child_coefficients))
        children.append(tuple(replay["children"][side][j] for j in (1, 2, 3) for side in (0, 1)))
        sampled_prefix, sampled_free = tuple(sample() for _ in range(5)), tuple(sample() for _ in range(4))
        aa1, aag, bb1, bbg, cc1, ccg, xxp, xxm, ww = inverse_coordinates(sampled_prefix, sampled_free, cofactors)
        k0, k2, k3, l2, l3 = cofactors
        assert sampled_prefix == (k0 * ww * aa1 * bb1 * cc1 * xxm, k2 * aag * bbg, k3 * ccg * xxp, l2 * aa1 * bb1, l3 * cc1 * xxm)
        p0, p2, p3, q2, q3 = sampled_prefix
        q0 = first_p[1] * p0 * p2 * p3 / (first_q[1] * q2 * q3)
        check_first_packet(v, [p0, first_p[1], p2, p3], [q0, first_q[1], q2, q3], parent_products(count))
        changed_raw = inverse_coordinates(prefix, sampled_free, cofactors)
        changed = [
            [cofactor * factor for cofactor, factor in zip(fixed, masks, strict=True)]
            for fixed, masks in zip(node_cofactors, payload_factors(v, changed_raw), strict=True)
        ]
        changed_replay = gkr_replay(v, count, seed=188, details=True, bus_leaves=changed)
        full_depth_prefix(v, changed_replay, 188)
        assert changed_replay["view"][0] == replay["view"][0]
        assert recover_from_children(v, prefix, cofactors, child_coefficients, changed_replay["children"]) == changed_raw
        reconstructed_raw = recover_from_children(v, prefix, cofactors, child_coefficients, changed_replay["children"])
        reconstructed = [
            [cofactor * factor for cofactor, factor in zip(fixed, masks, strict=True)]
            for fixed, masks in zip(node_cofactors, payload_factors(v, reconstructed_raw), strict=True)
        ]
        assert stage_wire(v, (*reconstructed, count), replay["equality"], replay["challenge"], replay["combiner"]) == changed_replay["view"][3]
    assert all(value == invariants[0] for value in invariants)
    assert all(value == frontier_cofactors[0] for value in frontier_cofactors)
    assert all(value == retained[0] for value in retained)
    assert all(value[:2] == children[0][:2] for value in children)
    assert all(v.E.sum(boundaries[index][column] for index in (0, 5, 6, 7)) == v.ZERO for column in range(11))
    print(
        "Two valid MUL input families give six independent product coordinates after combining their outputs; XOR and unused memory give three more",
        flush=True,
    )
    print("The nine-coordinate monomial map has an explicit inverse for the first packet plus four remaining masks", flush=True)
    print(
        "Actual child-2 and child-3 affine coefficients are independent of every private payload family; child 1 and the retained controls stay fixed",
        flush=True,
    )
    print("All tested product frontiers replay both layers through the depth-22 verifier; no complete VM trace is instantiated", flush=True)
    print(
        "At fixed prefix and complementary cofactors, children 2 and 3 recover all nine product coordinates and the complete second-layer wire",
        flush=True,
    )
    print(
        "This payload hybrid has no remaining conditional randomness for child 0 or mixed rounds; their cofactor-dependent law still needs simulation",
        flush=True,
    )


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    rank = Fraction(base**2, (size - 2) ** 2)
    mul_error = Fraction((1 << 23) + 8 * MUL_NOISE + 8, size) + rank + Fraction(1, 1 << 384)
    xor_error = Fraction((1 << 23) + 8 * XOR_NOISE + 8, size) + rank + Fraction(1, 1 << 216)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary_error, _ = error_bound()
    assert 2 * mul_error + xor_error + unused_error + boundary_error + Fraction(1, 1 << 159) + Fraction(12, size) < Fraction(1, 1 << 155)
    print("Joint first packet, boundary and second children 1, 2, 3 reduce below 2^-155 to the same seven-field residual", flush=True)
    print("Child 0, both mixed round polynomials, the residual law and all later protocol obligations remain open", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    actual_joint_map(verifier)
    reservations(verifier, BITS, xor_rows=OLD_ROWS + XOR_NOISE, mul_rows=2 * MUL_NOISE)
    concrete_bound()
