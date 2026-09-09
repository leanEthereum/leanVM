"""Joint odd GKR children via extra XOR words, excluding even children and rounds."""

from collections import Counter
from fractions import Fraction
from functools import reduce
from itertools import product
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_column_count_audit import Library
from zk_control_composition_audit import combine, frontier, view
from zk_control_residual_audit import add_library
from zk_count_children_audit import gkr_replay
from zk_gkr_first_packet_audit import linear_view
from zk_gkr_second_wire_audit import full_depth_prefix
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations
from zk_set_payload_products_audit import BANKS, BITS

NOISE, OLD_ROWS = 36, 8
XOR_PC, XOR_FRAME = 2048, 1 << 17


def quadratic_obstruction():
    for degree, modulus in ((2, 0b111), (4, 0b10011)):
        f = Field(degree, modulus)
        laws = []
        for coefficient in (1, 2):
            counts = Counter()
            for u, v, r, s in product(range(1, f.size), repeat=4):
                term = reduce(lambda a, b: f.mul[a][b], (coefficient, u, r, f.inv[v], f.inv[s]), 1)
                counts[u, v ^ term, r, s] += 1
            assert len(counts) == f.size * (f.size - 1) ** 3 // 2
            assert set(counts.values()) == {1, 2}
            laws.append(counts)
        distance = Fraction(sum(abs(laws[0][key] - laws[1][key]) for key in laws[0].keys() | laws[1].keys()), 2 * (f.size - 1) ** 4)
        assert distance == Fraction(f.size, 2 * (f.size - 1))
    print(
        "The idealized control-only odd-child map has half-field conditional support; distinct coefficients give distance q/(2(q-1)), not a full-VM attack",
        flush=True,
    )


def xor_library(v, old_values, payloads):
    library, positions = Library(v), {}
    library.pc, library.frame = XOR_PC, XOR_FRAME
    block = library.block(v.OP_XOR)
    words = [[value, 0, 0] for value in old_values] + payloads
    for index, word in enumerate(words):
        templates = library.templates(block, library.fresh_frame())
        for limb, value in enumerate(word):
            templates[0][1][v.ARITH_COLUMNS.index(f"va_{limb}")] = v.E(value)
        row, closing = library.append(templates)
        positions[row], positions[closing] = index, 1536 + index
    library.verify()
    indices = {
        "code": {XOR_PC, XOR_PC + 1},
        "memory": {XOR_FRAME + 128 * index + offset for index in range(len(words)) for offset in (0, 1, 2, 64, 65, 66)},
    }
    return library, positions, indices


def actual_masks(v):
    rng = Random(185)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    assert bus.depth == 22 and layout.stack_log == 24
    old_layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    old_bus = v.bus_layout((0, 20, 20), old_layout.push)
    for opcode in (v.OP_MUL, v.OP_JUMP, v.OP_SET):
        selected = lambda blocks, places, opcode=opcode: [place for block, place in zip(blocks, places, strict=True) if block.owner == opcode]
        assert selected(layout.push, bus.tables) == selected(old_layout.push, old_bus.tables)
    xor_blocks = [place for block, place in zip(layout.push, bus.tables, strict=True) if block.owner == v.OP_XOR]
    assert all(place.index >> 18 == (place.index + 63) >> 18 == 15 for place in xor_blocks)
    point, y = [sample() for _ in range(20)], [sample(), sample()]
    points = [[sample() for _ in range(20)] for _ in range(2)]
    words = [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in range(2)] for _ in range(BANKS)]
    gauges = [[[rng.getrandbits(64) or 1 for _ in range(2)] for _ in range(2)] for _ in range(BANKS)]
    old_values = [rng.getrandbits(64) for _ in range(OLD_ROWS)]
    left, right = [[[rng.getrandbits(64) for _ in range(3)] for _ in range(NOISE)] for _ in range(2)]
    cases = [[[0] * 3 for _ in range(NOISE)], left, right, [[a ^ b for a, b in zip(x, z, strict=True)] for x, z in zip(left, right, strict=True)]]
    boundaries, invariants, products_, children, retained = [], [], [], [], []
    for payloads in cases:
        xor, positions, xor_indices = xor_library(v, old_values, payloads)
        quads = []
        for index in range(NOISE):
            row_index = OLD_ROWS + index
            row = xor.rows[2 * row_index][1]
            quad = [
                beta + v.dot(e[:6], [form.evaluate(row.__getitem__) for form in getattr(v.TABLES[v.OP_XOR].flushes, side)[block]])
                for side, block in (("pull", 2), ("push", 2), ("pull", 4), ("push", 4))
            ]
            d = e[2] * (v.ONE + v.GEN)
            h = e[1] * v.GEN ** (XOR_FRAME + 128 * row_index) * (v.ONE + v.GEN**2)
            assert quad == [quad[0], quad[0] + d, quad[0] + h, quad[0] + d + h]
            assert len(set(quad)) == 4
            quads.append(quad)
        a1, ag, c1, cg = [reduce(mul, column, v.ONE) for column in zip(*quads, strict=True)]
        u_plus, u_minus = ag * cg, a1 * c1
        products_.append((u_plus, u_minus))
        boundary = linear_view(v, xor, positions, layout, bus, point, y, e, xor_indices["memory"])
        boundaries.append(boundary)
        library, indices = combine(v, words, gauges, (0, 1) * 4, 0)
        add_library(library, xor)
        for kind, values in indices.items():
            values.update(xor_indices[kind])
        library.verify()
        free, residual, controls, seed = view(v, library, indices, e, beta, points)
        retained.append((free, residual, controls, seed, dict(library.reads), dict(library.exponents)))
        push, pull, count = frontier(v, library, indices, e, beta, xor_log=6)
        replay = gkr_replay(v, count, seed=186, details=True, bus_leaves=(push, pull))
        full_depth_prefix(v, replay, 186)
        weights = v.eq_kernel(replay["challenge"])
        cofactors = push[15] / u_plus, pull[15] / u_minus
        offsets = [v.dot(weights[:3], nodes[3:12:4]) for nodes in (push, pull)]
        actual = replay["children"][0][3], replay["children"][1][3]
        assert actual == tuple(
            offset + weights[3] * cofactor * value for offset, cofactor, value in zip(offsets, cofactors, (u_plus, u_minus), strict=True)
        )
        invariants.append((*cofactors, *offsets))
        children.append((replay["children"][0][1], replay["children"][1][1], *actual))
    assert all(value == invariants[0] for value in invariants)
    assert all(value == retained[0] for value in retained)
    assert all(value[:2] == children[0][:2] for value in children)
    assert all(value[2:] != children[0][2:] for value in children[1:])
    assert len(set(products_)) == len(cases)
    assert all(v.E.sum(column) == v.ZERO for column in zip(*boundaries, strict=True))
    assert all(
        all(a + b == boundaries[0][i] + boundaries[0][i + 4] for i, (a, b) in enumerate(zip(boundary[:4], boundary[4:8], strict=True)))
        for boundary in boundaries
    )
    print("New full-word XOR cycles have four distinct shifted factors, two product masks and a seven-field linear boundary view", flush=True)
    print(
        "Actual node-15 cofactors and child-3 offsets are payload-independent; child 1, SET/JUMP products, bytecode data and final counts stay fixed",
        flush=True,
    )
    print("Both GKR layers replay through the depth-22 reader; XOR height 6 leaves every MUL/JUMP/SET placement unchanged", flush=True)


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    ratio_squared = Fraction(16 * size, (base**2 - 4) ** 2)
    mixing_squared = Fraction(((size - 1) ** 2 - 1) * size**7, 4) * ratio_squared**NOISE
    assert mixing_squared < Fraction(1, 1 << 432)
    rank = Fraction(base**2, (size - 2) ** 2)
    xor_error = Fraction((1 << 23) + 8 * NOISE + 8, size) + rank + Fraction(1, 1 << 216)
    assert xor_error < Fraction(1, 1 << 168)
    mul_error = Fraction((1 << 23) + 8 * 48 + 8, size) + rank + Fraction(1, 1 << 384)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary_error, _ = error_bound()
    assert mul_error + unused_error + xor_error + boundary_error + Fraction(1, 1 << 159) + Fraction(8, size) < Fraction(1, 1 << 155)
    print("Two-product XOR mixing below 2^-216, including exclusions below 2^-168; joint odd-child reduction below 2^-155", flush=True)
    print("The seven-field residual, even children, second-layer polynomials and later protocol remain unresolved", flush=True)


if __name__ == "__main__":
    quadratic_obstruction()
    verifier = verifier_module()
    actual_masks(verifier)
    reservations(verifier, BITS, xor_rows=OLD_ROWS + NOISE)
    concrete_bound()
