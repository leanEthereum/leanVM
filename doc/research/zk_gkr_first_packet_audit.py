"""Reduce the first-packet/boundary view to a bytecode product/evaluation pair."""

from fractions import Fraction
from functools import reduce
from itertools import permutations, product
from operator import mul
from random import Random
from types import FunctionType

from zk_bus_boundary_audit import error_bound, final_evaluation, switch_library
from zk_bus_packet_audit import table_packets, weight
from zk_gkr_coarse_audit import (
    PAD_FRAME,
    PAD_PC,
    REAL_FRAME,
    REAL_PC,
    check_first_packet,
    cycles,
    layout_certificate,
)
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module

NOISE, UNUSED = 48, 1 << 19
CODE_BASE, MEMORY_PC = 1 << 16, (1 << 16) + (1 << 13)


def fingerprint(v, e, beta, separator, address, count, payload):
    assert all(0 <= value < 1 << 64 for value in (address, *payload))
    values = (separator, v.E(address), count, *(v.E(value) for value in payload))
    return beta + v.dot(e[: len(values)], values)


def sparse_packet(v, library, positions, layout, bus, e, beta):
    packet = [[v.ONE] * 4 for _ in range(3)]
    count_layout = v.bus_layout((), layout.count)
    for side, blocks, placements in ((0, layout.push, bus.tables), (1, layout.pull, bus.tables), (2, layout.count, count_layout.tables)):
        for block, placement in zip(blocks, placements, strict=True):
            assert placement.index >> 20 == (placement.index + (1 << placement.variables) - 1) >> 20
            for row_id, (opcode, row) in enumerate(library.rows):
                if opcode != block.owner:
                    continue
                coordinates = [form.evaluate(row.__getitem__) for form in block.coordinates]
                value = coordinates[0] if side == 2 else beta + v.dot(e[: len(coordinates)], coordinates)
                packet[side][(placement.index + positions[row_id]) >> 20] *= value
    for kind, separator, child in (("memory", v.SEP_MEM, 0), ("code", v.SEP_BYTECODE, 1)):
        for address, payload in library.images[kind].items():
            packet[0][child] *= fingerprint(v, e, beta, separator, address, v.ONE, payload)
            packet[1][child] *= fingerprint(v, e, beta, separator, address, v.GEN ** library.reads[kind, address], payload)
    check_first_packet(v, *packet)
    return packet


def linear_view(v, library, positions, layout, bus, point, y, e, memory_indices):
    push, pull = table_packets(v, library, positions, bus, layout, point, e)
    memory, z = [v.ZERO] * 3, [*y, *point]
    for index in memory_indices:
        payload = [v.E(value) for value in library.images["memory"][int(v.GEN**index)]]
        global_index = bus.framework[1].index + index
        contribution = weight(v, point, global_index >> 2) * v.dot(e[3:6], payload)
        push[global_index % 4] += contribution
        pull[global_index % 4] += contribution
        for lane, value in enumerate(payload):
            memory[lane] += weight(v, z[: layout.log_memory], index) * value
    return push + pull + memory


def incidence_certificate():
    matrix = [[1, 0, 1, 0, 1], [0, 1, 0, 0, 0], [0, 0, 0, 1, 0], [1, 0, 0, 0, 0], [0, 0, 1, 0, 0]]
    determinant = sum(
        (-1) ** sum(order[i] > order[j] for i in range(5) for j in range(i + 1, 5)) * reduce(mul, (matrix[i][order[i]] for i in range(5)), 1)
        for order in permutations(range(5))
    )
    assert abs(determinant) == 1
    f, seen = Field(2, 0b111), set()
    multiply = lambda *values: reduce(lambda a, b: f.mul[a][b], values, 1)
    for a1, ag, c1, cg, unused in product(range(1, 4), repeat=5):
        p0, p2, p3, q2, q3 = multiply(unused, a1, c1), ag, cg, a1, c1
        q0 = multiply(unused, 2, f.inv[3], ag, cg)
        assert multiply(p0, 2, p2, p3) == multiply(q0, 3, q2, q3)
        assert multiply(p0, f.inv[multiply(q2, q3)]) == unused
        seen.add((p0, p2, p3, q2, q3))
    assert len(seen) == 3**5
    print(
        "Exact integer determinant is a unit; exhaustive small-field packet reconstruction preserves balance and all five free coordinates",
        flush=True,
    )


def actual_incidence(v):
    layout, bus = layout_certificate(v, NOISE)
    assert bus == v.bus_layout((0, 20, 20), layout.pull)
    assert [place.index for place in bus.framework[1:]] == [0, 1 << 20]
    assert all(place.index >= 2 << 20 for place in bus.tables)
    rng = Random(165)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    point, y = [sample() for _ in range(20)], [sample(), sample()]
    generate = lambda n: [[rng.getrandbits(64) for _ in range(3)] for _ in range(n)]
    xor = lambda a, b: [[x ^ y for x, y in zip(left, right, strict=True)] for left, right in zip(a, b, strict=True)]
    zero_mul, zero_unused = [(0, 0, 0)] * NOISE, [(0, 0, 0)] * 32
    left, right, unused_left, unused_right = generate(NOISE), generate(NOISE), generate(32), generate(32)
    cases = [(payload, zero_unused) for payload in (zero_mul, left, right, xor(left, right))]
    cases += [(zero_mul, payload) for payload in (unused_left, unused_right, xor(unused_left, unused_right))]
    memory_indices = {REAL_FRAME + offset for offset in (0, 1, 2, 64, 65, 66)}
    memory_indices |= {PAD_FRAME + 128 * row + offset for row in range(NOISE) for offset in (0, 1, 2, 64, 65, 66)}
    memory_indices |= set(range(UNUSED, UNUSED + 32))
    code_indices = {*range(REAL_PC, REAL_PC + 33), PAD_PC, PAD_PC + 1}
    cofactors, views, residuals, code_images, counts = [], [], [], [], []
    for payloads, unused_payloads in cases:
        library, positions, rows = cycles(v, 1, payloads)
        for offset, payload in enumerate(unused_payloads):
            address = int(v.GEN ** (UNUSED + offset))
            assert address not in library.images["memory"]
            library.images["memory"][address] = tuple(int(v.E(value)) for value in payload)
        library.verify()
        quads = []
        for index, row_id in enumerate(rows):
            row = library.rows[row_id][1]
            quad = [
                beta + v.dot(e[:6], [form.evaluate(row.__getitem__) for form in getattr(v.TABLES[v.OP_MUL].flushes, side)[block]])
                for side, block in (("pull", 2), ("push", 2), ("pull", 4), ("push", 4))
            ]
            d, h = e[2] * (v.ONE + v.GEN), e[1] * v.GEN ** (PAD_FRAME + 128 * index) * (v.ONE + v.GEN**2)
            assert quad == [quad[0], quad[0] + d, quad[0] + h, quad[0] + d + h]
            assert len(set(map(int, quad))) == 4
            quads.append(quad)
        a1, ag, c1, cg = [reduce(mul, values, v.ONE) for values in zip(*quads, strict=True)]
        unused = reduce(
            mul,
            (
                fingerprint(v, e, beta, v.SEP_MEM, int(v.GEN**index), v.ONE, library.images["memory"][int(v.GEN**index)])
                for index in range(UNUSED, UNUSED + 32)
            ),
            v.ONE,
        )
        push, pull, count = sparse_packet(v, library, positions, layout, bus, e, beta)
        cofactors.append([push[0] / (unused * a1 * c1), push[2] / ag, push[3] / cg, pull[0] / (unused * ag * cg), pull[2] / a1, pull[3] / c1])
        assert pull[0] == push[1] * push[0] * push[2] * push[3] / (pull[1] * pull[2] * pull[3])
        views.append(linear_view(v, library, positions, layout, bus, point, y, e, memory_indices))
        residuals.append((pull[1], final_evaluation(v, library, "code", code_indices, [*y, *point][:20])))
        code_images.append(library.images["code"])
        counts.append((count, dict(library.reads), dict(library.exponents)))
    assert all(cofactor == cofactors[0] for cofactor in cofactors)
    assert all(residual == residuals[0] for residual in residuals)
    assert all(image == code_images[0] for image in code_images) and all(value == counts[0] for value in counts)
    for indices in ((0, 1, 2, 3), (0, 4, 5, 6)):
        assert all(v.E.sum(views[index][column] for index in indices) == v.ZERO for column in range(11))
    assert all(view[i] + view[i + 4] == views[0][i] + views[0][i + 4] for view in views for i in range(4))
    print(
        "Actual sparse traces verify all six product incidences, shared-root reconstruction, seven-field linear views and unchanged bytecode residuals",
        flush=True,
    )
    print("All 28 count blocks fit whole first-packet children; their public normalization is assumed, not constructed by this audit", flush=True)


def occupancy_residual(v):
    switch = FunctionType(
        switch_library.__code__,
        {
            **switch_library.__globals__,
            "CODE_BASE": CODE_BASE,
            "MEMORY_PC": MEMORY_PC,
            "CODE_FRAMES": 1 << 18,
            "MEMORY_FRAMES": (1 << 18) + (1 << 15),
        },
    )
    rng = Random(166)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta, point = v.eq_kernel([sample() for _ in range(4)]), sample(), [sample() for _ in range(20)]
    support = (0, 1, 64, 129)
    for kind in ("code", "memory"):
        before, indices = switch(v, kind, support, [0] * len(support))

        def code_root(library):
            return reduce(
                mul,
                (
                    fingerprint(v, e, beta, v.SEP_BYTECODE, address, v.GEN ** library.reads["code", address], payload)
                    for address, payload in library.images["code"].items()
                ),
                v.ONE,
            )

        baseline = code_root(before), final_evaluation(v, before, "code", indices["code"], point)
        ratios, linear = [], []
        for s in support:
            if kind == "code":
                seeds = [
                    fingerprint(
                        v,
                        e,
                        beta,
                        v.SEP_BYTECODE,
                        int(v.GEN ** (CODE_BASE + 2 * s + bit)),
                        v.ONE,
                        before.images["code"][int(v.GEN ** (CODE_BASE + 2 * s + bit))],
                    )
                    for bit in (0, 1)
                ]
                delta = e[2] * (v.ONE + v.GEN**2)
                ratios.append(seeds[0] * (seeds[1] + delta) / ((seeds[0] + delta) * seeds[1]))
                linear.append((v.ONE + v.GEN**2) * weight(v, point[1:], (CODE_BASE >> 1) + s))
            else:
                ratios.append(v.ONE)
                linear.append(v.ZERO)
        for bits in product((0, 1), repeat=len(support)):
            after, after_indices = switch(v, kind, support, bits)
            assert before.images == after.images and indices == after_indices
            expected_product = baseline[0] * reduce(mul, (ratio for ratio, bit in zip(ratios, bits, strict=True) if bit), v.ONE)
            expected_linear = baseline[1] + v.E.sum(coefficient for coefficient, bit in zip(linear, bits, strict=True) if bit)
            assert code_root(after) == expected_product
            assert final_evaluation(v, after, "code", indices["code"], point) == expected_linear
        if kind == "code":
            assert all(ratio != v.ONE for ratio in ratios) and all(coefficient != v.ZERO for coefficient in linear)
    print(
        "Valid occupancy libraries: bytecode residual is a product and linear sum of the same bits; memory occupancy leaves both components fixed",
        flush=True,
    )


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    _, boundary = error_bound()
    mix_four = Fraction(1 << 1055) * Fraction(1 << 98, base**2 - 4) ** NOISE
    mix_one = Fraction(1 << 767) * Fraction(1 << 96, base**2 - 1) ** 32
    four = Fraction((1 << 23) + 8 * NOISE + 8, size) + Fraction(base**2, (size - 2) ** 2) + mix_four
    one = Fraction((1 << 23) + 40, size) + Fraction(base**2, (size - 2) ** 2) + mix_one
    assert mix_four < Fraction(1, 1 << 384)
    assert four + one + boundary < Fraction(1, 1 << 155)
    print(
        "Exact bound below 2^-155 for the first-packet/boundary leakage reduction; the actual joint bytecode residual law remains unproved",
        flush=True,
    )


if __name__ == "__main__":
    incidence_certificate()
    verifier = verifier_module()
    actual_incidence(verifier)
    occupancy_residual(verifier)
    concrete_bound()
