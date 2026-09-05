"""Exact algebraic certificates toward stacked-claim and VM padding, not a ZK VM."""

from fractions import Fraction
from random import Random
from types import SimpleNamespace

from zk_pcs_audit import (
    RightInverse,
    Tower,
    edot,
    kdot,
    reference_replay,
    verifier_module,
)


def binary_basis(values):
    pivots, basis = {}, []
    for value in values:
        reduced = value
        while reduced:
            bit = reduced.bit_length() - 1
            if bit in pivots:
                reduced ^= pivots[bit]
            else:
                pivots[bit] = reduced
                basis.append(value)
                break
    return basis


def span_error_bound():
    size = 1 << 192
    build = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    sixth_bad = Fraction(((1 << 32) - 1) ** 2, size - 1)
    bound = build + sixth_bad * Fraction(1, 1 << 32) + Fraction(1, 1 << 256)
    assert bound < Fraction(1, 1 << 158)
    assert bound + Fraction(64 * 16 + 28, size) < Fraction(1, 1 << 157)
    print("Sparse binary-span bound: exact rational arithmetic certifies error below 2^-158", flush=True)


def moore_certificate():
    for bits in (2, 4, 8):
        field = Tower(bits)
        values = [1 << i for i in range(3 * bits)]
        rows = []
        for _ in range(bits):
            rows += field.expand([values])
            values = [field.mul(value, value) for value in values]
        assert len(field.pivots(rows)) == 3 * bits
    print("Moore maps: base-field rank equals three times the number of Frobenius rows in all toy towers", flush=True)


def ring_bank_certificate(verifier):
    field, rng = Tower(64, verifier), Random(40)
    positions = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    assert len(positions) == len(set(positions)) == 448
    high = field.eq([field.random(rng) for _ in range(12)])
    beta = [high[i] for i in positions]
    basis = binary_basis(beta)
    assert len(basis) == 192
    low = field.eq([field.random(rng) for _ in range(2)])
    for points in ([0, 1, 7], [3, 9, 17], [0]):
        degree = len(points)
        rows = [field.novel(2, point) for point in points]
        inverse = RightInverse(field, [list(row[:degree]) for row in rows])
        z = inverse.solve([row[degree] for row in rows]) + [1] + [0] * (3 - degree)
        assert all(kdot(field, row, z) == 0 for row in rows)
        frobenius = low[:]
        for _ in range(64):
            assert edot(field, z, frobenius)
            frobenius = [field.mul(value, value) for value in frobenius]
    print("Actual-field ring bank: 448 weights contain a certified 192-element binary basis; all 64 query-kernel factors are nonzero", flush=True)


def stacked_basis(verifier, message):
    field, rng = Tower(64, verifier), Random(42)
    ext = lambda value: verifier.E(*field.coords(value))
    point = tuple(ext(field.random(rng)) for _ in range(5))
    eq = verifier.eq_kernel(point)
    slices = tuple(verifier.E.sum(eq[u] for u in range(32) if (message[u] >> bit) & 1) for bit in range(64))
    challenges = tuple(ext(field.random(rng)) for _ in range(6))

    class RingCoins:
        def samples(self, count):
            assert count == len(challenges)
            return challenges

    target, ring_weight = verifier.ring_switch(point, slices, RingCoins())
    assert target == verifier.E.sum(verifier.E(message[u]) * verifier._phi(eq[u], challenges) for u in range(32))
    ring_placement = verifier.Placement(5, 0)
    placements = (verifier.Placement(4, 32), verifier.Placement(3, 48, 1))
    layout = SimpleNamespace(placements=placements, stack_log=6)
    claims = [(lambda x: ring_placement.eq_above(x) * ring_weight(x[:5]), target)]
    for index, placement in enumerate(placements):
        local_point = tuple(ext(field.random(rng)) for _ in range(placement.variables))
        vector = [verifier.E(message[placement.index + (u << placement.low)]) for u in range(1 << placement.variables)]
        value = verifier.multilinear_eval(vector, local_point)
        claims.append(verifier.ColumnClaim(index, local_point, value).on_stack(layout))
    scales = verifier.powers(ext(field.random(rng)), len(claims))

    def basis(x):
        return verifier.dot(scales, [weight(x) for weight, _ in claims])

    boolean = lambda i: [verifier.E((i >> j) & 1) for j in range(6)]
    assert verifier.dot(scales, [value for _, value in claims]) == verifier.E.sum(basis(boolean(i)) * verifier.E(message[i]) for i in range(64))
    print("Stacked weight: actual ring_switch, aligned placement, interleaved ColumnClaim, and batching agree with their claimed values", flush=True)
    return basis


def selector_obstruction(verifier):
    field, rng = Tower(64, verifier), Random(43)
    placement = verifier.Placement(3, 184)
    point = tuple(verifier.E(*field.coords(field.random(rng))) for _ in range(3))
    layout = SimpleNamespace(placements=(placement,), stack_log=9)
    weight, _ = verifier.ColumnClaim(0, point, verifier.ZERO).on_stack(layout)
    padding = [i for i in range(512) if i // 32 < 5 or i % 32 < 20]
    support = [placement.index + i for i in range(8)]
    boolean = lambda i: [verifier.E((i >> j) & 1) for j in range(9)]
    assert all(weight(boolean(i)) == verifier.ZERO for i in padding)
    assert any(weight(boolean(i)) != verifier.ZERO for i in support)
    print("Selector obstruction: a valid placement weight vanishes on the one-point padding layout but not on its real block", flush=True)


def memory_geometry(verifier):
    layout = verifier.build_layout([verifier.K(0)] * 16, 18, (3, 3, 3, 3, 3, 3))
    placement = layout.placements[verifier.MEMORY_0]
    height = 1 << (layout.stack_log - verifier.INITIAL_FOLDING_FACTOR)
    assert placement.low == 0 and placement.index % (8 * height) == 0
    assert (1 << placement.variables) >= 8 * height
    first = placement.index // height
    lanes = [(first + 7) ^ j for j in range(5)]
    intervals = [(lane * height - placement.index, (lane + 1) * height - placement.index) for lane in lanes]
    assert all(2 <= lo < hi <= 1 << layout.log_memory for lo, hi in intervals)
    print(f"Memory-bank geometry only: stack log={layout.stack_log}, five lane ranges={intervals}; these cells must be reserved unused", flush=True)


def jump_freedoms(verifier):
    field, rng = Tower(64, verifier), Random(44)
    table = verifier.TABLES[verifier.OP_JUMP]
    inverse = table.columns.index("w")
    condition = table.columns.index("v_cond")
    flag = table.columns.index("b")
    forms = [form for side in (table.flushes.push, table.flushes.pull) for block in side for form in block]
    assert all(inverse not in monomial for form in forms for monomial in form.terms)
    for _ in range(20):
        columns = [verifier.E(rng.getrandbits(64)) for _ in table.columns]
        columns[condition] = columns[flag] = verifier.ZERO
        assert table.constraints(columns) == (verifier.ZERO, verifier.ZERO)
        before = [form.evaluate(columns.__getitem__) for form in forms]
        columns[inverse] = verifier.E(rng.getrandbits(64))
        assert table.constraints(columns) == (verifier.ZERO, verifier.ZERO)
        assert before == [form.evaluate(columns.__getitem__) for form in forms]
    for bit in (0, 1):
        columns = [verifier.ZERO] * table.width
        columns[table.columns.index("pc")] = verifier.GEN**12
        columns[table.columns.index("fp")] = verifier.GEN**20
        columns[table.columns.index("v_pc")] = verifier.GEN**13
        columns[table.columns.index("v_fp")] = verifier.GEN**20
        columns[condition] = columns[flag] = verifier.E(bit)
        columns[inverse] = verifier.ONE
        assert table.constraints(columns) == (verifier.ZERO, verifier.ZERO)
        state = tuple(form.evaluate(columns.__getitem__) for form in table.flushes.push[0])
        assert state == (verifier.SEP_STATE, verifier.GEN**13, verifier.GEN**20)
    field_point = [field.random(rng) for _ in range(12)]
    weights = field.eq(field_point)
    indices = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    assert len(binary_basis([weights[i] for i in indices])) == 192
    print(
        "JUMP freedoms: zero-branch inverse is bus-invisible; a random Boolean condition can have a fixed successor; flag-evaluation weights span E",
        flush=True,
    )


def jump_terminal_certificate(verifier):
    field, rng = Tower(64, verifier), Random(45)
    table = verifier.TABLES[verifier.OP_JUMP]
    point = [field.random(rng) for _ in range(14)]
    low, high = field.eq(point[:12]), field.eq(point[12:])
    positions = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    directions = []
    for group, condition in enumerate((verifier.ONE, verifier.GEN)):
        for bit in (0, 1):
            columns = [verifier.ZERO] * table.width
            columns[table.columns.index("v_cond")] = condition * verifier.E(bit)
            columns[table.columns.index("b")] = verifier.E(bit)
            columns[table.columns.index("w")] = condition.inv()
            assert table.constraints(columns) == (verifier.ZERO, verifier.ZERO)
        for index in positions:
            weight = field.mul(high[group], low[index])
            directions.append(field.mul(int(condition), weight) | (weight << 192))
    for index in range(5):
        weight = field.mul(high[2], low[index])
        directions += [field.mul(1 << bit, weight) << 384 for bit in range(64)]
    assert len(directions) == 2 * 448 + 5 * 64
    assert len(binary_basis(directions)) == 3 * 192
    print(
        "Valid JUMP terminal map: two Boolean cycle families plus five free inverses have full binary rank 576 for (condition, flag, inverse)",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    span_error_bound()
    moore_certificate()
    ring_bank_certificate(verifier)
    reference_replay(verifier, stacked_basis)
    selector_obstruction(verifier)
    memory_geometry(verifier)
    jump_freedoms(verifier)
    jump_terminal_certificate(verifier)
