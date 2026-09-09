"""Six-table conditional reconstruction with real layouts and unequal heights."""

from functools import reduce
from operator import mul
from random import Random

from zk_jump_bus_audit import cycle_rows
from zk_metadata_audit import COUNTS, SPARSE
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis


def forms_at(verifier, heights, sample):
    layout = verifier.build_layout([verifier.K(0)] * (16 << 8), 16, heights)
    blocks = (layout.push, layout.pull, layout.count)
    layouts = [verifier.bus_layout((0, 16, 8) if side < 2 else (), items) for side, items in enumerate(blocks)]
    point = [sample() for _ in range(layouts[0].depth)]
    weights, beta = verifier.eq_kernel([sample() for _ in range(4)]), sample()
    forms = [[verifier.Form() for _ in range(3)] for _ in verifier.TABLES]
    for side, (items, placement) in enumerate(zip(blocks, layouts)):
        for block, selector in zip(items, placement.tables):
            weight = selector.eq_above(point)
            form = forms[block.owner][side]
            form.add_scaled(verifier._const(beta if side < 2 else verifier.ZERO), weight)
            for slot, coordinate in enumerate(block.coordinates):
                form.add_scaled(coordinate, weight * (weights[slot] if side < 2 else verifier.ONE))
    return forms, point


def interpolate_cubic(verifier, values):
    zero, one, at_gen, at_square = values
    first, second = verifier.GEN, verifier.GEN**2
    a1, a2 = first * (first + verifier.ONE), second * (second + verifier.ONE)
    b1, b2 = first * (first**2 + verifier.ONE), second * (second**2 + verifier.ONE)
    d1, d2 = at_gen + zero + first * (zero + one), at_square + zero + second * (zero + one)
    determinant = a1 * b2 + a2 * b1
    quadratic, cubic = (d1 * b2 + d2 * b1) / determinant, (a1 * d2 + a2 * d1) / determinant
    return zero, quadratic, cubic


def replay(verifier, heights, forms, powers, equality, challenges, batch, target, wire, terminals):
    class Stream:
        def __init__(self):
            self.values = iter([*(value for row in wire for value in row), *(value for row in terminals for value in row)])
            self.coins = iter(reversed(challenges))

        def next_scalar(self):
            return next(self.values)

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            return next(self.coins)

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    stream = Stream()
    claims = verifier.table_sumcheck(heights, forms, [verifier.ONE, batch], powers, equality, target, stream)
    assert len(claims) == sum(verifier.TABLE_WIDTHS)
    assert next(stream.values, None) is None and next(stream.coins, None) is None


def certificate(verifier, heights, seed):
    rng = Random(seed)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    product = lambda values: reduce(mul, values, verifier.ONE)
    size = max(heights)
    forms, equality = forms_at(verifier, heights, sample)
    equality = equality[:size]
    powers, challenges, batch = verifier.powers(sample(), 3), [sample() for _ in range(size)], sample()
    rows = [[[verifier.E(rng.getrandbits(64)) for _ in table.columns] for _ in range(1 << height)] for table, height in zip(verifier.TABLES, heights)]
    rows[verifier.OP_JUMP] = cycle_rows(verifier, rng, size)

    def polynomial(table, row):
        constraints = verifier.TABLES[table].constraints(row)
        return verifier.dot(powers, [form.evaluate(row.__getitem__) for form in forms[table]]) + verifier.dot(
            [verifier.ONE, batch][: len(constraints)], constraints
        )

    def columns_at(table, point):
        weights = verifier.eq_kernel(point)
        return [verifier.E.sum(weight * row[column] for weight, row in zip(weights, rows[table])) for column in range(verifier.TABLE_WIDTHS[table])]

    def full_at(point):
        return verifier.E.sum(
            product(point[height:]) * verifier.eq_eval(equality[:height], point[:height]) * polynomial(table, columns_at(table, point[:height]))
            for table, height in enumerate(heights)
        )

    targets = [
        verifier.E.sum(weight * polynomial(table, row) for weight, row in zip(verifier.eq_kernel(equality[:height]), rows[table]))
        for table, height in enumerate(heights)
    ]
    target, wire, free, records = verifier.E.sum(targets), [], [], []
    points = (verifier.ZERO, verifier.ONE, verifier.GEN, verifier.GEN**2)
    for coordinate in reversed(range(size)):
        factors = [
            product(
                challenges[index] if index >= height else verifier.ONE + equality[index] + challenges[index] for index in range(coordinate + 1, size)
            )
            for height in heights
        ]
        inactive = verifier.E.sum(factor * initial for height, factor, initial in zip(heights, factors, targets) if height <= coordinate)
        scale = factors[verifier.OP_JUMP]
        values = [
            verifier.E.sum(
                full_at([*(verifier.E(index >> bit & 1) for bit in range(coordinate)), t, *challenges[coordinate + 1 :]])
                for index in range(1 << coordinate)
            )
            for t in points
        ]
        message = interpolate_cubic(verifier, values)
        wire.append(message)
        r = equality[coordinate]
        cofactor_zero = values[0] / (scale * (verifier.ONE + r))
        cofactor_one = (values[1] + inactive) / (scale * r)
        cofactor_quadratic = message[2] / scale
        assert message[1] == scale * (cofactor_zero + cofactor_one + r * cofactor_quadratic)
        if coordinate == size - 1:
            first_one = cofactor_one
        else:
            free.append(cofactor_one)
        if coordinate:
            free.append(cofactor_quadratic)
        records.append((scale, inactive, factors))

    endpoints = [
        [columns_at(table, [verifier.E(branch), *challenges[1:height]]) for branch in (0, 1)] if height else [rows[table][0], rows[table][0]]
        for table, height in enumerate(heights)
    ]
    jump, columns = verifier.OP_JUMP, verifier.JUMP_COLUMNS
    c, w = (columns.index(name) for name in ("v_cond", "w"))
    endpoints[jump][0][w] = endpoints[jump][1][w] = verifier.ZERO
    c0, c1 = endpoints[jump][0][c], endpoints[jump][1][c]
    root = c0 / (c0 + c1)
    final_scale, _, final_factors = records[-1]
    at_root = verifier.E.sum(
        factor / final_scale * polynomial(table, [a + root * (a + b) for a, b in zip(*endpoint)])
        for table, (height, factor, endpoint) in enumerate(zip(heights, final_factors, endpoints))
        if height
    )

    def reconstruct(free):
        cursor, claim, recovered = 0, target, []
        for round_index, coordinate in enumerate(reversed(range(size))):
            scale, inactive, _ = records[round_index]
            r, coin = equality[coordinate], challenges[coordinate]
            cofactor_claim = (claim + inactive) / scale
            one = first_one if not round_index else free[cursor]
            cursor += int(round_index != 0)
            zero = (cofactor_claim + r * one) / (verifier.ONE + r)
            quadratic = free[cursor] if coordinate else (at_root + zero + (zero + one) * root) / (root * (verifier.ONE + root))
            cursor += int(coordinate != 0)
            linear = zero + one + quadratic
            message = (scale * (verifier.ONE + r) * zero, scale * (linear + (verifier.ONE + r) * quadratic), scale * quadratic)
            recovered.append(message)
            cofactor_value = zero + coin * (linear + coin * quadratic)
            claim = inactive * coin + scale * (verifier.ONE + r + coin) * cofactor_value
        assert cursor == len(free)
        terminal = [[a + challenges[0] * (a + b) for a, b in zip(*endpoint)] for endpoint in endpoints]
        remainder = verifier.E.sum(
            factor / final_scale * polynomial(table, row)
            for table, (height, factor, row) in enumerate(zip(heights, final_factors, terminal))
            if height
        )
        terminal[jump][w] = (cofactor_value + remainder) / terminal[jump][c]
        return terminal, recovered

    terminals, recovered = reconstruct(free)
    assert recovered == wire
    assert all(row == columns_at(table, challenges[:height]) for table, (height, row) in enumerate(zip(heights, terminals)))
    replay(verifier, heights, forms, powers, equality, challenges, batch, target, recovered, terminals)
    synthetic, synthetic_wire = reconstruct([sample() for _ in free])
    replay(verifier, heights, forms, powers, equality, challenges, batch, target, synthetic_wire, synthetic)
    print(
        f"All six tables, heights {heights}: direct interpolation equals conditional reconstruction; genuine and synthetic wires pass the unchanged table_sumcheck",
        flush=True,
    )


def count_slope_certificate(verifier):
    rng = Random(122)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    forms, equality = forms_at(verifier, (18, 20, 18, 18, 20, 17), sample)
    challenge, root, gamma = [sample() for _ in range(20)], sample(), sample()
    powers = verifier.powers(gamma, 3)
    local = forms[verifier.OP_JUMP]
    coefficients = []
    for name in COUNTS:
        column = verifier.JUMP_COLUMNS.index(name)
        assert all(len(term) == 1 for form in local for term in form.terms if column in term)
        assert local[2].terms[(column,)] != verifier.ZERO
        coefficients.append(verifier.dot(powers, [form.terms.get((column,), verifier.ZERO) for form in local]))
    assert coefficients[0] * (challenge[0] + root) != verifier.ZERO
    folded = verifier.eq_kernel(challenge[8:])
    initial = verifier.eq_kernel(equality[8:20])
    upper = verifier.eq_kernel(equality[8:19])
    fold_selector = verifier.eq_kernel(challenge[2:8])[148 >> 2]
    initial_selector = verifier.eq_kernel(equality[2:8])[148 >> 2]
    directions = []
    for branch in (0, 1):
        fold_branch = challenge[0] if branch else verifier.ONE + challenge[0]
        root_branch = root if branch else verifier.ONE + root
        initial_branch = equality[0] if branch else verifier.ONE + equality[0]
        for index in SPARSE:
            for column, coefficient in enumerate(coefficients):
                delta = (verifier.ONE + verifier.GEN) * (verifier.GEN ** (2 * index) if column == 3 else verifier.ONE)
                at_terminal = fold_selector * folded[index] * delta
                at_initial = initial_selector * initial_branch * delta * coefficient
                values = [verifier.ZERO] * 4
                values[column] = fold_branch * at_terminal
                values.extend(
                    (
                        coefficient * root_branch * at_terminal,
                        at_initial * initial[index],
                        at_initial * upper[index % 2048] if index & 2048 else verifier.ZERO,
                    )
                )
                directions.append(sum(int(value) << (192 * position) for position, value in enumerate(values)))
    ranks = [len(binary_basis([direction & ((1 << (192 * size)) - 1) for direction in directions])) for size in (4, 5, 6, 7)]
    assert ranks[:2] == [4 * 192, 5 * 192]
    print(
        f"Count-swap diagnostic: binary ranks for terminals, then last-root residual, initial target and first upper-half target are {ranks}",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    certificate(verifier, (2, 4, 0, 3, 4, 3), 120)
    certificate(verifier, (4, 1, 2, 0, 4, 4), 121)
    count_slope_certificate(verifier)
