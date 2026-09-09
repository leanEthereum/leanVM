"""Exact conditional reconstruction of the bus-batched JUMP sumcheck, not full ZK."""

from random import Random

from zk_frame_audit import check_bus, jump_row
from zk_jump_audit import inverse_message_map
from zk_pcs_audit import Tower, edot, verifier_module


def bus_form(verifier, sample):
    table, form = verifier.TABLES[verifier.OP_JUMP], verifier.Form()
    weights, beta = verifier.eq_kernel([sample() for _ in range(4)]), sample()
    for blocks in (table.flushes.push, table.flushes.pull):
        for block in blocks:
            selector = sample()
            form.add_scaled(verifier._const(beta), selector)
            for weight, coordinate in zip(weights, block):
                form.add_scaled(coordinate, selector * weight)
    for column in table.count_columns:
        form.add_scaled(verifier._col(column), sample())
    return form


def cycle_rows(verifier, rng, log_size=6):
    rows = []
    for index in range(1 << (log_size - 1)):
        pc, frame = verifier.GEN ** (64 + 2 * index), verifier.GEN ** (1000 + 8 * index)
        zero = jump_row(verifier, pc, frame, (0, 1, 2), pc * verifier.GEN, frame)
        for name, value in (("v_cond", verifier.ZERO), ("b", verifier.ZERO), ("w", verifier.E(rng.getrandbits(64)))):
            zero[verifier.JUMP_COLUMNS.index(name)] = value
        rows.extend((zero, jump_row(verifier, pc * verifier.GEN, frame, (3, 4, 5), pc, frame)))
    check_bus(verifier, rows)
    rng.shuffle(rows)
    return rows


def direct_view(verifier, rows, form, equality, challenges, batch):
    table = verifier.TABLES[verifier.OP_JUMP]

    def value(row):
        first, second = table.constraints(row)
        return first + batch * second + form.evaluate(row.__getitem__)

    target = verifier.E.sum(weight * value(row) for weight, row in zip(verifier.eq_kernel(equality), rows))
    work, factor, free, wire, endpoints = rows, verifier.ONE, [], [], None
    for coordinate in reversed(range(len(challenges))):
        half, weights = len(work) // 2, verifier.eq_kernel(equality[:coordinate])

        def at(t, weights=weights, work=work, half=half):
            return verifier.E.sum(
                weight * value([a + t * (a + b) for a, b in zip(low, high)]) for weight, low, high in zip(weights, work[:half], work[half:])
            )

        at_zero, at_one, at_gen = (at(t) for t in (verifier.ZERO, verifier.ONE, verifier.GEN))
        quadratic = (at_gen + at_zero + verifier.GEN * (at_zero + at_one)) / (verifier.GEN * (verifier.ONE + verifier.GEN))
        if not wire:
            first_one = at_one
        else:
            free.append(at_one)
        if coordinate:
            free.append(quadratic)
        else:
            endpoints = tuple(zip(*work))
        linear, r, coin = at_zero + at_one + quadratic, equality[coordinate], challenges[coordinate]
        wire.append((factor * (verifier.ONE + r) * at_zero, factor * (linear + (verifier.ONE + r) * quadratic), factor * quadratic))
        work = [[a + coin * (a + b) for a, b in zip(low, high)] for low, high in zip(work[:half], work[half:])]
        factor *= verifier.ONE + r + coin
    return target, first_one, free, endpoints, work[0], wire


def reconstruct(verifier, target, first_one, free, endpoints, form, equality, challenges, batch):
    columns = verifier.JUMP_COLUMNS
    condition, flag, inverse = (columns.index(name) for name in ("v_cond", "b", "w"))
    endpoints = list(endpoints)
    endpoints[inverse] = (verifier.ZERO, verifier.ZERO)
    c0, c1 = endpoints[condition]
    root = c0 / (c0 + c1)
    root_values = [low + root * (low + high) for low, high in endpoints]
    assert root_values[condition] == verifier.ZERO
    at_root = root_values[flag] + form.evaluate(root_values.__getitem__)
    cursor, claim, factor, wire = 0, target, verifier.ONE, []
    for round_index, coordinate in enumerate(reversed(range(len(challenges)))):
        at_one = first_one if not round_index else free[cursor]
        cursor += int(round_index != 0)
        r, coin = equality[coordinate], challenges[coordinate]
        at_zero = (claim + r * at_one) / (verifier.ONE + r)
        if coordinate:
            quadratic = free[cursor]
            cursor += 1
        else:
            quadratic = (at_root + at_zero + (at_zero + at_one) * root) / (root * (verifier.ONE + root))
        linear = at_zero + at_one + quadratic
        wire.append((factor * (verifier.ONE + r) * at_zero, factor * (linear + (verifier.ONE + r) * quadratic), factor * quadratic))
        claim = at_zero + coin * (linear + coin * quadratic)
        factor *= verifier.ONE + r + coin
    assert cursor == len(free)
    terminal = [low + challenges[0] * (low + high) for low, high in endpoints]
    terminal[inverse] = (claim + terminal[flag] + form.evaluate(terminal.__getitem__)) / terminal[condition] + batch * (terminal[flag] + verifier.ONE)
    return terminal, wire


def replay(verifier, target, terminal, wire, form, equality, challenges, batch):
    class Replay:
        def __init__(self):
            self.stream = iter([*(value for row in wire for value in row), *terminal])
            self.coins = iter(reversed(challenges))

        def next_scalar(self):
            return next(self.stream)

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            return next(self.coins)

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    tables = verifier.TABLES
    verifier.TABLES = (tables[verifier.OP_JUMP],)
    transcript = Replay()
    try:
        claims = verifier.table_sumcheck(
            [len(challenges)],
            [(form, verifier.Form(), verifier.Form())],
            [verifier.ONE, batch],
            [verifier.ONE, verifier.ZERO, verifier.ZERO],
            equality,
            target,
            transcript,
        )
    finally:
        verifier.TABLES = tables
    assert len(claims) == len(terminal) == 14
    assert next(transcript.stream, None) is None and next(transcript.coins, None) is None
    assert all(claim.value == value and claim.point == tuple(challenges) for claim, value in zip(claims, terminal))


if __name__ == "__main__":
    verifier, rng = verifier_module(), Random(110)
    field = Tower(64, verifier)
    sample = lambda: verifier.E(*field.coords(field.random(rng)))
    rows, form = cycle_rows(verifier, rng), bus_form(verifier, sample)
    equality, challenges, batch = [sample() for _ in range(6)], [sample() for _ in range(6)], sample()
    target, first_one, free, endpoints, terminal, wire = direct_view(verifier, rows, form, equality, challenges, batch)
    assert target != verifier.ZERO and first_one != verifier.ZERO
    recovered, reconstructed = reconstruct(verifier, target, first_one, free, endpoints, form, equality, challenges, batch)
    assert recovered == terminal and reconstructed == wire
    replay(verifier, target, recovered, reconstructed, form, equality, challenges, batch)
    synthetic, synthetic_wire = reconstruct(verifier, target, first_one, [sample() for _ in free], endpoints, form, equality, challenges, batch)
    replay(verifier, target, synthetic, synthetic_wire, form, equality, challenges, batch)
    print(
        "Bus-batched reconstruction: direct and reconstructed messages agree; genuine and synthetic wires pass the actual table_sumcheck with all fourteen terminals",
        flush=True,
    )

    condition_column, inverse_column = (verifier.JUMP_COLUMNS.index(name) for name in ("v_cond", "w"))
    padding = [index for index, row in enumerate(rows) if row[condition_column] == verifier.ZERO]
    delta = [rng.getrandbits(64) for _ in padding]
    changed = [row[:] for row in rows]
    for index, difference in zip(padding, delta):
        changed[index][inverse_column] += verifier.E(difference)
    assert all(form.evaluate(before.__getitem__) == form.evaluate(after.__getitem__) for before, after in zip(rows, changed))
    changed_target, changed_one, changed_free, _, _, _ = direct_view(verifier, changed, form, equality, challenges, batch)
    assert (target, first_one) == (changed_target, changed_one)
    matrix, _, _ = inverse_message_map(
        field, [int(row[condition_column]) for row in rows], padding, list(map(int, equality)), list(map(int, challenges))
    )
    assert [int(a + b) for a, b in zip(free, changed_free)] == [edot(field, row, delta) for row in matrix[:-1]]
    print(
        "Inverse-only differences: bus values, initial target and first cofactor endpoint stay fixed; the free-message map is exactly the earlier inverse matrix",
        flush=True,
    )
