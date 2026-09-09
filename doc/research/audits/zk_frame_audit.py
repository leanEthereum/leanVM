"""Joint-view counterexample and frame-changing padding certificates."""

from collections import Counter
from fractions import Fraction
from random import Random

from zk_jump_audit import complete_bank_layout, einv
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis


def jump_row(verifier, pc, frame, offsets, destination, destination_frame):
    table = verifier.TABLES[verifier.OP_JUMP]
    row = [verifier.ZERO] * table.width
    values = {
        "pc": pc,
        "fp": frame,
        "o_c": verifier.GEN ** offsets[0],
        "o_d": verifier.GEN ** offsets[1],
        "o_f": verifier.GEN ** offsets[2],
        "v_cond": verifier.ONE,
        "v_pc": destination,
        "v_fp": destination_frame,
        "cnt_c": verifier.ONE,
        "cnt_d": verifier.ONE,
        "cnt_f": verifier.ONE,
        "cnt_bc": verifier.ONE,
        "w": verifier.ONE,
        "b": verifier.ONE,
    }
    for name, value in values.items():
        row[table.columns.index(name)] = value
    assert table.constraints(row) == (verifier.ZERO, verifier.ZERO)
    return row


def check_bus(verifier, rows, boundary=None):
    table = verifier.TABLES[verifier.OP_JUMP]
    pushes, pulls = [], []
    for row in rows:
        pushes += [tuple(form.evaluate(row.__getitem__) for form in block) for block in table.flushes.push]
        pulls += [tuple(form.evaluate(row.__getitem__) for form in block) for block in table.flushes.pull]
    if boundary is not None:
        start, end = boundary
        pushes.append((verifier.SEP_STATE, start, verifier.ONE))
        pulls.append((verifier.SEP_STATE, end, verifier.ONE))
    memories, bytecodes = {}, {}
    for entry in pulls:
        if entry[0] not in (verifier.SEP_MEM, verifier.SEP_BYTECODE):
            continue
        image = memories if entry[0] == verifier.SEP_MEM else bytecodes
        address = int(entry[1])
        assert address not in image and entry[2] == verifier.ONE
        image[address] = entry
    for image in (memories, bytecodes):
        for entry in image.values():
            pushes.append(entry)
            pulls.append((*entry[:2], verifier.GEN, *entry[3:]))
    encode = lambda entries: Counter(tuple(map(int, entry)) for entry in entries)
    assert encode(pushes) == encode(pulls)
    return memories, bytecodes


def constant_frame_leak(verifier):
    field, rng = Tower(64, verifier), Random(101)
    point = [verifier.E(*field.coords(field.random(rng))) for _ in range(20)]
    transcripts = []
    for frame in (verifier.ONE, verifier.GEN**10):
        rows = [
            jump_row(verifier, verifier.ONE, verifier.ONE, (2, 3, 4), verifier.GEN, frame),
            jump_row(verifier, verifier.GEN, frame, (5, 6, 7), verifier.GEN**63, verifier.ONE),
        ]
        _, code = check_bus(verifier, rows, (verifier.ONE, verifier.GEN**63))
        table = verifier.TABLES[verifier.OP_JUMP]
        fp, vfp = (table.columns.index(name) for name in ("fp", "v_fp"))
        weights = [verifier.eq_eval(point, [verifier.E(index >> bit & 1) for bit in range(20)]) for index in (20, 21)]
        difference = verifier.E.sum(weight * (row[fp] + row[vfp]) for weight, row in zip(weights, rows))
        transcripts.append((difference, code))
    assert transcripts[0][0] == verifier.ZERO and transcripts[1][0] != verifier.ZERO
    assert transcripts[0][1] == transcripts[1][1]
    print(
        "Constant-frame leak: two executions with the same bytecode and boundaries differ in the exposed fp+v_fp evaluation; both buses balance",
        flush=True,
    )


def frame_cycle(verifier):
    table = verifier.TABLES[verifier.OP_JUMP]
    first, second = verifier.GEN**20, verifier.GEN**21
    frame_a, frame_b = verifier.GEN**100, verifier.GEN**106
    cases = []
    for destination in (frame_a, frame_b):
        rows = [
            jump_row(verifier, first, frame_a, (0, 1, 2), second, destination),
            jump_row(verifier, second, destination, (3, 4, 5), first, frame_a),
        ]
        check_bus(verifier, rows)
        cases.append(rows)
    fp, vfp = (table.columns.index(name) for name in ("fp", "v_fp"))
    for index in range(table.width):
        if index not in (fp, vfp):
            assert all(cases[0][row][index] == cases[1][row][index] for row in (0, 1))
    difference = frame_a + frame_b
    assert cases[0][0][vfp] + cases[1][0][vfp] == difference
    assert cases[0][1][fp] + cases[1][1][fp] == difference
    print(
        "Frame-changing gadget: both two-row cycles balance; only fp and v_fp columns change, while c, b, w and all four read counts stay fixed",
        flush=True,
    )


def weighted_span(verifier):
    field, rng = Tower(64, verifier), Random(102)
    point = [field.random(rng) for _ in range(20)]
    sparse = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    high, selectors = field.eq(point[8:]), field.eq(point[1:8])
    multipliers = [int(verifier.GEN ** (12 * (1 << bit))) for bit in range(12)]
    transformed, common = [], 1
    for value, multiplier in zip(point[8:], multipliers):
        denominator = 1 ^ value ^ field.mul(multiplier, value)
        common = field.mul(common, denominator)
        transformed.append(field.mul(field.mul(multiplier, value), einv(field, denominator)))
    transformed_weights = field.eq(transformed)
    weights = []
    for index in sparse:
        scalar = 1
        for bit, multiplier in enumerate(multipliers):
            if index >> bit & 1:
                scalar = field.kmul(scalar, multiplier)
        weight = field.mul(scalar, high[index])
        assert weight == field.mul(common, transformed_weights[index])
        weights.append(weight)
    assert len(binary_basis(weights)) == 192
    directions = []
    for family, tag in enumerate((14, 18)):
        base = 1000000 + 50000 * family
        delta = int(verifier.GEN**base * (verifier.ONE + verifier.GEN**6))
        for weight in weights:
            value = field.mul(field.mul(delta, selectors[tag >> 1]), weight)
            fp = field.mul(point[0] if family == 0 else 1 ^ point[0], value)
            vfp = field.mul(1 ^ point[0] if family == 0 else point[0], value)
            directions.append(fp | (vfp << 192))
    assert len(binary_basis(directions)) == 384
    banks, _, _ = complete_bank_layout(field, 12, 8)
    assert not {14, 15, 18, 19}.intersection(banks)
    assert not {14, 15, 18, 19}.intersection((6, 7, 10, 11, 12))
    print("Frame evaluation bank: exact Mobius identity and binary rank 384 for the joint (fp, v_fp) map over the actual fields", flush=True)


def error_bounds():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    frame = span + Fraction(50, size)
    joint = 2 * span + Fraction(323, size)
    root = Fraction((1 << 40) + 16, size) + Fraction(1 << 128, (size - 2) ** 2) + Fraction(1 << 95) * Fraction(1 << 96, (1 << 128) - 1) ** 8
    assert frame < Fraction(1, 1 << 157)
    assert joint < Fraction(1, 1 << 156)
    assert joint + root < Fraction(1, 1 << 150)
    print("Exact bounds: frame pair below 2^-157; with isolated JUMP below 2^-156; with shared root below 2^-150", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    constant_frame_leak(verifier)
    frame_cycle(verifier)
    weighted_span(verifier)
    error_bounds()
