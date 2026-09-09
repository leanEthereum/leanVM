"""Triangular valid counter banks for the bus-batched JUMP view, excluding GKR."""

from fractions import Fraction
from random import Random

from zk_frame_audit import jump_row
from zk_jump_audit import complete_bank_layout
from zk_jump_bus_audit import reconstruct, replay
from zk_metadata_audit import COUNTS, SPARSE, check_bus, padding
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis
from zk_table_batch_audit import forms_at
from zk_two_point_audit import SPARSE_TWO, error_bounds


def counter_rows(verifier):
    rows, memories, code, masks = {}, {}, {}, []
    columns, g = verifier.JUMP_COLUMNS, verifier.GEN

    def pair(pc, frame, position, count):
        first = jump_row(verifier, pc, frame, (0, 1, 2), pc, frame)
        second = first[:]
        for name in COUNTS[:3]:
            second[columns.index(name)] = g
        first[columns.index("cnt_bc")] = count
        second[columns.index("cnt_bc")] = g * count
        assert position not in rows and position + 2 not in rows
        rows[position], rows[position + 2] = first, second
        for offset, value in enumerate((verifier.ONE, pc, frame)):
            address = int(frame * g**offset)
            assert address not in memories
            memories[address] = (int(value), 0, 0), g**2
        code[int(pc)] = (int(g**verifier.OP_JUMP), 1, int(g), int(g**2), 0, 0), count * g**2

    for branch in (0, 1):
        pc, frame, count = g ** (1024 + branch), g ** (10000000 + 1000000 * branch), verifier.ONE
        for index in range(1 << 14):
            position = 160 + 4 * (index >> 11) + branch + 256 * (index % 2048)
            pair(pc, frame, position, count)
            if index in SPARSE_TWO:
                masks.extend((position, position + 2, column) for column in range(4))
            frame *= g**32
            count *= g**2
    pc, count = g**1026, verifier.ONE
    for index in SPARSE:
        position = 192 + 4 * (index >> 11) + 256 * (index % 2048) + (1 << 19)
        pair(pc, g ** (13000000 + 32 * index), position, count)
        masks.append((position, position + 2, 0))
        count *= g**2
    assert len(rows) == 66432 and len(masks) == 5056
    return rows, memories, code, masks


def layout_certificate(verifier):
    rows, memories, code, masks = counter_rows(verifier)
    rng, program_swaps = Random(124), []
    for branch in (0, 1):
        extra, pairs, extra_memory, extra_code = padding(verifier, branch, include_counts=False)
        for target, source in ((rows, extra), (memories, extra_memory), (code, extra_code)):
            assert not target.keys() & source.keys()
            target.update(source)
        program_swaps.extend((left, right) for bank in pairs for _, left, right in bank)
    field = Tower(64, verifier)
    planes, _, _ = complete_bank_layout(field, 12, 8)
    reserved = {tag + 256 * index for tag in (6, 7, 10, 11) for index in SPARSE} | {12 + 256 * index for index in range(1792)}
    assert not any(index % 256 in planes or index in reserved for index in rows)
    assert len(rows) == 88832 and len(rows) + 294400 == 383232
    check_bus(verifier, rows, memories, code)
    randomized = {index: row[:] for index, row in rows.items()}
    for left, right in program_swaps:
        if rng.getrandbits(1):
            randomized[left], randomized[right] = randomized[right], randomized[left]
    for left, right, column in masks:
        if rng.getrandbits(1):
            local = verifier.JUMP_COLUMNS.index(COUNTS[column])
            randomized[left][local], randomized[right][local] = randomized[right][local], randomized[left][local]
    check_bus(verifier, randomized, memories, code)
    print(
        "88832 new rows: original and randomized libraries balance the actual bus against identical memory and final counters; total reserved rows 383232",
        flush=True,
    )
    return rows, masks


def observation_certificate(verifier, rows, masks):
    rng = Random(125)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    forms, equality = forms_at(verifier, (18, 20, 18, 18, 20, 17), sample)
    challenge, gamma, eta = [sample() for _ in range(20)], sample(), sample()
    powers = verifier.powers(gamma, 3)
    form = verifier.Form()
    for weight, source in zip(powers, forms[verifier.OP_JUMP]):
        form.add_scaled(source, weight)
    columns = verifier.JUMP_COLUMNS
    coefficients = [form.terms[(columns.index(name),)] for name in COUNTS]
    assert coefficients[0] != verifier.ZERO
    c_pair, b_pair = [sample() for _ in range(2)], [sample() for _ in range(2)]
    root = c_pair[0] / (c_pair[0] + c_pair[1])
    assert root not in (verifier.ZERO, verifier.ONE, challenge[0])
    main_coords, upper_coords = [*range(8, 19), 2, 3, 4], [*range(8, 19), 2]
    fold_main = verifier.eq_kernel([challenge[i] for i in main_coords])
    initial_main = verifier.eq_kernel([equality[i] for i in main_coords])
    fold_upper = verifier.eq_kernel([challenge[i] for i in upper_coords])
    initial_upper = verifier.eq_kernel([equality[i] for i in upper_coords])
    fold_selector = verifier.eq_kernel(challenge[5:8])[5] * (verifier.ONE + challenge[19])
    initial_selector = verifier.eq_kernel(equality[5:8])[5] * (verifier.ONE + equality[19])
    fold_upper_selector = verifier.eq_kernel(challenge[3:8])[24] * challenge[19]
    initial_upper_selector = verifier.eq_kernel(equality[3:8])[24]
    directions, lower_directions = [], []
    for left, right, column in masks:
        local = columns.index(COUNTS[column])
        delta, branch = rows[left][local] + rows[right][local], left % 2
        if left < 1 << 19:
            index = (left >> 8) + (((left % 256) - 160 - branch) >> 2) * 2048
            fold = fold_selector * fold_main[index]
            initial = initial_selector * initial_main[index]
            upper = verifier.ZERO
        else:
            index = ((left - (1 << 19)) >> 8) + (((left % 256) - 192) >> 2) * 2048
            fold = fold_upper_selector * fold_upper[index]
            upper = initial_upper_selector * initial_upper[index]
            initial = equality[19] * upper
        fold_branch = challenge[0] if branch else verifier.ONE + challenge[0]
        root_branch = root if branch else verifier.ONE + root
        initial_branch = equality[0] if branch else verifier.ONE + equality[0]
        values = [verifier.ZERO] * 4
        values[column] = delta * fold_branch * fold
        values.extend(
            (
                coefficients[column] * delta * root_branch * fold,
                coefficients[column] * delta * initial_branch * initial,
                coefficients[column] * delta * initial_branch * upper,
            )
        )
        direction = sum(int(value) << (192 * position) for position, value in enumerate(values))
        directions.append(direction)
        if left < 1 << 19:
            assert values[-1] == verifier.ZERO
            lower_directions.append(direction)
        if left % 2048 < 200:
            bits = lambda index: [verifier.E(index >> bit & 1) for bit in range(20)]
            assert fold_branch * fold == verifier.eq_eval(challenge, bits(left)) + verifier.eq_eval(challenge, bits(right))
            assert initial_branch * initial == verifier.eq_eval(equality[:20], bits(left)) + verifier.eq_eval(equality[:20], bits(right))
    assert len(binary_basis(lower_directions)) == 6 * 192
    assert len(binary_basis(directions)) == 7 * 192
    print("Counter observations: lower banks have rank 1152 and leave the first cofactor fixed; the upper bank raises joint rank to 1344", flush=True)

    endpoints = [(sample(),) * 2 for _ in columns]
    endpoints[columns.index("v_cond")], endpoints[columns.index("b")] = c_pair, b_pair
    endpoints[columns.index("w")] = (verifier.ZERO, verifier.ZERO)
    at_root = [a + root * (a + b) for a, b in endpoints]
    wanted = sample()
    slope = (wanted + at_root[columns.index("b")] + form.evaluate(at_root.__getitem__)) / (coefficients[0] * (root + challenge[0]))
    count = columns.index(COUNTS[0])
    constant = endpoints[count][0]
    endpoints[count] = constant + challenge[0] * slope, constant + (verifier.ONE + challenge[0]) * slope
    target, first_one = sample(), sample()
    terminal, wire = reconstruct(verifier, target, first_one, [sample() for _ in range(38)], endpoints, form, equality[:20], challenge, eta)
    replay(verifier, target, terminal, wire, form, equality[:20], challenge, eta)
    print(
        "Restricted simulator: independently sampled target, first cofactor, residual and metadata reconstruct twenty rounds accepted by the actual JUMP table-sumcheck arm",
        flush=True,
    )


def statistical_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    _, unweighted, weighted = error_bounds()
    bound = 4 * span + unweighted + weighted + Fraction(381, size)
    assert bound < Fraction(1, 1 << 146)
    print(
        "Exact bound: bus-batched JUMP view, including its target and all fourteen terminals, below 2^-146; preceding GKR and openings excluded",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    rows, masks = layout_certificate(verifier)
    observation_certificate(verifier, rows, masks)
    statistical_bound()
