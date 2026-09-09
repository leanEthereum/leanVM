"""A refined folded-row interface for a jointly hidden three-round GKR tail."""

from fractions import Fraction
from itertools import islice
from random import Random

from zk_audit_field import accelerate
from zk_bus_packet_audit import weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE
from zk_pcs_audit import verifier_module
from zk_penultimate_slopes_audit import CENTERS, determinant, geometric_span, placements
from zk_terminal_boundary_audit import CODE_FRAMES, MEMORY_PCS, geometry


def native_relation(v, layout, bus):
    count_places = v.bus_layout((), layout.count).tables
    for name in ("cnt_a", "cnt_b"):
        column = v.ARITH_COLUMNS.index(name)
        counter = next(
            place
            for block, place in zip(layout.count, count_places, strict=True)
            if block.owner == v.OP_MUL and block.coordinates[0].terms == {(column,): v.ONE}
        )
        index = next(
            i
            for i, block in enumerate(layout.pull)
            if block.owner == v.OP_MUL
            and block.coordinates[0].terms.get((), v.ZERO) == v.SEP_MEM
            and block.coordinates[2].terms == {(column,): v.ONE}
        )
        assert bus.tables[index].index == counter.index + (5 << 19)
        assert bus.tables[index].variables == counter.variables == 18
        for slot, (push, pull) in enumerate(zip(layout.push[index].coordinates, layout.pull[index].coordinates, strict=True)):
            difference = {monomial: coefficient for monomial, coefficient in (push + pull).terms.items() if coefficient}
            assert difference == ({(column,): v.ONE + v.GEN} if slot == 2 else {})
    assert all(
        place.index + (1 << place.variables) <= 3 << 19
        for block, place in zip(layout.count, count_places, strict=True)
        if block.owner in (v.OP_MUL, v.OP_JUMP)
    )
    print("Actual symbolic flushes and placements prove P_5+Q_5=e_2(1+g)C_0; count sector 3 is untouched by MUL/JUMP swaps", flush=True)


def banks(v):
    result = []
    profiles = (
        (v.OP_MUL, ("cnt_a", "cnt_c", "cnt_bc", 0, 1, 2, 3)),
        (v.OP_JUMP, ("cnt_c", "cnt_f", 0)),
    )
    for opcode, kinds in profiles:
        for kind_index, kind in enumerate(kinds):
            for partner in (1, 2, 3):
                ordinal = 3 * kind_index + partner - 1
                band, center = (2 + ordinal // 8, CENTERS[ordinal % 8]) if opcode == v.OP_MUL else (1 + 2 * (ordinal // 7), CENTERS[1 + ordinal % 7])
                result.append((opcode, kind, partner, band, center << 6))
    return result


def library_of(v, bank, bank_id, support):
    opcode, kind, partner, band, shift = bank
    counter = isinstance(kind, str)
    library, positions, quartets, templates = Library(v), {}, [], []
    for child in range(1 if counter else 4):
        pc, frame = 206000 + 16 * bank_id + 2 * child, 910000 + 128 * bank_id + 8 * child
        block = library.templates((opcode, pc, [], opcode == v.OP_MUL), v.GEN**frame)
        if opcode == v.OP_MUL:
            a, b = (child, 1) if kind == 1 else (1, child) if kind == 2 else (7, 1)
            block[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(a)
            block[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.E(b)
            for name, offset in zip(("o_c", "o_d", "o_f"), (3, 4, 5), strict=True):
                block[1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        templates.append(block)
    for ordinal, index in enumerate(support):
        rows = []
        for child in range(4):
            row = library.append(templates[0 if counter else child])[0]
            rows.append(row)
            positions[row] = 4 * ((band << 12) + (index ^ shift)) + child
        if counter:
            for col in v.TABLES[opcode].count_columns:
                selected = 2 if v.TABLES[opcode].columns[col] == kind else 1
                labels = [None] * 4
                labels[0], labels[partner] = 0, selected
                other = iter(label for label in range(4) if label not in (0, selected))
                labels = [next(other) if label is None else label for label in labels]
                library.set_labels([(row, col) for row in rows], [4 * ordinal + label for label in labels])
        quartets.append(rows)
    library.verify()
    return library, positions, quartets


def column(v, bank, library, positions, rows, places, x, e, *, stripped):
    opcode, _, partner, _, _ = bank
    result = [v.ZERO] * 11  # Push/pull sectors 4..7 and count sectors 0..2.
    first, second = [library.rows[rows[j]][1] for j in (0, partner)]
    for side, blocks in enumerate(places):
        for block, place in blocks:
            if block.owner != opcode:
                continue
            values = [[form.evaluate(row.__getitem__) for form in block.coordinates] for row in (first, second)]
            leaves = [values[j][0] if side == 2 else v.dot(e[: len(values[j])], values[j]) for j in range(2)]
            index = place.index + positions[rows[0]]
            sector = index >> 19
            assert sector in (range(3) if side == 2 else range(4, 8))
            scalar = weight(v, x[12:17], (index >> 14) & 31) if stripped else weight(v, x[:17], (index >> 2) & ((1 << 17) - 1))
            result[4 * side + sector - (0 if side == 2 else 4)] += scalar * (leaves[0] + leaves[1])
    assert result[1] + result[5] == e[2] * (v.ONE + v.GEN) * result[8]
    return [*result[:5], *result[6:]]


def coarse_map(v, fine, challenge, factor):
    assert len(fine) == 10
    values = [*fine[:5], fine[1] + factor * fine[7], *fine[5:], v.ZERO]
    return [(v.ONE + challenge) * values[j] + challenge * values[j + 1] for j in range(0, 12, 2)]


def conditional_coordinates(v, fine, challenge, factor):
    return [*coarse_map(v, fine, challenge, factor), *[fine[j] + fine[j + 1] for j in (0, 2, 5, 7)]]


def reservation(v):
    occupied = {opcode: set() for opcode in (v.OP_MUL, v.OP_JUMP)}
    for opcode, _, _, band, shift in banks(v):
        rows = {4 * ((band << 12) + (index ^ shift)) + child for index in SPARSE for child in range(4)}
        assert occupied[opcode].isdisjoint(rows)
        occupied[opcode].update(rows)
    counter = {8 * ((bank << 12) + index) + low for bank in range(4) for index in SPARSE for low in range(8)}
    returns = set(range(1536, 1568))
    occupancy = set(islice((row for row in range(1 << 17) if row not in counter | returns), 10 * len(SPARSE)))
    previous = counter | returns | occupancy
    assert occupied[v.OP_JUMP].isdisjoint(previous)
    closing = set(islice((row for row in range(1 << 17) if row not in previous | occupied[v.OP_JUMP]), 21 * 4 * len(SPARSE)))
    assert len(closing) == len(occupied[v.OP_MUL]) == 37632 and len(occupied[v.OP_JUMP]) == 16128
    assert len(previous | occupied[v.OP_JUMP] | closing) == 72608
    assert max(occupied[v.OP_MUL]) < 1 << 18 and max(previous | occupied[v.OP_JUMP] | closing) < 1 << 17
    assert 910000 + 128 * len(banks(v)) < 1 << 20 and 206000 + 16 * len(banks(v)) < 1 << 20
    assert 910000 > CODE_FRAMES + (1 << 15) and 206000 > max(MEMORY_PCS)
    print("Replacement bank reservations: 37632 MUL rows and 53760 new JUMP rows; 72608 JUMP rows including terminal padding", flush=True)


def audit(v):
    layout, bus, _, _ = geometry(v)
    native_relation(v, layout, bus)
    places, rng = placements(v, layout, bus), Random(224)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    x, e = [sample() for _ in range(20)], v.eq_kernel([sample() for _ in range(4)])
    vectors = {partner: [] for partner in (1, 2, 3)}
    for bank_id, bank in enumerate(banks(v)):
        library, positions, quartets = library_of(v, bank, bank_id, SPARSE[:65])
        base = column(v, bank, library, positions, quartets[0], places, x, e, stripped=True)
        vectors[bank[2]].append(base)
        for ordinal in (0, 1, 63, 64):
            actual = column(v, bank, library, positions, quartets[ordinal], places, x, e, stripped=False)
            factor = weight(v, x[:12], SPARSE[ordinal] ^ bank[4]) * (v.GEN ** (4 * ordinal) if isinstance(bank[1], str) else v.ONE)
            assert actual == [factor * value for value in base]
    for partner, columns in vectors.items():
        value = determinant(v, columns)
        assert value
        print(f"Pair (0,{partner}): nonzero 10-by-10 determinant {int(value):048x}; degree at most 90", flush=True)
    units = [[v.E(int(i == j)) for i in range(10)] for j in range(10)]
    factor = e[2] * (v.ONE + v.GEN)
    transformed = [conditional_coordinates(v, unit, x[17], factor) for unit in units]
    assert determinant(v, transformed) == (v.ONE + x[17]) ** 2
    assert determinant(v, [conditional_coordinates(v, unit, v.ONE, factor) for unit in units]) == v.ZERO
    print(
        "Ten native coordinates split into six coarse values and four slopes; the omitted push/pull difference is tied to a count slice", flush=True
    )
    geometric_span(v, x)
    reservation(v)
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    fine = 30 * span + Fraction(30 * 36 + 3 * 90, size)
    terminal = 3 * span + Fraction(137, size) + Fraction(3, 1 << 256)
    bound = fine + terminal + Fraction(1 + 128 + 123, size)
    assert bound == 33 * span + Fraction(1739, size) + Fraction(3, 1 << 256)
    assert bound < Fraction(1, 1 << 152)
    print("Uniform three-round-tail and boundary error bound below 2^-152; no new randomness is assumed after conditioning", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    accelerate(verifier)
    audit(verifier)
