"""Uniform sparse row-swap sources for the penultimate quartic's slope quotient."""

from fractions import Fraction
from itertools import islice
from random import Random

from zk_audit_field import accelerate
from zk_bus_packet_audit import weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis
from zk_terminal_boundary_audit import CODE_FRAMES, MEMORY_PCS, geometry

CENTERS = (0, 7, 25, 30, 42, 45, 51, 52)


def banks(v):
    result = []
    for opcode in (v.OP_MUL, v.OP_JUMP):
        for kind in range(3):
            for partner in (1, 2, 3):
                ordinal = 3 * kind + partner - 1
                band, center = (2 + ordinal // 8, CENTERS[ordinal % 8]) if opcode == v.OP_MUL else (1 + 2 * (ordinal // 7), CENTERS[1 + ordinal % 7])
                result.append((opcode, kind, partner, band, center << 6))
    return result


def library_of(v, bank, bank_id, support):
    opcode, kind, partner, band, shift = bank
    library, positions, quartets = Library(v), {}, []
    templates = []
    for child in range(4 if kind == 2 else 1):
        pc, frame = 205000 + 16 * bank_id + 2 * child, 900000 + 128 * bank_id + 8 * child
        block = library.templates((opcode, pc, [], opcode == v.OP_MUL), v.GEN**frame)
        if opcode == v.OP_MUL:
            block[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(child if kind == 2 else 7)
            block[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.ONE
            for name, offset in zip(("o_c", "o_d", "o_f"), (3, 4, 5), strict=True):
                block[1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        templates.append(block)
    for ordinal, index in enumerate(support):
        rows = []
        for child in range(4):
            appended = library.append(templates[child if kind == 2 else 0])
            rows.append(appended[0])
            positions[appended[0]] = 4 * ((band << 12) + (index ^ shift)) + child
        if kind < 2:
            special = "cnt_a" if opcode == v.OP_MUL else "cnt_f"
            for col in v.TABLES[opcode].count_columns:
                selected = 2 if kind == 1 and v.TABLES[opcode].columns[col] == special else 1
                labels = [None] * 4
                labels[0], labels[partner] = 0, selected
                remaining = iter(label for label in range(4) if label not in (0, selected))
                labels = [next(remaining) if label is None else label for label in labels]
                library.set_labels([(row, col) for row in rows], [4 * ordinal + label for label in labels])
        quartets.append(rows)
    library.verify()
    return library, positions, quartets


def placements(v, layout, bus):
    return (
        tuple(zip(layout.push, bus.tables, strict=True)),
        tuple(zip(layout.pull, bus.tables, strict=True)),
        tuple(zip(layout.count, v.bus_layout((), layout.count).tables, strict=True)),
    )


def column(v, bank, library, positions, rows, places, x, e, *, stripped):
    opcode, _, partner, _, _ = bank
    result = [v.ZERO] * 6
    first, second = [library.rows[rows[j]][1] for j in (0, partner)]
    for side, blocks in enumerate(places):
        for block, place in blocks:
            if block.owner != opcode:
                continue
            values = [[form.evaluate(row.__getitem__) for form in block.coordinates] for row in (first, second)]
            leaves = [values[j][0] if side == 2 else v.dot(e[: len(values[j])], values[j]) for j in range(2)]
            index = place.index + positions[rows[0]]
            quarter = index >> 20
            assert quarter in ((0, 1) if side == 2 else (2, 3))
            scalar = weight(v, x[12:18], (index >> 14) & 63) if stripped else weight(v, x[:18], (index >> 2) & ((1 << 18) - 1))
            delta = scalar * (leaves[0] + leaves[1])
            result[side] += delta * (x[18] if quarter % 2 else v.ONE + x[18])
            result[3 + side] += delta
    return result


def determinant(v, columns):
    matrix, result = [list(row) for row in zip(*columns, strict=True)], v.ONE
    for col in range(len(matrix)):
        pivot = next((row for row in range(col, len(matrix)) if matrix[row][col]), None)
        if pivot is None:
            return v.ZERO
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        scalar = matrix[col][col]
        result *= scalar
        matrix[col] = [value / scalar for value in matrix[col]]
        for row in range(col + 1, len(matrix)):
            scale = matrix[row][col]
            matrix[row] = [a + scale * b for a, b in zip(matrix[row], matrix[col], strict=True)]
    return result


def geometric_span(v, x):
    scalars = [v.GEN ** (4 * ((1 << i) if i < 6 else 64 * (i - 5))) for i in range(12)]
    for ordinal, index in enumerate(SPARSE):
        factor = v.ONE
        for bit, scalar in enumerate(scalars):
            if index >> bit & 1:
                factor *= scalar
        assert factor == v.GEN ** (4 * ordinal)
    for shift in (center << 6 for center in CENTERS):
        reflected = [coin + v.E(shift >> bit & 1) for bit, coin in enumerate(x[:12])]
        denominators = [v.ONE + coin + scalar * coin for coin, scalar in zip(reflected, scalars, strict=True)]
        assert all(denominators)
        transformed = [scalar * coin / denominator for coin, scalar, denominator in zip(reflected, scalars, denominators, strict=True)]
        common = v.ONE
        for denominator in denominators:
            common *= denominator
        for ordinal, index in enumerate(SPARSE):
            assert weight(v, x[:12], index ^ shift) * v.GEN ** (4 * ordinal) == common * weight(v, transformed, index)
        for kind in (0, 2):
            values = [
                int(weight(v, x[:12], index ^ shift) * (v.GEN ** (4 * ordinal) if kind == 0 else v.ONE)) for ordinal, index in enumerate(SPARSE)
            ]
            assert len(binary_basis(values)) == 192
    print("All sparse ordinal weights factor geometrically; reflected/Mobius span identities and exact binary ranks pass", flush=True)


def reservation(v):
    assert all((a ^ b).bit_count() >= 3 for i, a in enumerate(CENTERS) for b in CENTERS[i + 1 :])
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
    closing = set(islice((row for row in range(1 << 17) if row not in previous | occupied[v.OP_JUMP]), 9 * 4 * len(SPARSE)))
    assert len(closing) == 16128 and len(occupied[v.OP_MUL]) == len(occupied[v.OP_JUMP]) == 16128
    assert len(previous | occupied[v.OP_JUMP] | closing) == 51104
    assert max(occupied[v.OP_MUL]) < 1 << 18 and max(previous | occupied[v.OP_JUMP] | closing) < 1 << 17
    assert 900000 + 128 * 18 < 1 << 20 and 205000 + 16 * 18 < 1 << 20
    assert 900000 > CODE_FRAMES + (1 << 15) and 205000 > max(MEMORY_PCS)
    print(
        "Eighteen sparse banks fit disjointly: 16128 MUL rows, 32256 new JUMP rows; 51104 JUMP rows including the terminal-boundary construction",
        flush=True,
    )


def audit(v):
    layout, bus, _, _ = geometry(v)
    places, rng = placements(v, layout, bus), Random(222)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    x, e = [sample() for _ in range(20)], v.eq_kernel([sample() for _ in range(4)])
    vectors = {partner: [] for partner in (1, 2, 3)}
    for bank_id, bank in enumerate(banks(v)):
        library, positions, quartets = library_of(v, bank, bank_id, SPARSE[:65])
        base = column(v, bank, library, positions, quartets[0], places, x, e, stripped=True)
        vectors[bank[2]].append(base)
        for ordinal in (0, 1, 63, 64):
            actual = column(v, bank, library, positions, quartets[ordinal], places, x, e, stripped=False)
            factor = weight(v, x[:12], SPARSE[ordinal] ^ bank[4]) * (v.GEN ** (4 * ordinal) if bank[1] < 2 else v.ONE)
            assert actual == [factor * value for value in base]
    for partner, columns in vectors.items():
        value = determinant(v, columns)
        assert value
        print(f"Pair (0,{partner}): exact nonzero 6-by-6 determinant {int(value):048x}; polynomial degree at most 66", flush=True)
    geometric_span(v, x)
    reservation(v)
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    rank_error = 18 * span + Fraction(18 * 36 + 3 * 66, size)
    terminal = 3 * span + Fraction(137, size) + Fraction(3, 1 << 256)
    assert rank_error == 18 * span + Fraction(846, size)
    assert rank_error + terminal + Fraction(123, size) == 21 * span + Fraction(1106, size) + Fraction(3, 1 << 256)
    assert rank_error + terminal + Fraction(123, size) < Fraction(1, 1 << 153)
    print("Uniform rank bound below 2^-153; two-round tail and boundary composition also fits below 2^-153", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    accelerate(verifier)
    audit(verifier)
