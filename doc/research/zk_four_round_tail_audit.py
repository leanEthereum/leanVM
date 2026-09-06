"""A sixteen-coordinate native interface for extending the joint GKR tail."""

from fractions import Fraction
from itertools import islice
from random import Random
from types import SimpleNamespace

from zk_audit_field import accelerate
from zk_bus_packet_audit import weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE, polynomial_product
from zk_pcs_audit import verifier_module
from zk_penultimate_slopes_audit import CENTERS, determinant, placements
from zk_terminal_boundary_audit import CODE_FRAMES, MEMORY_PCS, geometry
from zk_three_round_tail_audit import column as coarser_column


def banks(v):
    result = []
    profiles = (
        (v.OP_MUL, ("cnt_a", "cnt_b", "cnt_c", "cnt_bc", 0, 1, 2, 3, 4, 5)),
        (v.OP_JUMP, ("cnt_c", "cnt_f", "cnt_bc", 0, 1, 2)),
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
        pc, frame = 207000 + 16 * bank_id + 2 * child, 920000 + 128 * bank_id + 16 * child
        block = library.templates((opcode, pc, [], opcode == v.OP_MUL), v.GEN**frame)
        if opcode == v.OP_MUL:
            a, b = (child, 1) if kind == 1 else (1, child) if kind == 2 else (child, child) if kind == 4 else (7, 1)
            block[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(a)
            block[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.E(b)
            if kind == 5:
                block[0][1][v.ARITH_COLUMNS.index("o_a")] = v.GEN ** (6 + child)
            for name, offset in zip(("o_c", "o_d", "o_f"), (3, 4, 5), strict=True):
                block[1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        elif kind == 2:
            block[0][1][v.JUMP_COLUMNS.index("v_cond")] = v.E(child + 1)
            block[0][1][v.JUMP_COLUMNS.index("w")] = v.ONE / v.E(child + 1)
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
                remaining = iter(label for label in range(4) if label not in (0, selected))
                labels = [next(remaining) if label is None else label for label in labels]
                library.set_labels([(row, col) for row in rows], [4 * ordinal + label for label in labels])
        quartets.append(rows)
    library.verify()
    return library, positions, quartets


def native_relations(v, layout, bus):
    places = placements(v, layout, bus)
    expected = {v.OP_MUL: ((9, 3), (10, 0), (11, 1), (12, 2)), v.OP_JUMP: ((13, 5), (14, 4), (14, 4), (15, 5))}
    for opcode, sectors in expected.items():
        reads = [(i, block, place) for i, (block, place) in enumerate(places[1]) if block.owner == opcode][1:]
        for (index, block, place), (bus_sector, count_sector) in zip(reads, sectors, strict=True):
            ((column,),) = block.coordinates[2].terms
            count_place = next(p for b, p in places[2] if b.owner == opcode and b.coordinates[0].terms == {(column,): v.ONE})
            assert place.index >> 18 == bus_sector and count_place.index >> 18 == count_sector
            assert place.variables == count_place.variables and place.index % (1 << 18) == count_place.index % (1 << 18)
            for slot, (push, pull) in enumerate(zip(layout.push[index].coordinates, block.coordinates, strict=True)):
                terms = {monomial: value for monomial, value in (push + pull).terms.items() if value}
                assert terms == ({(column,): v.ONE + v.GEN} if slot == 2 else {})
    state = next(i for i, block in enumerate(layout.push) if block.owner == v.OP_JUMP)
    names = v.JUMP_COLUMNS
    replace = {names.index("v_pc"): names.index("pc"), names.index("v_fp"): names.index("fp")}
    for push, pull in zip(layout.push[state].coordinates, layout.pull[state].coordinates, strict=True):
        terms = {}
        for monomial, value in (push + pull).terms.items():
            monomial = tuple(sorted(replace.get(i, i) for i in monomial if i != names.index("b")))
            terms[monomial] = terms.get(monomial, v.ZERO) + value
        assert not any(terms.values())
    assert all(place.index + (1 << place.variables) <= 6 << 18 for block, place in places[2] if block.owner in expected)
    print("Symbolic read differences prove five universal relations; self-loop state cancellation supplies the sixth invariant", flush=True)


def expand(v, fine, factor, invariant=None):
    assert len(fine) == 16
    push, (q8, q13), count = fine[:8], fine[8:10], fine[10:]
    pull = [q8, push[1] + factor * count[3], push[2] + factor * count[0], push[3] + factor * count[1]]
    pull.extend((push[4] + factor * count[2], q13, push[6] + factor * count[4], push[7] + factor * count[5] + push[5] + q13))
    if invariant is not None:
        pull[7] += invariant
    return push, pull, count


def column(v, bank, library, positions, rows, places, x, e, *, stripped):
    opcode, _, partner, _, _ = bank
    result = [[v.ZERO] * length for length in (8, 8, 6)]
    first, second = [library.rows[rows[j]][1] for j in (0, partner)]
    for side, blocks in enumerate(places):
        for block, place in blocks:
            if block.owner != opcode:
                continue
            values = [[form.evaluate(row.__getitem__) for form in block.coordinates] for row in (first, second)]
            leaves = [values[j][0] if side == 2 else v.dot(e[: len(values[j])], values[j]) for j in range(2)]
            index = place.index + positions[rows[0]]
            sector = (index >> 18) - (0 if side == 2 else 8)
            assert 0 <= sector < len(result[side])
            scalar = weight(v, x[12:16], (index >> 14) & 15) if stripped else weight(v, x[:16], (index >> 2) & ((1 << 16) - 1))
            result[side][sector] += scalar * (leaves[0] + leaves[1])
    push, pull, count = result
    fine = [*push, pull[0], pull[5], *count]
    assert result == list(expand(v, fine, e[2] * (v.ONE + v.GEN)))
    return fine


def coarse_map(v, fine, challenge, factor):
    push, pull, count = expand(v, fine, factor)
    fold = lambda values: [(v.ONE + challenge) * values[j] + challenge * values[j + 1] for j in range(0, len(values), 2)]
    p, q, c = fold(push), fold(pull), fold(count)
    assert q[1] == p[1] + factor * c[0]
    return [*p, q[0], q[2], q[3], *c]


def conditional_coordinates(v, fine, challenge, factor):
    push, _, count = expand(v, fine, factor)
    slopes = [push[j] + push[j + 1] for j in range(0, 8, 2)] + [count[0] + count[1], count[4] + count[5]]
    return [*coarse_map(v, fine, challenge, factor), *slopes]


def slope_shifts(v, coarse, challenge, factor, invariant, h0, h2):
    p4, _p5, p6, p7, q4, q6, q7, _c0, c1, c2 = coarse
    h1 = (challenge * invariant + p6 + q6 + p7 + q7 + factor * ((v.ONE + challenge) * c1 + c2)) / (factor * challenge * (v.ONE + challenge))
    shifts = (
        factor * h1 + (p4 + q4 + factor * c1) / (v.ONE + challenge),
        factor * h0,
        factor * h1 + (p6 + q6 + factor * c1) / challenge,
        factor * h2 + (p7 + q7 + factor * c2) / challenge,
    )
    return h1, shifts


def four_round_reader(v):
    rng = Random(229)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    challenges, equalities = [sample() for _ in range(4)], [sample() for _ in range(4)]
    combiner, factor = sample(), sample()
    work = [[[sample() for _ in range(16)] for _ in range(4)] for _ in range(3)]
    for child in range(4):
        fine, invariant = [sample() for _ in range(16)], sample()
        push, pull, count = expand(v, fine, factor, invariant)
        work[0][child][8:], work[1][child][8:], work[2][child][:6] = push, pull, count
        work[2][child][8:] = [v.ONE] * 8
        t = challenges[0]
        fold = lambda values, t=t: [values[j] + t * (values[j] + values[j + 1]) for j in range(0, len(values), 2)]
        p, q, c = fold(push), fold(pull), fold(count)
        assert q[1] == p[1] + factor * c[0]
        coarse = [*p, q[0], q[2], q[3], *c]
        h1, shifts = slope_shifts(v, coarse, t, factor, invariant, count[0] + count[1], count[4] + count[5])
        assert h1 == count[2] + count[3]
        assert shifts == tuple(push[2 * i] + push[2 * i + 1] + pull[2 * i] + pull[2 * i + 1] for i in range(4))
    wire, messages = [], []
    for coordinate, challenge in enumerate(challenges):
        message = [v.ZERO] * 5
        weights = v.eq_kernel(equalities[coordinate + 1 :])
        for side, children in enumerate(work):
            for row, scalar in enumerate(weights):
                lines = [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in children]
                for degree, value in enumerate(polynomial_product(v, lines)):
                    message[degree] += combiner**side * scalar * value
        if messages:
            assert v.poly_eval(messages[-1], challenges[coordinate - 1]) == message[0] + equalities[coordinate] * v.E.sum(message[1:])
        messages.append(message)
        wire.extend(message[1:])
        work = [
            [[child[2 * row] + challenge * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in side]
            for side in work
        ]
    incoming = messages[0][0] + equalities[0] * v.E.sum(messages[0][1:])
    stream, coins = iter(wire), iter(challenges)
    transcript = SimpleNamespace(next_scalars=lambda n: [next(stream) for _ in range(n)], sample=lambda: next(coins))
    transcript.sumcheck_round_poly = lambda n, claim, eq: v.Transcript.sumcheck_round_poly(transcript, n, claim, eq)
    point, claim = v.sumcheck(transcript, incoming, 5, equalities)
    assert point == tuple(challenges) and next(stream, None) is None and next(coins, None) is None
    assert claim == v.E.sum(combiner**side * rows[0][0] * rows[1][0] * rows[2][0] * rows[3][0] for side, rows in enumerate(work))
    print("Arbitrary invariant offsets give the stated four slope shifts; the actual four-round reader accepts all linking claims", flush=True)


def reservation(v):
    occupied = {opcode: set() for opcode in (v.OP_MUL, v.OP_JUMP)}
    for opcode, _, _, band, shift in banks(v):
        rows = {4 * ((band << 12) + (index ^ shift)) + child for index in SPARSE for child in range(4)}
        assert occupied[opcode].isdisjoint(rows)
        occupied[opcode].update(rows)
    counter = {8 * ((bank << 12) + index) + low for bank in range(4) for index in SPARSE for low in range(8)}
    returns = set(range(1536, 1568))
    fixed = counter | returns
    occupancy = set(islice((row for row in range(1 << 17) if row not in fixed), 10 * len(SPARSE)))
    previous = fixed | occupancy
    assert occupied[v.OP_JUMP].isdisjoint(previous)
    blocked = previous | occupied[v.OP_JUMP]
    closing = set(islice((row for row in range(1 << 17) if row not in blocked), len(occupied[v.OP_MUL])))
    assert len(closing) == len(occupied[v.OP_MUL]) == 53760 and len(occupied[v.OP_JUMP]) == 32256
    assert len(previous | occupied[v.OP_JUMP] | closing) == 104864
    assert max(occupied[v.OP_MUL]) < 1 << 18 and max(previous | occupied[v.OP_JUMP] | closing) < 1 << 17
    assert 920000 > CODE_FRAMES + (1 << 15) and 207000 > max(MEMORY_PCS)
    assert 920000 + 128 * len(banks(v)) < 1 << 20 and 207000 + 16 * len(banks(v)) < 1 << 20
    print("Forty-eight replacement banks fit: 53760 MUL rows, 86016 new JUMP rows, 104864 total JUMP rows", flush=True)


def certificates(v, *, full):
    layout, bus, _, _ = geometry(v)
    native_relations(v, layout, bus)
    places, rng = placements(v, layout, bus), Random(228)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    x, e = [sample() for _ in range(20)], v.eq_kernel([sample() for _ in range(4)])
    vectors = {partner: [] for partner in (1, 2, 3)}
    for bank_id, bank in enumerate(banks(v)):
        library, positions, quartets = library_of(v, bank, bank_id, SPARSE[:65] if full else SPARSE[:1])
        base = column(v, bank, library, positions, quartets[0], places, x, e, stripped=True)
        vectors[bank[2]].append(base)
        for ordinal in (0, 1, 63, 64) if full else ():
            actual = column(v, bank, library, positions, quartets[ordinal], places, x, e, stripped=False)
            factor = weight(v, x[:12], SPARSE[ordinal] ^ bank[4]) * (v.GEN ** (4 * ordinal) if isinstance(bank[1], str) else v.ONE)
            assert actual == [factor * value for value in base]
            coarse = coarser_column(v, bank, library, positions, quartets[ordinal], places, x, e, stripped=False)
            assert coarse_map(v, actual, x[16], e[2] * (v.ONE + v.GEN)) == coarse
    for partner, columns in vectors.items():
        value = determinant(v, columns)
        print(f"Pair (0,{partner}): 16-by-16 determinant {int(value):048x}", flush=True)
        assert value
    factor = e[2] * (v.ONE + v.GEN)
    units = [[v.E(int(i == j)) for i in range(16)] for j in range(16)]
    value = determinant(v, [conditional_coordinates(v, unit, x[16], factor) for unit in units])
    assert value == factor * x[16] ** 2 * (v.ONE + x[16]) ** 2
    for t, delta in ((v.ZERO, factor), (v.ONE, factor), (x[16], v.ZERO)):
        assert determinant(v, [conditional_coordinates(v, unit, t, delta) for unit in units]) == v.ZERO
    print("Conditional-coordinate determinant is Delta*t^2*(1+t)^2; six independent slopes remain per child", flush=True)


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    fine = 48 * span + Fraction(48 * 36 + 3 * 128, size)
    terminal = 3 * span + Fraction(137, size) + Fraction(3, 1 << 256)
    smoothing = Fraction(6 + 30 + 1 + 128 + 123, size) + Fraction(648, size**2)
    bound = fine + terminal + smoothing
    assert bound == 51 * span + Fraction(2537, size) + Fraction(648, size**2) + Fraction(3, 1 << 256)
    assert bound < Fraction(1, 1 << 152)
    print("Uniform four-round tail and boundary bound below 2^-152; one fine-cut failure event is charged", flush=True)


def audit(v):
    certificates(v, full=True)
    four_round_reader(v)
    reservation(v)
    error_bound()


if __name__ == "__main__":
    verifier = verifier_module()
    accelerate(verifier)
    audit(verifier)
