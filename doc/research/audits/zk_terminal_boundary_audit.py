"""Joint terminal-quartic/boundary masks, excluding the preceding GKR wire."""

from fractions import Fraction
from functools import reduce
from itertools import islice, pairwise
from operator import mul
from random import Random
from types import SimpleNamespace

from zk_audit_field import accelerate
from zk_bus_boundary_audit import final_evaluation, packed
from zk_bus_packet_audit import counter_columns, table_packets, weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE, polynomial_product
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

UNUSED, XOR_PC, XOR_FRAMES = 524288, 32776, 131072
MEMORY_FRAMES = tuple((20 + bank) << 15 for bank in range(4))
MEMORY_PCS = tuple(204800 + bank for bank in range(4))
CODE_BASE, CODE_FRAMES = 196608, 851968


def geometry(v):
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus, counts = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22 and counts.depth < bus.depth
    assert [(p.index, p.variables) for p in bus.framework[1:]] == [(0, 20), (1 << 20, 20)]
    assert all(p.index >= 1 << 21 for p in bus.tables)
    assert all(p.index + (1 << p.variables) <= 1 << 21 for p in counts.tables)
    counter, reader = {}, {}
    for block, place in zip(layout.count, counts.tables, strict=True):
        ((column,),) = block.coordinates[0].terms
        counter[block.owner, column] = place
    for block, place in zip(layout.pull, bus.tables, strict=True):
        if block.coordinates[0].terms[()] != v.SEP_STATE:
            ((column,),) = block.coordinates[2].terms
            reader[block.owner, column] = place
    return layout, bus, counter, reader


def word_columns(v, data, x, y, e):
    layout, _, _, reader = data
    z, tau = [*y, *x], x[18]
    memory, xor, units = [], [], []
    for row in range(32):
        child, address = row % 4, UNUSED + row
        for limb in range(3):
            unit = [v.ZERO] * 10  # T[4], m[3], f_push[:3]
            unit[4 + limb] = weight(v, z[:20], address)
            if child < 3:
                unit[7 + child] = (v.ONE + tau) * e[3 + limb] * weight(v, x[:18], address >> 2)
            memory.extend(packed([value * v.E(1 << bit) for value in unit]) for bit in range(64))
    placements = [reader[v.OP_XOR, v.ARITH_COLUMNS.index(name)] for name in ("cnt_a", "cnt_c")]
    for row in range(32):
        unit = [v.ZERO] * 10
        for place in placements:
            index = place.index + row
            unit[index % 4] += e[3] * weight(v, x, index >> 2)
        for address in (XOR_FRAMES + 128 * row, XOR_FRAMES + 128 * row + 2):
            unit[4] += weight(v, z[:20], address)
            if address % 4 < 3:
                unit[7 + address % 4] += (v.ONE + tau) * e[3] * weight(v, x[:18], address >> 2)
        coefficient = e[3] * sum((place.eq_above([v.ZERO, v.ZERO, *x]) for place in placements), v.ZERO)
        expected = coefficient * weight(v, x[: layout.table_log_heights[v.OP_XOR] - 2], row >> 2)
        assert unit[row % 4] == expected and all(unit[j] == v.ZERO for j in range(4) if j != row % 4)
        units.append(unit)
        xor.extend(packed([value * v.E(1 << bit) for value in unit]) for bit in range(64))
    assert len(binary_basis(memory)) == 6 * 192
    assert len(binary_basis(column & ((1 << 768) - 1) for column in xor)) == 4 * 192
    assert len(binary_basis(memory + xor)) == 10 * 192
    print("Word map: unused limbs rank 1152, XOR table quotient rank 768, joint ten-field rank 1920", flush=True)
    return units


def xor_cycles(v, data, x, y, e, units):
    layout, bus, _, _ = data
    rng, views, libraries = Random(216), [], []
    payloads = [rng.getrandbits(64) for _ in range(32)]
    for words in ([0] * 32, payloads):
        library, positions = Library(v), {}
        library.pc, library.frame = XOR_PC, XOR_FRAMES
        block = library.block(v.OP_XOR)
        for row, value in enumerate(words):
            templates = library.templates(block, library.fresh_frame())
            templates[0][1][v.ARITH_COLUMNS.index("va_0")] = v.E(value)
            xor, jump = library.append(templates)
            positions[xor], positions[jump] = row, 1536 + row
        library.verify()
        push, pull = table_packets(v, library, positions, bus, layout, x, e)
        memory, endpoint = [v.ZERO] * 3, [v.ZERO] * 4
        for row, value in enumerate(words):
            for address in (XOR_FRAMES + 128 * row, XOR_FRAMES + 128 * row + 2):
                memory[0] += v.E(value) * weight(v, [*y, *x][:20], address)
                endpoint[address % 4] += v.E(value) * e[3] * (v.ONE + x[18]) * weight(v, x[:18], address >> 2)
        packet = [a + (v.ONE + x[-1]) * b for a, b in zip(push, endpoint, strict=True)]
        table_only = [a + (v.ONE + x[-1]) * b for a, b in zip(packet, endpoint, strict=True)]
        views.append((table_only + memory + endpoint[:3], [a + b for a, b in zip(push, pull, strict=True)]))
        libraries.append(library)
    assert libraries[0].images["code"] == libraries[1].images["code"]
    assert dict(libraries[0].reads) == dict(libraries[1].reads)
    assert dict(libraries[0].exponents) == dict(libraries[1].exponents)
    assert views[0][1] == views[1][1]
    observed = [a + b for a, b in zip(views[0][0], views[1][0], strict=True)]
    assert observed == [v.E.sum(unit[j] * v.E(value) for unit, value in zip(units, payloads, strict=True)) for j in range(10)]
    print("Thirty-two valid XOR/JUMP cycles match the ten-coordinate map; code, read counts and bus differences stay fixed", flush=True)


def occupancy(v, bank, support, bits):
    library, indices = Library(v), {"memory": set(), "code": set()}
    offsets = tuple(j for j in range(4) if j != bank) if bank < 4 else (0, 1, 2)
    base = MEMORY_FRAMES[bank] if bank < 4 else CODE_FRAMES
    for index, bit in zip(support, bits, strict=True):
        alternatives = []
        for alternative in (0, 1):
            frame = base + 8 * index + 4 * alternative
            pc = MEMORY_PCS[bank] if bank < 4 else CODE_BASE + 2 * index + alternative
            row = library.row(v.OP_JUMP, pc, v.GEN**frame, pc)
            for name, offset in zip(("o_c", "o_d", "o_f"), offsets, strict=True):
                row[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
            template = [(v.OP_JUMP, row)]
            library.register(template)
            alternatives.append(template)
            indices["memory"].update(frame + offset for offset in offsets)
            indices["code"].add(pc)
        library.append(alternatives[bit])
        library.append(alternatives[bit])
    library.verify()
    return library, indices


def final_slices(v, library, kind, indices, x):
    return [
        v.ONE
        + v.E.sum(
            (v.ONE + v.GEN ** library.reads[kind, int(v.GEN**index)]) * weight(v, x[:18], index >> 2) for index in indices if index % 4 == child
        )
        for child in range(4)
    ]


def occupancy_column(v, bank, index, x):
    factor = v.ONE + v.GEN**2
    if bank < 4:
        scalar = factor * weight(v, x[1:18], (MEMORY_FRAMES[bank] >> 3) + index)
        return [scalar if child != bank else v.ZERO for child in range(4)], [v.ZERO] * 4
    scalar = factor * weight(v, x[1:18], (CODE_FRAMES >> 3) + index)
    memory, code = [scalar, scalar, scalar, v.ZERO], [v.ZERO] * 4
    for bit in (0, 1):
        pc = CODE_BASE + 2 * index + bit
        code[pc % 4] += factor * weight(v, x[:18], pc >> 2)
    return memory, code


def metadata(v, slices, x, y, e):
    memory, code = slices
    weights, tau = v.eq_kernel(y), x[18]
    difference = [e[2] * ((v.ONE + tau) * a + tau * b) for a, b in zip(memory, code, strict=True)]
    return difference[:3] + [v.dot(weights, memory), v.dot(weights, code)]


def occupancy_certificate(v, x, y, e):
    columns = [[packed(metadata(v, occupancy_column(v, bank, index, x), x, y, e)) for index in SPARSE] for bank in range(5)]
    memory_columns = [column for bank in columns[:4] for column in bank]
    assert len(binary_basis(memory_columns)) == 4 * 192
    assert len(binary_basis(column >> (4 * 192) for column in columns[4])) == 192
    assert len(binary_basis(memory_columns + columns[4])) == 5 * 192
    for bank in range(5):
        support = (0, 1, 64, 129)
        before, indices = occupancy(v, bank, support, [0] * len(support))
        baseline = [final_slices(v, before, kind, indices[kind], x) for kind in ("memory", "code")]
        for bits in ((1, 0, 0, 0), (0, 1, 0, 1), (1, 1, 1, 1)):
            after, other = occupancy(v, bank, support, bits)
            assert before.images == after.images and indices == other
            assert dict(before.exponents) == dict(after.exponents)
            assert len(before.rows) == len(after.rows) == 2 * len(support)
            for (_, old), (_, new) in zip(before.rows, after.rows, strict=True):
                assert all(old[col] == new[col] for col in v.TABLES[v.OP_JUMP].count_columns)
            observed = []
            for side, kind in enumerate(("memory", "code")):
                current = final_slices(v, after, kind, indices[kind], x)
                assert v.dot(v.eq_kernel(y), current) == final_evaluation(v, after, kind, indices[kind], [*y, *x][:20])
                observed.append([a + b for a, b in zip(current, baseline[side], strict=True)])
            expected = [
                [v.E.sum(occupancy_column(v, bank, index, x)[side][j] for index, bit in zip(support, bits, strict=True) if bit) for j in range(4)]
                for side in range(2)
            ]
            assert observed == expected
    print("Four memory occupancy banks span all four slices; the code quotient adds one field, total metadata rank 960", flush=True)
    print("All five valid-cycle banks match simultaneous switch formulas and preserve both installed images and every table count leaf", flush=True)


def tail_reader(v, x, y, e):
    rng = Random(217)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    count, difference, push = [[sample() for _ in range(4)] for _ in range(3)]
    memory, memory_final, code_final = [sample() for _ in range(3)], sample(), sample()
    fixed_push, fixed_difference = [sample() for _ in range(3)], [sample() for _ in range(3)]
    beta, code_payload, combiner, equality = sample(), sample(), sample(), sample()
    weights, tau, challenge = v.eq_kernel(y), x[18], x[-1]
    address = v.index_mle([*y, *x][:20])
    totals = []
    for fm, fb in ((v.ONE, v.ONE), (memory_final, code_final)):
        left = beta + v.dot(e[:6], [v.SEP_MEM, address, fm, *memory])
        right = beta + e[0] * v.SEP_BYTECODE + e[1] * address + e[2] * fb + code_payload
        totals.append((v.ONE + tau) * left + tau * right)
    fixed_pull = [a + b for a, b in zip(fixed_push, fixed_difference, strict=True)]
    for endpoint, total in zip((fixed_push, fixed_pull), totals, strict=True):
        endpoint.append((total + v.dot(weights[:3], endpoint)) / weights[3])
        assert v.dot(weights, endpoint) == total
    pull = [a + b for a, b in zip(push, difference, strict=True)]
    lines = [
        [(f, (u + f) / challenge) for u, f in zip(packet, endpoint, strict=True)]
        for packet, endpoint in zip((push, pull), (fixed_push, fixed_pull), strict=True)
    ]
    lines.append([((u + challenge) / (v.ONE + challenge), (v.ONE + u) / (v.ONE + challenge)) for u in count])
    quartic = [v.ZERO] * 5
    for side, values in enumerate(lines):
        for degree, coefficient in enumerate(polynomial_product(v, values)):
            quartic[degree] += combiner**side * coefficient
    incoming = quartic[0] + equality * v.E.sum(quartic[1:])
    stream_values = iter(quartic[1:])
    stream = SimpleNamespace(next_scalars=lambda n: [next(stream_values) for _ in range(n)], sample=lambda: challenge)
    stream.sumcheck_round_poly = lambda n, claim, eq: v.Transcript.sumcheck_round_poly(stream, n, claim, eq)
    point, claim = v.sumcheck(stream, incoming, 5, [equality])
    assert point == (challenge,) and next(stream_values, None) is None
    assert claim == v.E.sum(combiner**side * reduce(mul, packet) for side, packet in enumerate((push, pull, count)))
    assert quartic[0] + combiner**2 * polynomial_product(v, lines[2])[0] == reduce(mul, fixed_push) + combiner * reduce(mul, fixed_pull)
    print(
        "Twenty-three sampled fields reconstruct endpoint constraints, the last quartic and its incoming claim accepted by the actual sumcheck reader",
        flush=True,
    )


def reservations():
    counter_rows = {8 * ((bank << 12) + index) + low for bank in range(4) for index in SPARSE for low in range(8)}
    returns = set(range(1536, 1536 + 32))
    assert counter_rows.isdisjoint(returns)
    occupancy_rows = set(islice((row for row in range(1 << 17) if row not in counter_rows | returns), 10 * len(SPARSE)))
    assert len(counter_rows | returns | occupancy_rows) == 18848
    memory = [(65536, 65536 + 4 * 5 * 4 * len(SPARSE)), (XOR_FRAMES, XOR_FRAMES + 32 * 128), (UNUSED, UNUSED + 32)]
    memory += [(base, base + (1 << 15)) for base in MEMORY_FRAMES] + [(CODE_FRAMES, CODE_FRAMES + (1 << 15))]
    codes = [(4096, 4096 + 2 * 5 * 4 * len(SPARSE)), (XOR_PC, XOR_PC + 2), (CODE_BASE, CODE_BASE + (1 << 13))]
    codes += [(min(MEMORY_PCS), max(MEMORY_PCS) + 1)]
    for intervals in (memory, codes):
        assert all(a[1] <= b[0] for a, b in pairwise(intervals)) and intervals[-1][1] <= 1 << 20
    print(
        "Disjoint reservations fit the supported layout: 18848 JUMP rows, 32 XOR rows, 32 unused cells; fixed valid completion remains an assumption",
        flush=True,
    )


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    word = Fraction(45, size) + Fraction(3, 1 << 256)
    counters, memory, code = span + Fraction(30, size), span + Fraction(39, size), span + Fraction(19, size)
    boundary = word + counters + memory + code
    assert boundary == 3 * span + Fraction(133, size) + Fraction(3, 1 << 256)
    assert boundary + Fraction(4, size) < Fraction(1, 1 << 156)
    print("Exact rational bound: extended boundary plus terminal interpolation below 2^-156; no earlier-wire conditioning", flush=True)


if __name__ == "__main__":
    verifier, rng = verifier_module(), Random(215)
    accelerate(verifier)
    data = geometry(verifier)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    x, y, e = [sample() for _ in range(20)], [sample() for _ in range(2)], verifier.eq_kernel([sample() for _ in range(4)])
    units = word_columns(verifier, data, x, y, e)
    xor_cycles(verifier, data, x, y, e, units)
    counters = counter_columns(verifier, data[2], data[3], x, e)
    assert len(binary_basis(column & ((1 << (8 * 192)) - 1) for column in counters)) == 8 * 192
    print("Existing two counter-label banks retain rank 1536 in the actual eight-field count/difference quotient", flush=True)
    occupancy_certificate(verifier, x, y, e)
    tail_reader(verifier, x, y, e)
    reservations()
    error_bound()
