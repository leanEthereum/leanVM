"""Exact correlated bounds and a row/label ledger for noncompression normalization."""

import argparse
from itertools import product
from math import isqrt

from zk_column_count_audit import Library, base_trace, router_banks
from zk_count_coarse_balance_audit import (
    coarse_table,
    completion_budget,
    fill_block,
    mixed_routers,
    native_frontier,
)
from zk_count_reuse_audit import counts as unequal_counts
from zk_pcs_audit import verifier_module


def schedule(cap):
    large = isqrt(cap)
    small = isqrt(2 * large)
    return 2 * large + 8 * small, large * (large - 1) + 4 * small * (small - 1), max(0, 2 * max(large, small) - 1)


def ceil_sqrt(value):
    root = isqrt(value)
    return root + (root * root < value)


def interval_sum(intervals):
    return tuple(map(sum, zip(*intervals, strict=True)))


def plan(bytecode, differences, jump_reference, jump_differences):
    assert len(bytecode) == 5 and tuple(map(len, differences)) == (3, 3, 1, 3) and len(jump_differences) == 3
    assert jump_differences[0] == (0, 0)
    assert all(low <= high for low, high in (*bytecode, *(entry for row in differences for entry in row), jump_reference, *jump_differences))
    bc_rows, targets, bc_labels = [], [], []
    for low, high in bytecode[:4]:
        rows, offset, label = schedule(high - low)
        bc_rows.append(rows)
        targets.append(high + offset)
        bc_labels.append(label)
    jump_low = bytecode[4][0] + sum(target - high for target, (_, high) in zip(targets, bytecode[:4], strict=True))
    jump_high = bytecode[4][1] + sum(target - low for target, (low, _) in zip(targets, bytecode[:4], strict=True))
    rows, offset, label = schedule(jump_high - jump_low)
    bc_rows.append(rows)
    targets.append(jump_high + offset)
    bc_labels.append(label)
    h_low, h_high = interval_sum([entry for row in differences for entry in row] + list(jump_differences))
    s_low, s_high = h_low + 3 * jump_reference[0], h_high + 3 * jump_reference[1]
    memory_cap = (s_high - s_low) // 3
    memory_rows, memory_offset, _ = schedule(memory_cap)
    post = [
        [(low + targets[t], high + targets[t] + (2 if (t, c) == (3, 2) else 0)) for c, (low, high) in enumerate(row)]
        for t, row in enumerate(differences)
    ]
    jump_post = []
    for low, high in jump_differences:
        rest_low, rest_high = h_low - low, h_high - high
        constant = targets[4] + memory_offset
        jump_post.append((constant + (s_high + 2 * low - rest_high) // 3, constant + (s_high + 2 * high - rest_low) // 3))
    post.append(jump_post)
    radii = [max(1, ceil_sqrt(max(high - low for c, (low, high) in enumerate(row) if (t, c) != (1, 0)))) for t, row in enumerate(post)]
    rx, rm, rs, rd, rj = radii
    added = (
        bc_rows[0] + rx,
        bc_rows[1] + 3 * (rx + rm + rd + rj) + rs,
        bc_rows[2] + rs,
        bc_rows[3] + rd + 2,
        sum(bc_rows) + memory_rows + rx + rm + rs + rd + 2 * rj + 2,
    )
    return {
        "bytecode": tuple(bytecode),
        "differences": tuple(differences),
        "jump_reference": jump_reference,
        "jump_differences": tuple(jump_differences),
        "bc_rows": bc_rows,
        "targets": targets,
        "jump_interval": (jump_low, jump_high),
        "s_interval": (s_low, s_high),
        "memory_cap": memory_cap,
        "memory_rows": memory_rows,
        "memory_offset": memory_offset,
        "post": post,
        "radii": radii,
        "added": added,
        "new_label": max(*bc_labels, memory_rows - 1, 2 * max(radii) - 1, 1),
    }


def code_normalizer(library, opcode, low, high):
    column = library.v.TABLES[opcode].columns.index("cnt_bc")
    incoming = library.exponents[opcode, column]
    repeats, target = unequal_counts(high - low, incoming - low)
    before = library.memory_exponents()
    for count in repeats:
        template = library.templates(library.block(opcode), library.fresh_frame())
        library.register(template)
        for _ in range(count):
            library.append(template)
    assert library.exponents[opcode, column] == low + target
    increment = low + target - incoming
    assert all(
        value - before[source, column] == (increment if source in (opcode, library.v.OP_JUMP) else 0)
        for (source, column), value in library.memory_exponents().items()
    )


def memory_normalizer(library, deficit, budget):
    quotient, residue = divmod(deficit, 3)
    repeats, _ = unequal_counts(budget["memory_cap"], budget["memory_cap"] - quotient)
    block = library.block(library.v.OP_JUMP)
    for count in repeats:
        template = library.templates(block, library.fresh_frame())
        library.register(template)
        for _ in range(count):
            library.append(template)
    for slot in range(2):
        block = library.block(library.v.OP_DEREF)
        neutral, alias = library.fresh_frame(), library.fresh_frame()
        alternatives = (
            library.templates(block, neutral, neutral * library.v.GEN**3),
            library.templates(block, alias, alias * library.v.GEN),
        )
        for template in alternatives:
            library.register(template)
        library.append(alternatives[int(slot < residue)])
    return residue


def normalize(library, budget):
    v = library.v
    columns = [table.count_columns[:-1] for table in v.TABLES[:5]]
    assert all(table.columns[table.count_columns[-1]] == "cnt_bc" for table in v.TABLES[:5])
    original = library.memory_exponents()
    bc = [library.exponents[table.opcode, table.columns.index("cnt_bc")] for table in v.TABLES[:5]]
    for value, (low, high) in zip(bc, budget["bytecode"], strict=True):
        assert low <= value <= high
    z = [[original[t, column] - bc[t] for column in row] for t, row in enumerate(columns[:4])]
    for row, intervals in zip(z, budget["differences"], strict=True):
        assert all(low <= value <= high for value, (low, high) in zip(row, intervals, strict=True))
    reference = original[4, columns[4][0]]
    j = [original[4, column] - reference for column in columns[4]]
    assert budget["jump_reference"][0] <= reference - bc[4] <= budget["jump_reference"][1]
    assert all(low <= value <= high for value, (low, high) in zip(j, budget["jump_differences"], strict=True))
    h = sum(map(sum, z)) + sum(j)
    s = h + 3 * (reference - bc[4])
    assert budget["s_interval"][0] <= s <= budget["s_interval"][1]
    preserved = [row[:] for opcode, row in library.rows if opcode == v.OP_BLAKE2S]
    before_rows = [sum(source == opcode for source, _ in library.rows) for opcode in range(5)]
    before_frame, before_pc = library.frame, library.pc
    for opcode in range(5):
        interval = budget["jump_interval"] if opcode == 4 else budget["bytecode"][opcode]
        code_normalizer(library, opcode, *interval)
    for t, row in enumerate(columns):
        for column in row:
            assert library.exponents[t, column] == original[t, column] + budget["targets"][t] - bc[t]
    before_router = library.memory_exponents()
    banks = [bank for opcode, size in enumerate(budget["radii"]) for bank in router_banks(library, size, (opcode,))]
    fixed = {column: value - before_router[column] for column, value in library.memory_exponents().items()}
    residue = memory_normalizer(library, budget["s_interval"][1] - s, budget)
    before_route = library.memory_exponents()
    public_total = (
        sum(value for (opcode, _), value in original.items() if opcode == v.OP_BLAKE2S)
        + sum(len(row) * budget["targets"][t] for t, row in enumerate(columns))
        + budget["s_interval"][1]
        + 3 * budget["memory_offset"]
        + sum(fixed.values())
    )
    assert sum(before_route.values()) == public_total
    for c, column in enumerate(columns[4]):
        value = before_route[4, column] - fixed[4, column]
        expected = budget["targets"][4] + budget["memory_offset"] + j[c] + (budget["s_interval"][1] - h) // 3
        assert value == expected
    for (opcode, column), target, receiver in banks:
        low, high = budget["post"][opcode][columns[opcode].index(column)]
        assert low <= before_route[opcode, column] - fixed[opcode, column] <= high
        shift = high + fixed[opcode, column] - before_route[opcode, column]
        library.route(target, receiver, shift)
        assert library.exponents[opcode, column] == high + fixed[opcode, column]
    assert sum(library.memory_exponents().values()) == sum(before_route.values())
    assert library.frame - before_frame == 69 * 128 and library.pc - before_pc == 175
    assert [sum(source == opcode for source, _ in library.rows) - before_rows[opcode] for opcode in range(5)] == list(budget["added"])
    assert all(label <= budget["new_label"] for (index, _), (_, label) in library.labels.items() if index >= sum(before_rows) + len(preserved))
    assert preserved == [row for opcode, row in library.rows if opcode == v.OP_BLAKE2S]
    return tuple(before_route[4, column] - fixed[4, column] for column in columns[4]), residue


def jump_skew(library, skew):
    for count in (2 + skew, 2 - skew):
        block = library.block(library.v.OP_JUMP)
        templates = [library.templates(block, library.fresh_frame()) for _ in range(4)]
        for template in templates:
            library.register(template)
        for template in templates[:count]:
            library.append(template)


def asymmetric_jump(library, scatter):
    column = library.v.JUMP_COLUMNS.index("cnt_c")
    columns = [library.v.JUMP_COLUMNS.index(name) for name in ("cnt_c", "cnt_d", "cnt_f")]
    before = [library.exponents[library.v.OP_JUMP, source] for source in columns]
    block = library.v.OP_JUMP, library.pc, [column], True
    library.pc += 4
    templates = [library.templates(block, library.fresh_frame()) for _ in range(2)]
    for template in templates:
        library.register(template)
    for index in range(3):
        library.append(templates[int(scatter and index % 2 == 1)])
    added = [library.exponents[library.v.OP_JUMP, source] - value for source, value in zip(columns, before, strict=True)]
    assert [value - added[0] for value in added] == [0, -1 if scatter else -3, -1 if scatter else -3]


def fixture(verifier, multiplicity, scatter, skew, budget, coarse):
    library = Library(verifier)
    base_trace(library, (multiplicity,) * 5 + (1,), scatter)
    block = library.block(verifier.OP_BLAKE2S)
    for _ in range(5):
        library.append(library.templates(block, library.fresh_frame()))
    asymmetric_jump(library, scatter)
    jump_skew(library, skew)
    incoming_bc = library.exponents[4, verifier.JUMP_COLUMNS.index("cnt_bc")]
    jump_result = normalize(library, budget)
    products = tuple(library.exponents[table.opcode, column] for table in verifier.TABLES for column in table.count_columns)
    frontier = None
    if coarse:
        routers, placements = mixed_routers(library, 4, 32), {}
        for opcode in range(5):
            placement, _ = coarse_table(library, opcode, 32 if opcode == 4 else 4, 128, 32, 128, {}, routers.get(opcode), True)
            placements.update(placement)
        for position, index in enumerate(index for index, (opcode, _) in enumerate(library.rows) if opcode == verifier.OP_BLAKE2S):
            placements[index] = position
        frontier = native_frontier(library, placements, (9, 9, 9, 9, 12, 3), 7)
    else:
        library.verify()
    print(
        f"Correlated normalization: multiplicity={multiplicity}, scatter={scatter}, JUMP skew={skew}; complete chains and ISA pass, coarse={coarse}.",
        flush=True,
    )
    return (products, frontier, library.images), (incoming_bc, jump_result)


def interval_certificates():
    bytecode = ((0, 3), (0, 6), (0, 3), (0, 3), (0, 48))
    differences = (((-3, 3),) * 3, ((-6, 9),) * 3, ((-3, 3),), ((-3, 3),) * 3)
    jump_differences = ((0, 0), (-3, 0), (-3, 0))
    budget = plan(bytecode, differences, (-48, 70), jump_differences)
    assert budget["radii"] == [3, 4, 3, 3, 6]
    for width in (0, 48, (1 << 31) - (1 << 15)):
        enlarged = plan((*bytecode[:4], (0, width)), differences, (-width, 70), jump_differences)
        assert enlarged["radii"] == budget["radii"]
        assert [high - low for low, high in enlarged["post"][4]] == [high - low for low, high in budget["post"][4]]
        assert enlarged["new_label"] <= 165888
        completion_budget(enlarged["added"])
        print(
            f"JUMP code width {width}: router sizes {enlarged['radii']}, added rows {enlarged['added']}, maximum new label {enlarged['new_label']}.",
            flush=True,
        )
    for cap in range(200):
        rows, offset, label = schedule(cap)
        for deficit in (0, cap // 2, cap):
            values, target = unequal_counts(cap, cap - deficit)
            assert sum(values) == rows and max(values, default=0) <= label + 1 and target == cap + offset
    tiny_differences = (((-2, 2), (0, 0), (0, 0)), ((0, 0),) * 3, ((0, 0),), ((0, 0),) * 3)
    tiny = plan(((0, 2),) * 4 + ((3, 7),), tiny_differences, (-4, 2), ((0, 0), (-2, 2), (-2, 2)))
    for z, j1, j2, reference in product(range(-2, 3), range(-2, 3), range(-2, 3), range(-4, 3)):
        h = z + j1 + j2
        s = h + 3 * reference
        quotient, residue = divmod(tiny["s_interval"][1] - s, 3)
        assert 0 <= quotient <= tiny["memory_cap"] and 0 <= residue < 3
        for c, value in enumerate((0, j1, j2)):
            actual = tiny["targets"][4] + tiny["memory_offset"] + value + reference + quotient
            expected = tiny["targets"][4] + tiny["memory_offset"] + value + (tiny["s_interval"][1] - h) // 3
            low, high = tiny["post"][4][c]
            assert actual == expected and low <= actual <= high
    print("Correlated interval endpoints pass every small case, including signed differences, all residues and nonzero lower bounds.", flush=True)
    return budget


def prefill_certificates(verifier):
    for opcode in range(5):
        for length in (0, 1, 15, 16, 17, 31, 32, 33, 63, 64, 65):
            library = Library(verifier)
            fill_block(library, opcode, length)
            library.verify()
            quotient, remainder = divmod(length, 16)
            for source in {opcode, verifier.OP_JUMP}:
                bc = library.exponents[source, verifier.TABLES[source].columns.index("cnt_bc")]
                expected = -quotient * remainder if source == opcode else -quotient * int(remainder > 0)
                assert all(value - bc == expected for (table, _), value in library.memory_exponents().items() if table == source)
    print("Private-length prefilling: exact linear memory-minus-code increments and equal JUMP-memory increments pass for all opcodes.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--coarse", action="store_true", help="also check the integrated native coarse frontier")
    args = parser.parse_args()
    budget, verifier, expected = interval_certificates(), verifier_module(), None
    prefill_certificates(verifier)
    for multiplicity, scatter in ((2, False), (3, True)) if args.coarse else ((2, False), (2, True), (3, False), (3, True)):
        previous = None
        for skew in (0, 2):
            result, diagnostic = fixture(verifier, multiplicity, scatter, skew, budget, args.coarse)
            if previous is not None:
                assert diagnostic[0] != previous[0] and diagnostic[1] == previous[1]
            if expected is not None:
                assert result == expected
            expected, previous = result, diagnostic
    print("The large-width ledger is a conditional interval calculation, not a guest-wide resource or statistical-ZK theorem.", flush=True)
