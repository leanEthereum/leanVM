"""Exact bytecode-count normalization by reusing the mandatory compression pool."""

import argparse
from collections import Counter
from itertools import pairwise
from math import comb, isqrt
from random import Random

from zk_column_count_audit import Library
from zk_count_adapter_audit import positions as adapter_positions
from zk_count_root_audit import four_squares_small
from zk_flock_children_audit import families, pair
from zk_flock_coset_audit import library_messages, reordered_index
from zk_flock_interface_audit import packed_words
from zk_flock_lowbank_audit import positions as low_positions
from zk_flock_skip_audit import witness
from zk_pcs_audit import verifier_module
from zk_three_point_audit import THREE_POINT_SUPPORT


def counts(cap, exponent):
    assert 0 <= exponent <= cap
    first_center = isqrt(cap)
    small_center = isqrt(2 * first_center)
    first = isqrt(cap - exponent)
    residue = cap - exponent - first * first
    assert 0 <= residue <= 2 * first_center
    squares = (first, *four_squares_small(residue))
    centers = (first_center, *(small_center for _ in range(4)))
    assert all(square <= center for square, center in zip(squares, centers, strict=True))
    result = tuple(value for center, square in zip(centers, squares, strict=True) for value in (center + square, center - square))
    constant = first_center * (first_center - 1) + 4 * small_center * (small_center - 1)
    assert sum(result) == 2 * first_center + 8 * small_center
    assert exponent + sum(comb(value, 2) for value in result) == cap + constant
    return result, cap + constant


def calibration_pool():
    mandatory = {reordered_index(2048 * bank + index) for bank in range(96) for index in THREE_POINT_SUPPORT}
    adapted = {row for _, rows, _ in adapter_positions() for row in rows}
    assert len(mandatory) == 98304 and len(adapted) == 3072 and adapted <= mandatory
    pool = [sorted(row for row in mandatory - adapted if row >> 14 == slab) for slab in range(16)]
    assert all(len(rows) == 5952 for rows in pool)
    selected = [rows[: 5944 + (slab < 8)] for slab, rows in enumerate(pool)]
    assert sum(map(len, selected)) == 95112
    return selected


def balanced_frontier(histogram):
    assert sum(histogram) == 65536
    real = sorted(((code, label) for code, count in enumerate(histogram) for label in range(count)), key=lambda token: token[::-1])
    real_slabs = [real[slab::16] for slab in range(16)]
    schedule, target = counts(comb(65536, 2), sum(label for _, label in real))
    tokens = {(code, label) for code, count in enumerate(schedule) for label in range(count)}
    width, length = 1440, 46340
    assert schedule[0] >= length
    router = {(0, label) for label in (*range(16 * width), *range(length - 16 * width, length))}
    assert len(router) == 46080 and router <= tokens
    remaining = sorted(tokens - router, key=lambda token: token[::-1])
    assigned = [remaining[slab::16] for slab in range(16)]
    targets = [target // 16 + (slab < target % 16) for slab in range(16)]
    middle = width * (length - 1) // 2
    deficits = [targets[slab] - sum(label for _, label in real_slabs[slab] + assigned[slab]) - 2 * middle for slab in range(16)]
    assert sum(deficits) == 0 and max(map(abs, deficits)) <= 65535 + 92679 + 1
    pending, order, partial = list(range(16)), [], 0
    while pending:
        selected = next(slab for slab in pending if partial == 0 or (deficits[slab] <= 0 if partial > 0 else deficits[slab] >= 0))
        pending.remove(selected)
        order.append(selected)
        partial += deficits[selected]
        assert abs(partial) <= max(map(abs, deficits))
    assert partial == 0

    def transfer(start, shift):
        half = width // 2
        assert 0 <= shift <= half * half
        quotient, residue = divmod(shift, half)
        selected = {start + quotient + index + (index >= half - residue) for index in range(half)}
        complement = set(range(start, start + width)) - selected
        assert len(selected) == len(complement) == half
        return selected, complement

    capacity, partial = (width // 2) ** 2, 0
    for edge, left in enumerate(order):
        right = order[(edge + 1) % 16]
        partial += deficits[left]
        assert abs(partial) <= capacity
        shift = capacity + partial
        for start, amount in ((edge * width, min(shift, capacity)), (length - (edge + 1) * width, max(0, shift - capacity))):
            selected, complement = transfer(start, amount)
            assigned[left].extend((0, label) for label in sorted(selected))
            assigned[right].extend((0, label) for label in sorted(complement))
    assert [len(rows) for rows in assigned] == [5944 + (slab < 8) for slab in range(16)]
    assert [sum(label for _, label in real_slabs[slab] + assigned[slab]) for slab in range(16)] == targets
    flattened = [token for rows in assigned for token in rows]
    assert len(flattened) == len(set(flattened)) == len(tokens) and set(flattened) == tokens
    assert all(len(rows) == 4096 for rows in real_slabs)
    return targets, assigned, real_slabs


def coarse_certificate(verifier):
    rng = Random(691)
    random_cuts = [0, *sorted(rng.randrange(65537) for _ in range(127)), 65536]
    cases = ((65536,), (8192,) * 8, (512,) * 128, (65500, 36), tuple(right - left for left, right in pairwise(random_cuts)))
    expected, pool = None, calibration_pool()
    for histogram in cases:
        targets, assigned, real = balanced_frontier(histogram)
        assert all(len(tokens) == len(rows) for tokens, rows in zip(assigned, pool, strict=True))
        if expected is not None:
            assert targets == expected
        expected = targets
        for slab, rows in enumerate(real):
            assert len(rows) == 4096
            assert all(
                reordered_index((96 + index // 128) * 2048 + 8 * slab + (index % 8) + 128 * ((index // 8) % 16)) >> 14 == slab
                for index in range(4096)
            )
    layout = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    count_layout = verifier.bus_layout((), layout.count)
    bc = verifier.BLAKE2S_COLUMNS.index("cnt_bc")
    locations = [
        placement
        for block, placement in zip(layout.count, count_layout.tables, strict=True)
        if block.owner == verifier.OP_BLAKE2S and (bc,) in block.coordinates[0].terms
    ]
    assert len(locations) == 1 and locations[0].index >> 14 == 848
    assert len({int(verifier.GEN**value) for value in expected}) == 2
    print(
        "Five private instruction histograms give identical sixteen native BLAKE2s bytecode frontier products, with complete reused label chains.",
        flush=True,
    )
    print("Real-row sorting and a balanced 16-edge label router use the same compression pool; other count columns and JUMP remain open.", flush=True)


def certificate(verifier):
    cap = comb(65536, 2)
    largest = counts(cap, 0)
    smallest = counts(cap, cap)
    assert largest[1] == smallest[1] == 4295168588
    assert sum(largest[0]) == sum(smallest[0]) == 95112
    assert 4 * ((98304 - 3072) // 8) ** 2 < cap
    private = (cap, 8 * comb(8192, 2))
    schedules = [counts(cap, value) for value in private]
    assert schedules[0][1] == schedules[1][1]
    assert schedules[0][0] != schedules[1][0]
    pool = [row for rows in calibration_pool() for row in rows]
    assert len(pool) == 95112 and 95232 - len(pool) == 120
    layout = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    block = layout.placements[verifier.GLOBAL_COLUMN_BASES[verifier.OP_BLAKE2S] + verifier.BLAKE2S_COLUMNS.index("cnt_bc")]
    assert divmod(block.index, 1 << 22) == (59, 1 << 20)
    assert divmod(layout.placements[verifier.BYTECODE_FINAL_COUNTERS].index, 1 << 22) == (59, 5 << 18)
    pc = layout.placements[verifier.GLOBAL_COLUMN_BASES[verifier.OP_BLAKE2S] + verifier.BLAKE2S_COLUMNS.index("pc")]
    assert pc.index >> 22 != 59
    for name in ("pc", "v_pc", "cnt_bc"):
        column = verifier.GLOBAL_COLUMN_BASES[verifier.OP_JUMP] + verifier.JUMP_COLUMNS.index(name)
        assert layout.placements[column].index >> 22 != 59
    for schedule, expected in schedules:
        assigned = dict(zip(pool, (index for index, count in enumerate(schedule) for _ in range(count))))
        assert len(assigned) == 95112
        assert Counter(assigned.values()) == {index: count for index, count in enumerate(schedule) if count}
        assert expected == 4295168588
    print("A 95112-row schedule normalizes every uncertain exponent up to C(65536,2) inside the 95232 unadapted mandatory rows.", flush=True)
    print(
        "All 98304 binary choices and the 3072 adapted rows remain; 120 mandatory rows and all 57608 general-input positions are unused by calibration.",
        flush=True,
    )
    print("Calibration-only changes in lane 59 start at 2^20; real-row sorting changes the covered complement, not the masking maps.", flush=True)


def reservations():
    mandatory = {reordered_index(2048 * bank + index) for bank in range(96) for index in THREE_POINT_SUPPORT}
    metadata = {
        reordered_index(row)
        for kind, banks, support in families(True)
        for bank in range(banks)
        for index in support
        for row in pair(kind, bank, index)
    }
    low = {base + child for endpoints in low_positions() for base in endpoints for child in range(16)}
    universe = {reordered_index(row) for row in range(96 << 11)}
    assert len(metadata) == 36856 and len(low) == 3840
    assert len(mandatory | metadata | low) == len(mandatory) + len(metadata) + len(low)
    general = universe - mandatory - metadata - low
    assert len(general) == 57608
    real_positions = set(range(1 << 18)) - universe
    assert len(real_positions) == 65536 and all(sum(row >> 14 == slab for row in real_positions) == 4096 for slab in range(16))
    adapters = {row for _, _, rows in adapter_positions() for row in rows}
    assert len(adapters) == 3072 and max(adapters) < 1 << 19
    assert (1 << 20) - len(universe) == 851968
    frames = ({*range(21500), 65535}, set(range(len(general))), set(range(len(mandatory))))
    assert sum(map(len, frames)) == 177413
    occupied = [{slot // 8 for slot in segment} for segment in frames]
    assert tuple(map(len, occupied)) == (2689, 7201, 12288)
    available = []
    for segment, used in enumerate(occupied):
        for slot in range(((1 << 22) - 1280) // 256):
            if slot not in used:
                available.append((segment << 22) + 1280 + 256 * slot)
    assert len(available) == 26959
    assert all(1280 <= address % (1 << 22) <= (1 << 22) - 256 and address < 3 << 22 for address in available)
    assert (3 * ((1 << 22) - 1280) - 32 * 177413) // 256 == 26960
    old_code = {*range(1024, 1054), *range(1056, 1088), 1090, 1091}
    assert len(old_code) == 64
    added = {1110, 1111, 1112, *range(1120, 1142)}
    assert not old_code & added and len(old_code | added) == 89 and max(old_code | added) < 1 << 11
    print("One explicit Flock reservation uses 177413 frames, 89 code locations, 196608 JUMP rows and 3072 MUL rows.", flush=True)
    print("It leaves 65536 BLAKE2s positions, 851968 JUMP positions and 26959 aligned 256-cell slots for the remaining construction.", flush=True)
    print("The former 26960 figure is only a cell-count ceiling: the fixed low-bank frame fragments one additional slot.", flush=True)


def cycles(verifier, assignment, inputs):
    library = Library(verifier)

    def templates(code, frame):
        result = library.templates((verifier.OP_BLAKE2S, 1120 + 2 * code, [], True), frame)
        for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18)):
            result[-1][1][verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
        return result

    for code in range(10):
        for opcode, row in templates(code, verifier.ONE):
            for block in verifier.TABLES[opcode].flushes.pull:
                values = tuple(int(form.evaluate(row.__getitem__)) for form in block)
                if values[0] == int(verifier.SEP_BYTECODE):
                    library.images["code"][values[1]] = values[3:]
    for number, (code, words) in enumerate(zip(assignment, inputs, strict=True)):
        frame = verifier.GEN ** ((2 << 22) + 1280 + 32 * (3072 + number))
        rows = templates(code, frame)
        for slot, name in enumerate(verifier.BLAKE2S_SLOTS):
            if name:
                rows[0][1][verifier.BLAKE2S_COLUMNS.index(name)] = verifier.E(words[slot])
        library.append(rows)
    library.verify()
    return library


def validity(verifier):
    rng = Random(683)
    cap = 257
    baseline = packed_words(witness(verifier, [0] * 16))
    profiles = [packed_words(witness(verifier, message)) for message in library_messages()[:8]]
    length = sum(counts(cap, 0)[0])
    inputs = [profiles[number % len(profiles)] if rng.getrandbits(1) else baseline for number in range(length)]
    columns = verifier.BLAKE2S_COLUMNS
    template = code_image = None
    for exponent in (0, 1, 16, 127, 256, 257):
        schedule, expected = counts(cap, exponent)
        library = cycles(verifier, [code for code, count in enumerate(schedule) for _ in range(count)], inputs)
        blake = [row for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
        fixed = [[value for name, value in zip(columns, row, strict=True) if name not in ("pc", "cnt_bc")] for row in blake]
        if template is not None:
            assert fixed == template
            assert library.images["code"] == code_image
        template = fixed
        code_image = library.images["code"]
        assert len(code_image) == 20
        actual = library.exponents[verifier.OP_BLAKE2S, columns.index("cnt_bc")]
        assert exponent + actual == expected
        assert library.exponents[verifier.OP_JUMP, verifier.JUMP_COLUMNS.index("cnt_bc")] == actual
        assert all(value == 0 for value in library.memory_exponents().values())
        for code in range(10):
            selected = [
                row_id
                for row_id, (opcode, row) in enumerate(library.rows)
                if opcode == verifier.OP_BLAKE2S and row[0] == verifier.GEN ** (1120 + 2 * code)
            ]
            labels = list(range(len(selected)))
            rng.shuffle(labels)
            library.set_labels([(row_id, columns.index("cnt_bc")) for row_id in selected], labels)
            library.set_labels([(row_id + 1, verifier.JUMP_COLUMNS.index("cnt_bc")) for row_id in selected], labels)
        library.verify()
    for cap in range(128):
        for exponent in range(cap + 1):
            counts(cap, exponent)
    print(
        "Six complete calibration libraries pass the reference ISA, bus and read-chain checks with identical compression values and memory counts.",
        flush=True,
    )
    print(
        "The JUMP bytecode exponent receives the opposite uncertain shift; its frontier and the other count columns still need normalization.",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="also recheck the complete wider metadata library and its exact frame prefix")
    arguments = parser.parse_args()
    verifier = verifier_module()
    certificate(verifier)
    coarse_certificate(verifier)
    reservations()
    validity(verifier)
    if arguments.full:
        from zk_flock_children_audit import build

        build(verifier, wide=True)
