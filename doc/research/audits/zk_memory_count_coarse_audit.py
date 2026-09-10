"""Load-bounded BLAKE2s memory frontiers, valid XOR routers and retained source spans."""

import subprocess
from collections import Counter, defaultdict
from itertools import product
from pathlib import Path
from random import Random

from zk_column_count_audit import Library
from zk_count_adapter_audit import positions as adapter_positions
from zk_flock_children_audit import METADATA_ROWS, THREE_POINT_SUPPORT, families, pair
from zk_flock_coset_audit import reordered_index
from zk_flock_lowbank_audit import extra_query_sources
from zk_flock_lowbank_audit import positions as low_positions
from zk_flock_multicoset_audit import query_sources
from zk_pcs_audit import Tower, verifier_module


def label_pairs(exponents, cap):
    bins = len(exponents)
    width = 2 * bins - 1
    target = cap + 2 * width - 1
    low, high, result = set(), set(), []
    for exponent in exponents:
        assert 0 <= exponent <= cap
        required = target - exponent
        first = next(value for value in range(width) if value not in low and required - value not in high)
        second = required - first
        assert 0 <= first < width <= second <= target
        low.add(first)
        high.add(second)
        result.append((first, second))
    assert len(low | high) == 2 * bins
    assert all(exponent + sum(labels) == target for exponent, labels in zip(exponents, result, strict=True))
    return target, result


def transfers():
    for bins in range(1, 5):
        for cap in range(6):
            for exponents in product(range(cap + 1), repeat=bins):
                label_pairs(exponents, cap)
    rng = Random(701)
    cap = 4096 * 15
    for _ in range(9):
        for values in ([0] * 16, [cap] * 16, [cap * (index % 2) for index in range(16)], [rng.randrange(cap + 1) for _ in range(16)]):
            target, labels = label_pairs(values, cap)
            selected = {label for pair in labels for label in pair}
            complement = set(range(target + 1)) - selected
            assert len(complement) == cap + 30
            assert sum(complement) + 16 * target - sum(values) == target * (target + 1) // 2
            assert len(selected) == 32
    print("Exact two-label routing covers every bin vector: exhaustive small cases and all nine maximum-profile chains pass.", flush=True)


def geometry(verifier):
    blocks = low_positions()
    mandatory = {reordered_index(2048 * bank + index) for bank in range(96) for index in THREE_POINT_SUPPORT}
    metadata = {
        reordered_index(row)
        for kind, banks, support in families(True)
        for bank in range(banks)
        for index in support
        for row in pair(kind, bank, index)
    }
    old_low = {base + child for endpoints in blocks for base in endpoints for child in range(16)}
    universe = {reordered_index(row) for row in range(96 << 11)}
    general = universe - mandatory - metadata - old_low
    protected = set(map(reordered_index, METADATA_ROWS))
    assert [sum(row >> 14 == slab for row in general) for slab in range(16)] == [8] + [3840] * 15
    vacated = tuple(base + 15 for base in blocks[119])
    assert vacated == (9567, 12287) and {437, 438} <= general - protected
    low = old_low - set(vacated) | {437, 438}
    general = general - {437, 438} | set(vacated)
    routers = [tuple(sorted(row for row in general if row >> 14 == slab and row >= 4096)[:2]) for slab in range(16)]
    assert routers[0] == vacated and all(len(rows) == 2 for rows in routers)
    selected = {row for rows in routers for row in rows}
    assert len(selected) == 32 and selected <= general - protected
    assert len(low) == 3840 and len(general) == 57608 and len(mandatory | metadata | low | general) == len(universe)
    assert all(row % 64 >= 16 for row in (*vacated, 437, 438, *selected))

    field = Tower(64, verifier)
    extra = extra_query_sources(field, blocks)
    for block in range(5):
        index = 5 * (16 * 119 + 15) + block
        polynomial = extra[index]
        assert [row for row, _ in polynomial] == [(block << 18) + row for row in vacated]
        extra[index] = [((block << 18) + row, value) for row, (_, value) in zip((437, 438), polynomial, strict=True)]
    sources = query_sources(field)[0] + extra
    sources += [[(row, 3) for row in rows] for _, rows, _ in adapter_positions()]
    prefix = [tuple((row, value) for row, value in polynomial if row < 4096) for polynomial in sources]
    prefix = [polynomial for polynomial in prefix if polynomial]
    assert len(prefix) == len(set(prefix)) == 1117
    assert len({row for polynomial in prefix for row, _ in polynomial}) == sum(map(len, prefix))
    assert all(value for polynomial in prefix for _, value in polynomial)
    print("Two low-bank rows move within interval zero; the 32 router rows avoid the prefix, mandatory source and protected rows.", flush=True)
    print("The retained 4096-point prefix now encodes exactly 1117 independent bits; the adapter-child residue exclusion survives.", flush=True)

    payload = " ".join(str(value) for endpoints in blocks for value in endpoints)
    for arguments in (("--lowbank-certificate", "4096", "119"), ("--balanced-quotient-certificate", "119")):
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", *arguments],
            input=payload,
            text=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )

    layout = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    for column in verifier.TABLES[verifier.OP_BLAKE2S].count_columns:
        placement = layout.placements[verifier.GLOBAL_COLUMN_BASES[verifier.OP_BLAKE2S] + column]
        if placement.index >> 22 == 59:
            assert all((placement.index % (1 << 22)) + row >= 4096 for row in selected)
    for table in verifier.TABLES[: verifier.OP_BLAKE2S]:
        assert all(layout.placements[verifier.GLOBAL_COLUMN_BASES[table.opcode] + column].index >> 22 != 59 for column in table.count_columns)
    count_bus = verifier.bus_layout((), layout.count)
    count_bases = [placement.index for block, placement in zip(layout.count, count_bus.tables, strict=True) if block.owner == verifier.OP_BLAKE2S]
    assert [index >> 14 for index in count_bases] == list(range(704, 864, 16))
    assert all(((index + row) >> 4) % 4 != 0 for index in count_bases for row in (*vacated, 437, 438))
    cap = 4096 * 15
    repeats = cap // 2 + 15
    assert repeats == 30735 and 9 * repeats == 276615
    assert 524288 - 9 * repeats == 247673
    assert 1048576 - 196608 - repeats == 821233
    old_codes = {*range(1024, 1054), *range(1056, 1088), 1090, 1091, 1110, 1111, 1112, *range(1120, 1142)}
    added_codes = set(range(1142, 1152))
    assert old_codes.isdisjoint(added_codes) and len(old_codes | added_codes) == 99 and max(added_codes) < 1 << 11
    new_returns = set(range(1 << 18, (1 << 18) + repeats))
    assert new_returns.isdisjoint(universe) and len(universe | new_returns) == 227343 and max(new_returns) < 1 << 20
    print("Load cap 16 uses 276615 XOR rows, 30735 additional JUMPs and ten new codes, with no extra BLAKE2s rows or reserved frames.", flush=True)
    return routers


def compression(library, pc, frame):
    v = library.v
    result = library.templates((v.OP_BLAKE2S, pc, [], True), frame)
    for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18), strict=True):
        result[-1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**offset
    return result


def self_copies(library, target, pc, frame):
    v, result = library.v, []
    for index, (_, address, values) in enumerate(library.memory_reads(v.OP_BLAKE2S, target)):
        row = library.row(v.OP_XOR, pc + index, frame)
        for name, value in (("o_a", address / frame), ("o_b", v.GEN**30), ("o_c", address / frame)):
            row[v.ARITH_COLUMNS.index(name)] = value
        for limb, value in enumerate(values):
            row[v.ARITH_COLUMNS.index(f"va_{limb}")] = value
        result.append((v.OP_XOR, row))
    assert len(result) == 9
    closing = library.row(v.OP_JUMP, pc + 9, frame, pc)
    for name, offset in zip(("o_c", "o_d", "o_f"), (24, 25, 26), strict=True):
        closing[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
    return result + [(v.OP_JUMP, closing)]


def prioritize(library):
    groups = defaultdict(list)
    for location, (address, _) in library.labels.items():
        if address[0] == "memory":
            groups[address].append(location)
    for locations in groups.values():
        locations.sort(key=lambda location: (library.rows[location[0]][0] != library.v.OP_BLAKE2S, location))
        library.set_labels(locations, range(len(locations)))


def valid_cycles(verifier):
    snapshots = []
    for allocation in (list(range(32)), [index // 4 for index in range(32)], [index % 8 for index in range(32)]):
        library = Library(verifier)
        real = []
        frames = [verifier.GEN ** ((1 << 22) + 1280 + 32 * (58000 + index)) for index in range(32)]
        templates = [compression(library, 1200, frame) for frame in frames]
        for template, frame in zip(templates, frames, strict=True):
            library.register(template)
            library.append(self_copies(library, template[0][1], 1202, frame))
        for index in allocation:
            real.append(library.append(templates[index])[0])
        prioritize(library)
        library.verify()
        multiplicities = Counter(
            address for (row, _), (address, _) in library.labels.items() if library.rows[row][0] == verifier.OP_BLAKE2S and address[0] == "memory"
        )
        assert max(multiplicities.values()) <= 4

        frame = verifier.GEN ** ((1 << 22) + 1280 + 32 * 5)
        template = compression(library, 1140, frame)
        copies = self_copies(library, template[0][1], 1142, frame)
        selected = [library.append(template)[0] for _ in range(32)]
        cap, repeats = 6, 18
        absorbers = [library.append(copies) for _ in range(repeats)]
        before = dict(library.reads)
        expected = []
        columns = [column for column, _, _ in library.memory_reads(verifier.OP_BLAKE2S, template[0][1])]
        for index, column in enumerate(columns):
            exponents = [sum(library.labels[row, column][1] for row in real[2 * slab : 2 * slab + 2]) for slab in range(16)]
            target, labels = label_pairs(exponents, cap)
            flattened = [label for pair in labels for label in pair]
            assert 32 + 2 * repeats == target + 1
            complement = sorted(set(range(target + 1)) - set(flattened))
            library.set_labels([(row, column) for row in selected], flattened)
            receiver = [(rows[index], verifier.ARITH_COLUMNS.index(name)) for rows in absorbers for name in ("cnt_a", "cnt_c")]
            library.set_labels(receiver, complement)
            for slab in range(16):
                rows = real[2 * slab : 2 * slab + 2] + selected[2 * slab : 2 * slab + 2]
                exponent = sum(library.labels[row, column][1] for row in rows)
                assert exponent == target
                expected.append(int(verifier.GEN**exponent))
        library.verify()
        assert dict(library.reads) == before
        snapshots.append((expected, library.images, Counter(opcode for opcode, _ in library.rows), dict(library.reads)))
    assert all(snapshot[:3] == snapshots[0][:3] for snapshot in snapshots)
    assert snapshots[0][3] != snapshots[1][3]
    print(
        "Three valid private frame-allocation patterns yield the same 144 frontier products and public sizes, with distinct final read counts.",
        flush=True,
    )
    print("XOR self-copies, BLAKE-first labeling, code/memory images, all ISA constraints, counted buses and complete label chains pass.", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    transfers()
    geometry(verifier)
    valid_cycles(verifier)
