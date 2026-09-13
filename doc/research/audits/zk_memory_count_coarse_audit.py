"""Load-bounded BLAKE2s memory frontiers, valid XOR routers and retained source spans."""

import subprocess
from collections import Counter, defaultdict
from itertools import combinations, product
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


def label_groups(exponents, cap, width=32):
    assert width >= 2 and width % 2 == 0
    radius = len(exponents) * width - 1
    target = cap + width * radius
    length = cap // width + 2 * radius + width
    length += length % 2
    used, result = set(), []
    for exponent in exponents:
        assert 0 <= exponent <= cap
        center, residue = divmod(target - exponent, width)
        selected = []
        for _ in range(width // 2 - 1):
            gap = next(value for value in range(1, radius + 1) if center - value not in used and center + value not in used)
            pair = (center - gap, center + gap)
            selected.extend(pair)
            used.update(pair)
        gap = next(value for value in range(1, radius + 1) if center - value not in used and center + value + residue not in used)
        pair = (center - gap, center + gap + residue)
        selected.extend(pair)
        used.update(pair)
        assert len(set(selected)) == width and sum(selected) + exponent == target
        assert all(0 <= value < length for value in selected)
        result.append(selected)
    assert len(used) == len(exponents) * width
    return target, length, result


def alternating_complement(length, selected):
    selected = set(selected)
    assert selected <= set(range(length)) and (length - len(selected)) % 2 == 0
    complement = sorted(set(range(length)) - selected)
    repeats = len(complement) // 2
    gap = sum(complement[1::2]) - sum(complement[::2])
    assert repeats <= gap <= repeats + len(selected)
    assert sum(complement) + sum(selected) == length * (length - 1) // 2
    return complement


def complement_certificates():
    for length in range(13):
        for removed in range(length % 2, length + 1, 2):
            for selected in combinations(range(length), removed):
                alternating_complement(length, selected)
    length, repeats, target = 33694, 16591, 1060832
    constant = 9 * (length * (length - 1) // 2 - 16 * target)
    total_cap = 9 * 65536 * 255 // 2
    intervals = (
        (-(-(constant - 9 * (repeats + 512)) // 2), (constant + total_cap - 9 * repeats) // 2),
        (-(-(constant + 9 * repeats) // 2), (constant + total_cap + 9 * (repeats + 512)) // 2),
    )
    assert total_cap == 75202560 and all(high - low == 37603584 for low, high in intervals)
    assert intervals == ((2477860002, 2515463586), (2478011625, 2515615209))
    print(f"Alternating XOR complements: exhaustive deleted-label subsets pass; full-budget count intervals {intervals}.", flush=True)


def transfers():
    for bins in range(1, 5):
        for cap in range(6):
            for exponents in product(range(cap + 1), repeat=bins):
                label_pairs(exponents, cap)
                for width in (2, 4, 6):
                    label_groups(exponents, cap, width)
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
    for load in (16, 213, 256, 906):
        cap = 4096 * (load - 1)
        for values in ([0] * 16, [cap] * 16, [cap * (index % 2) for index in range(16)], [rng.randrange(cap + 1) for _ in range(16)]):
            target, length, labels = label_groups(values, cap)
            selected = {label for group in labels for label in group}
            complement = alternating_complement(length, selected)
            assert length == 128 * (load - 1) + 1054
            assert len(complement) == 2 * (64 * (load - 1) + 271)
            assert sum(complement) + 16 * target - sum(values) == length * (length - 1) // 2
    print(
        "Thirty-two-label groups pass exact endpoint, concentrated and mixed transfers up to load 906; no statistical assumption is used.", flush=True
    )


def geometry(verifier, width):
    assert width in (2, 32)
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
    assert tuple(base + 15 for base in blocks[119]) == (9567, 12287) and {437, 438} <= general - protected
    destinations = sorted(row for row in general if row >> 14 == 1)[:30]
    moved = [(15, (437, 438))]
    if width == 32:
        moved += [(child, tuple(destinations[2 * child : 2 * child + 2])) for child in range(15)]
    vacated = {base + child for child, _ in moved for base in blocks[119]}
    relocated = {row for _, endpoints in moved for row in endpoints}
    assert len(vacated) == len(relocated) == width and relocated <= general - protected
    low = old_low - vacated | relocated
    general = general - relocated | vacated
    routers = [tuple(sorted(row for row in general if row >> 14 == slab and row >= 4096)[:width]) for slab in range(16)]
    assert set(routers[0]) == vacated and all(len(rows) == width for rows in routers)
    selected = {row for rows in routers for row in rows}
    assert len(selected) == 16 * width and selected <= general - protected
    assert len(low) == 3840 and len(general) == 57608 and len(mandatory | metadata | low | general) == len(universe)
    assert all(row % 64 >= 16 for row in vacated | relocated | selected)

    field = Tower(64, verifier)
    extra = extra_query_sources(field, blocks)
    for child, endpoints in moved:
        assert endpoints[0] >> 14 == endpoints[1] >> 14
        for block in range(5):
            index = 5 * (16 * 119 + child) + block
            polynomial = extra[index]
            assert [row for row, _ in polynomial] == [(block << 18) + base + child for base in blocks[119]]
            extra[index] = [((block << 18) + row, value) for row, (_, value) in zip(endpoints, polynomial, strict=True)]
    sources = query_sources(field)[0] + extra
    sources += [[(row, 3) for row in rows] for _, rows, _ in adapter_positions()]
    prefix = [tuple((row, value) for row, value in polynomial if row < 4096) for polynomial in sources]
    prefix = [polynomial for polynomial in prefix if polynomial]
    assert len(prefix) == len(set(prefix)) == 1117
    assert len({row for polynomial in prefix for row, _ in polynomial}) == sum(map(len, prefix))
    assert all(value for polynomial in prefix for _, value in polynomial)
    print(
        f"Relocating {width} low-bank rows frees {16 * width} router positions outside the prefix, mandatory source and protected rows.", flush=True
    )
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
    assert all(((index + row) >> 4) % 4 != 0 for index in count_bases for row in vacated | relocated)
    load = 16 if width == 2 else 256
    cap = 4096 * (load - 1)
    length = cap + 62 if width == 2 else label_groups([0] * 16, cap, width)[1]
    repeats = (length - 16 * width) // 2
    assert 9 * repeats == (276615 if width == 2 else 149319)
    assert (1 << layout.table_log_heights[verifier.OP_XOR]) - 9 * repeats == (247673 if width == 2 else 374969)
    assert (1 << layout.table_log_heights[verifier.OP_JUMP]) - len(universe) - repeats == (821233 if width == 2 else 835377)
    old_codes = {*range(1024, 1054), *range(1056, 1088), 1090, 1091, 1110, 1111, 1112, *range(1120, 1142)}
    added_codes = set(range(1142, 1152))
    assert old_codes.isdisjoint(added_codes) and len(old_codes | added_codes) == 99 and max(added_codes) < 1 << 11
    new_returns = set(range(1 << 18, (1 << 18) + repeats))
    assert new_returns.isdisjoint(universe) and len(universe | new_returns) == len(universe) + repeats and max(new_returns) < 1 << 20
    if width == 32:
        assert sum(range(3808, 3838)) == 114675
        assert len(general - selected) == 57096
    print(
        f"Load cap {load}, width {width}: {9 * repeats} XOR rows, {repeats} additional JUMPs, ten new codes and no new reserved frames.", flush=True
    )
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


def allocation():
    frames = ({*range(21500), 65535}, set(range(57608)), set(range(98304)))
    limit = ((1 << 22) - 1280) // 256
    runs = []
    for segment, allocated in enumerate(frames):
        occupied = {frame // 8 for frame in allocated}
        start = None
        for slot in range(limit + 1):
            if slot < limit and slot not in occupied:
                if start is None:
                    start = slot
            elif start is not None:
                runs.append((segment, start, slot))
                start = None
    assert runs == [(0, 2688, 8191), (0, 8192, 16379), (1, 7201, 16379), (2, 12288, 16379)]
    capacity = sum(end - start for _, start, end in runs)
    assert capacity == 26959
    rng = Random(709)
    for largest in (1, 2, 25, 64, 256, 4091):
        budget = capacity - (len(runs) - 1) * (largest - 1)
        quotient, residue = divmod(budget, largest)
        packed = [largest] * quotient + ([residue] if residue else [])
        remaining, mixed = budget, []
        while remaining:
            size = rng.randrange(1, min(largest, remaining) + 1)
            mixed.append(size)
            remaining -= size
        for requests in ([1] * budget, packed, packed[::-1], mixed):
            run, cursor, wasted = 0, runs[0][1], 0
            for size in requests:
                assert 1 <= size <= largest
                while size > runs[run][2] - cursor:
                    wasted += runs[run][2] - cursor
                    run += 1
                    assert run < len(runs)
                    cursor = runs[run][1]
                segment, start, end = runs[run]
                assert start <= cursor < cursor + size <= end
                first = (segment << 22) + 1280 + 256 * cursor
                assert first % (1 << 22) >= 1280 and first + 256 * size <= (segment + 1) << 22
                cursor += size
            assert wasted <= (len(runs) - 1) * (largest - 1)
    print(
        "Four actual payload runs support next-fit multi-slot allocations up to the proved rounded-demand bound, including large frames.", flush=True
    )


def shifted_range_counterexample(verifier):
    library = Library(verifier)
    frame = verifier.GEN ** ((1 << 22) + 1280 + 32 * 60000)
    bound, shift = 8, 4096
    value, complement = verifier.ONE / verifier.GEN, verifier.GEN**bound
    assert value not in [verifier.GEN**exponent for exponent in range(bound)]
    assert value * complement == verifier.GEN ** (bound - 1)
    rows = []
    fixed = library.row(verifier.OP_SET, 1200, frame)
    fixed[verifier.SET_COLUMNS.index("o")] = verifier.GEN**2
    fixed[verifier.SET_COLUMNS.index("k_0")] = verifier.GEN ** (bound - 1)
    rows.append((verifier.OP_SET, fixed))
    for pc, source, destination, pointer in ((1201, 0, 3, value), (1203, 1, 4, complement)):
        row = library.row(verifier.OP_DEREF, pc, frame, pointer=pointer)
        for name, exponent in (("o1", source), ("o2", shift), ("o3", destination)):
            row[verifier.DEREF_COLUMNS.index(name)] = verifier.GEN**exponent
        rows.append((verifier.OP_DEREF, row))
    multiply = library.row(verifier.OP_MUL, 1202, frame)
    multiply[verifier.ARITH_COLUMNS.index("va_0")] = value
    multiply[verifier.ARITH_COLUMNS.index("vb_0")] = complement
    rows.insert(2, (verifier.OP_MUL, multiply))
    closing = library.row(verifier.OP_JUMP, 1204, frame, 1200)
    for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18), strict=True):
        closing[verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
    rows.append((verifier.OP_JUMP, closing))
    library.append(rows)
    library.verify()
    assert all(int(verifier.GEN**address) in library.images["memory"] for address in (shift - 1, shift + bound))
    print(
        "Naively shifting both range probes accepts g^-1: the invalid range witness passes the reference ISA and complete counted buses.", flush=True
    )


def valid_cycles(verifier, width):
    snapshots, libraries = [], []
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
        selected = [library.append(template)[0] for _ in range(16 * width)]
        cap = 6 if width == 2 else 64
        length = cap + 62 if width == 2 else label_groups([0] * 16, cap, width)[1]
        repeats = (length - len(selected)) // 2
        absorbers = [library.append(copies) for _ in range(repeats)]
        before = dict(library.reads)
        expected, real_total = [], 0
        router_sums = [0, 0]
        columns = [column for column, _, _ in library.memory_reads(verifier.OP_BLAKE2S, template[0][1])]
        for index, column in enumerate(columns):
            exponents = [sum(library.labels[row, column][1] for row in real[2 * slab : 2 * slab + 2]) for slab in range(16)]
            real_total += sum(exponents)
            if width == 2:
                target, labels = label_pairs(exponents, cap)
            else:
                target, check_length, labels = label_groups(exponents, cap, width)
                assert check_length == length
            flattened = [label for group in labels for label in group]
            assert len(selected) + 2 * repeats == length
            complement = alternating_complement(length, flattened)
            router_sums = [total + sum(complement[role::2]) for role, total in enumerate(router_sums)]
            library.set_labels([(row, column) for row in selected], flattened)
            receiver = [(rows[index], verifier.ARITH_COLUMNS.index(name)) for rows in absorbers for name in ("cnt_a", "cnt_c")]
            library.set_labels(receiver, complement)
            for slab in range(16):
                rows = real[2 * slab : 2 * slab + 2] + selected[width * slab : width * slab + width]
                exponent = sum(library.labels[row, column][1] for row in rows)
                assert exponent == target
                expected.append(int(verifier.GEN**exponent))
        assert sum(router_sums) == 9 * (length * (length - 1) // 2 - 16 * target) + real_total
        assert 9 * repeats <= router_sums[1] - router_sums[0] <= 9 * (repeats + 16 * width)
        assert real_total <= 9 * len(real) * (max(multiplicities.values()) - 1) // 2
        library.verify()
        assert dict(library.reads) == before
        snapshots.append((expected, library.images, Counter(opcode for opcode, _ in library.rows), dict(library.reads)))
        libraries.append(library)
    assert all(snapshot[:3] == snapshots[0][:3] for snapshot in snapshots)
    assert snapshots[0][3] != snapshots[1][3]
    print(
        f"Width {width}: three valid private allocations yield the same 144 frontier products and public sizes, with distinct final read counts.",
        flush=True,
    )
    print("XOR self-copies, BLAKE-first labeling, code/memory images, all ISA constraints, counted buses and complete label chains pass.", flush=True)
    return libraries


if __name__ == "__main__":
    verifier = verifier_module()
    complement_certificates()
    transfers()
    allocation()
    shifted_range_counterexample(verifier)
    for width in (2, 32):
        geometry(verifier, width)
        valid_cycles(verifier, width)
