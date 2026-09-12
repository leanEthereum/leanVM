"""Simultaneous coarse count products via balanced row order and valid cycle routers."""

from collections import Counter, defaultdict
from fractions import Fraction
from random import Random

from zk_column_count_audit import Library
from zk_count_adapter_audit import positions as adapter_positions
from zk_flock_children_audit import families, pair
from zk_flock_coset_audit import reordered_index
from zk_flock_lowbank_audit import positions as low_positions
from zk_pcs_audit import verifier_module
from zk_three_point_audit import THREE_POINT_SUPPORT


def null_direction(columns):
    matrix = [list(map(Fraction, row)) for row in zip(*columns, strict=True)]
    pivots = []
    for column in range(len(columns)):
        selected = next((row for row in range(len(pivots), len(matrix)) if matrix[row][column]), None)
        if selected is None:
            continue
        pivot = len(pivots)
        matrix[pivot], matrix[selected] = matrix[selected], matrix[pivot]
        scale = matrix[pivot][column]
        matrix[pivot] = [value / scale for value in matrix[pivot]]
        for row in range(len(matrix)):
            if row != pivot:
                scale = matrix[row][column]
                matrix[row] = [value - scale * other for value, other in zip(matrix[row], matrix[pivot], strict=True)]
        pivots.append(column)
        if len(pivots) == len(matrix):
            break
    free = next(column for column in range(len(columns)) if column not in pivots)
    direction = [Fraction(int(column == free)) for column in range(len(columns))]
    for row, pivot in enumerate(pivots):
        direction[pivot] = -matrix[row][free]
    assert all(sum(value * coefficient for value, coefficient in zip(row, direction, strict=True)) == 0 for row in zip(*columns, strict=True))
    return direction


def steinitz_exact(vectors):
    count, dimension = len(vectors), len(vectors[0])
    if count <= dimension:
        return list(range(count))
    totals = tuple(map(sum, zip(*vectors, strict=True)))
    centered = [tuple(count * value - total for value, total in zip(vector, totals, strict=True)) for vector in vectors]
    active, removed = list(range(count)), []
    weights = [Fraction(count - dimension, count)] * count
    while len(active) > dimension:
        size = len(active)
        scale = Fraction(size - dimension - 1, size - dimension)
        for index in active:
            weights[index] *= scale
        while all(weights[index] for index in active):
            fractional = [index for index in active if 0 < weights[index] < 1]
            assert len(fractional) > dimension + 1
            chosen = fractional[: dimension + 2]
            direction = null_direction([(*centered[index], 1) for index in chosen])
            step = min(
                (1 - weights[index]) / delta if delta > 0 else -weights[index] / delta
                for index, delta in zip(chosen, direction, strict=True)
                if delta
            )
            for index, delta in zip(chosen, direction, strict=True):
                weights[index] += step * delta
                assert 0 <= weights[index] <= 1
        selected = next(index for index in active if weights[index] == 0)
        active.remove(selected)
        removed.append(selected)
        assert sum(weights[index] for index in active) == len(active) - dimension
        assert all(sum(weights[index] * centered[index][column] for index in active) == 0 for column in range(dimension))
    return active + removed[::-1]


def prefix_error(vectors, order):
    count, dimension = len(vectors), len(vectors[0])
    totals = tuple(map(sum, zip(*vectors, strict=True)))
    prefix, maximum = [0] * dimension, 0
    assert sorted(order) == list(range(count))
    for length, index in enumerate(order, 1):
        for column in range(dimension):
            prefix[column] += vectors[index][column]
            maximum = max(maximum, abs(count * prefix[column] - length * totals[column]))
    return Fraction(maximum, count)


def balanced_order(vectors, cap):
    count, dimension = len(vectors), len(vectors[0])
    totals = tuple(map(sum, zip(*vectors, strict=True)))
    pending, order, prefix = list(range(count)), [], [0] * dimension
    for length in range(1, count + 1):
        selected = min(pending, key=lambda index: max(abs(count * (prefix[c] + vectors[index][c]) - length * totals[c]) for c in range(dimension)))
        order.append(selected)
        pending.remove(selected)
        prefix = [value + other for value, other in zip(prefix, vectors[selected], strict=True)]
    if prefix_error(vectors, order) > dimension * cap:
        order = steinitz_exact(vectors)
    assert prefix_error(vectors, order) <= dimension * cap
    return order


def order_certificates():
    rng = Random(2027)
    for dimension in (1, 2, 4):
        for count in (1, dimension, dimension + 1, 12, 24):
            for cap in (0, 1, 17):
                vectors = [tuple(rng.randrange(cap + 1) for _ in range(dimension)) for _ in range(count)]
                assert prefix_error(vectors, steinitz_exact(vectors)) <= dimension * cap
    print("Exact rational Steinitz construction: all tested prefixes meet the dimension-times-label bound.", flush=True)


def fill_to(library, opcode, target, cap):
    missing = target - sum(source == opcode for source, _ in library.rows)
    assert missing >= 0
    while missing:
        length = min(missing, cap + 1)
        template = library.templates(library.block(opcode), library.fresh_frame())
        for _ in range(length):
            library.append(template)
        missing -= length


def coarse_table(library, opcode, blocks, block_size, half, cap, frozen):
    assert half % 2 == 0 and 2 * half <= block_size
    table = library.v.TABLES[opcode]
    columns = table.count_columns
    assert len(columns) * cap <= half * half // 2
    fill_to(library, opcode, blocks * (block_size - 2 * half), cap)
    ids = [index for index, (source, _) in enumerate(library.rows) if source == opcode and index not in frozen]
    vectors = [[library.labels[index, column][1] for column in columns] for index in ids]
    assert all(0 <= label <= cap for vector in vectors for label in vector)
    order = balanced_order(vectors, cap)
    free = [[block * block_size + row for row in range(block_size) if block * block_size + row not in frozen.values()] for block in range(blocks)]
    slots = [positions[2 * half :] for positions in free]
    assert sum(map(len, slots)) == len(ids)
    placement = dict(frozen)
    for index, position in zip(order, (position for block in slots for position in block), strict=True):
        placement[ids[index]] = position
    totals = tuple(map(sum, zip(*vectors, strict=True)))
    fixed = [
        [sum(library.labels[index, column][1] for index, position in frozen.items() if position // block_size == block) for column in columns]
        for block in range(blocks)
    ]
    desired, flows, length, prefix = [], [], 0, [0] * len(columns)
    for block in range(blocks):
        previous = length
        length += len(slots[block])
        desired.append([total * length // len(ids) - total * previous // len(ids) for total in totals])
        for index in order[previous:length]:
            prefix = [value + other for value, other in zip(prefix, vectors[index], strict=True)]
        flows.append([total * length // len(ids) - value for total, value in zip(totals, prefix, strict=True)])
    assert flows[-1] == [0] * len(columns)
    assert max(abs(value) for flow in flows for value in flow) <= len(columns) * cap
    frame_start = library.frame
    for block in range(blocks):
        template = library.templates(library.block(opcode), library.fresh_frame())
        targets = [library.append(template)[0] for _ in range(2 * half)]
        left, right = targets[:half], targets[half:]
        for index, position in zip(left, free[block][:half], strict=True):
            placement[index] = position
        for index, position in zip(right, free[(block + 1) % blocks][half : 2 * half], strict=True):
            placement[index] = position
        for column, flow in zip(columns, flows[block], strict=True):
            library.route([(index, column) for index in left], [(index, column) for index in right], half * half // 2 + flow)
    assert library.frame - frame_start == blocks * 128
    assert sorted(placement.values()) == list(range(blocks * block_size))
    result = []
    for block in range(blocks):
        actual = [
            sum(library.labels[index, column][1] for index, position in placement.items() if position // block_size == block) for column in columns
        ]
        expected = [a + b + half * (2 * half - 1) for a, b in zip(fixed[block], desired[block], strict=True)]
        assert actual == expected
        result.append(actual)
    return placement, result


def private_pointer_pair(library, secret):
    v, block_pc = library.v, library.pc
    library.pc += 8
    for target in (0, 20) if secret == 0 else (20, 0):
        frame = library.fresh_frame()
        row = library.row(v.OP_DEREF, block_pc, frame, pointer=frame * v.GEN**target)
        for name, offset in (("o1", 18), ("o2", 0), ("o3", 19)):
            row[v.DEREF_COLUMNS.index(name)] = v.GEN**offset
        library.append([(v.OP_DEREF, row)])
        for index in range(4):
            library.append([(v.OP_MUL, library.row(v.OP_MUL, block_pc + 1 + index, frame))])
        row = library.row(v.OP_JUMP, block_pc + 5, frame, block_pc)
        for name, offset in (("o_c", 24), ("o_d", 25), ("o_f", 26)):
            row[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        library.append([(v.OP_JUMP, row)])


def valid_library(verifier, secret, seed):
    library, frozen = Library(verifier), defaultdict(dict)
    for opcode in range(6):
        for block in range(4 if opcode == verifier.OP_BLAKE2S else 3):
            template = library.templates(library.block(opcode), library.fresh_frame())
            repetitions = [library.append(template) for _ in range(4)]
            if opcode == verifier.OP_MUL and block == 0:
                for position, rows in enumerate(repetitions):
                    frozen[opcode][rows[0]] = position
                    frozen[verifier.OP_JUMP][rows[-1]] = 64 + position
    private_pointer_pair(library, secret)
    rng, chains = Random(seed), defaultdict(list)
    for location, (address, _) in library.labels.items():
        index, column = location
        chains[address, library.rows[index][0], column].append(location)
    for locations in chains.values():
        labels = [library.labels[location][1] for location in locations]
        rng.shuffle(labels)
        library.set_labels(locations, labels)
    incoming = tuple(library.exponents[table.opcode, column] for table in verifier.TABLES for column in table.count_columns)
    preserved = [row[:] for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    placements, frontiers = {}, []
    for opcode in range(5):
        blocks, half, cap = (32, 16, 32) if opcode == verifier.OP_JUMP else (2, 8, 8)
        placement, products = coarse_table(library, opcode, blocks, 64, half, cap, frozen[opcode])
        placements.update(placement)
        frontiers.append(products)
    assert preserved == [row for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    for position, index in enumerate(index for index, (opcode, _) in enumerate(library.rows) if opcode == verifier.OP_BLAKE2S):
        placements[index] = position
    assert len(placements) == len(library.rows)
    library.verify()
    heights = (7, 7, 7, 7, 11, 4)
    assert tuple(sum(opcode == table.opcode for opcode, _ in library.rows) for table in verifier.TABLES) == tuple(1 << height for height in heights)
    layout = verifier.build_layout(range(16 << 13), 20, heights)
    count_layout = verifier.bus_layout((), layout.count)
    offsets = {}
    for block, placement in zip(layout.count, count_layout.tables, strict=True):
        ((column,),) = block.coordinates[0].terms
        offsets[block.owner, column] = placement.index
    native = defaultdict(lambda: verifier.ONE)
    for index, (opcode, row) in enumerate(library.rows):
        for column in verifier.TABLES[opcode].count_columns:
            native[(offsets[opcode, column] + placements[index]) >> 6] *= row[column]
    native = {index: int(value) for index, value in native.items() if value != verifier.ONE}
    print(f"Private pointer {secret}, label seed {seed}: native height-six normalization, all ISA constraints and complete chains pass.", flush=True)
    return incoming, frontiers, native, library.images["code"]


def candidate_geometry():
    metadata = {
        reordered_index(row)
        for kind, banks, support in families(True)
        for bank in range(banks)
        for index in support
        for row in pair(kind, bank, index)
    }
    low_blocks = low_positions()
    low = {base + child for endpoints in low_blocks for base in endpoints for child in range(16)}
    mandatory = {reordered_index(2048 * bank + index) for bank in range(96) for index in THREE_POINT_SUPPORT}
    universe = {reordered_index(row) for row in range(96 << 11)}
    general = universe - mandatory - metadata - low
    destinations = sorted(row for row in general if row >> 14 == 1)[:30]
    low.difference_update(base + child for base in low_blocks[119] for child in range(16))
    low.update((437, 438, *destinations))
    fixed_jump = metadata | low | {row for _, rows, _ in adapter_positions() for row in rows}
    fixed_mul = {row for _, _, rows in adapter_positions() for row in rows}
    assert (len(fixed_mul), len(fixed_jump)) == (3072, 43768)
    assert max(Counter(row >> 14 for row in fixed_jump).values()) == 6298
    half = 1152
    for total, fixed in ((1 << 19, fixed_mul), (1 << 20, fixed_jump)):
        for block in range(total >> 14):
            available = [row for row in range(block << 14, (block + 1) << 14) if row not in fixed]
            assert len(available) >= 2 * half
    added = (64 * half,) * 4 + (384 * half,)
    assert added == (73728, 73728, 73728, 73728, 442368)
    assert half * half // 8 == 165888
    assert 4 * 32 + 64 == 192
    assert 2 * 4 * 32 + 64 == 320
    assert 523392 + 320 < (1 << 19) - 1
    print("Candidate router reservation: 192 frames, 320 instructions; rows [73728,73728,73728,73728,442368] at label cap 165888.", flush=True)
    print(
        "Fixed MUL/JUMP mask positions are avoided. Incoming normalization, filler label caps and the total remaining row budget are not certified.",
        flush=True,
    )


if __name__ == "__main__":
    order_certificates()
    verifier, expected = verifier_module(), None
    for secret, seed in ((0, 101), (1, 101), (0, 907), (1, 907)):
        result = valid_library(verifier, secret, seed)
        if expected is not None:
            assert result == expected
        expected = result
    candidate_geometry()
