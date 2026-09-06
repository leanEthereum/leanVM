"""Prefix-preserving whole-row swaps in all three GKR channels, not a ZK theorem."""

from functools import reduce
from operator import mul
from random import Random

from zk_column_count_audit import Library
from zk_gkr_first_packet_audit import fingerprint
from zk_pcs_audit import verifier_module
from zk_sparse_gkr_audit import contract, dense_certificate, fold, replay, weight
from zk_stacked_audit import binary_basis


def encode(values):
    return sum(int(value) << (192 * index) for index, value in enumerate(values))


def kernel_basis(columns):
    pivots, kernel = {}, []
    for index, column in enumerate(columns):
        mask = 1 << index
        while column:
            bit = column.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = column, mask
                break
            other, combination = pivots[bit]
            column ^= other
            mask ^= combination
        if not column:
            kernel.append(mask)
    return kernel


def apply_columns(columns, mask):
    value = 0
    while mask:
        low = mask & -mask
        value ^= columns[low.bit_length() - 1]
        mask ^= low
    return value


def fingerprint_parameters(v):
    rng = Random(206)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    return rng, e, beta


def native_library(v, rows=16, unused_word=None):
    rng, e, beta = fingerprint_parameters(v)
    library, positions = Library(v), {}
    indices = {"memory": set(), "code": {32, 33}}
    for index in range(rows):
        frame = 8 + 8 * index
        templates = library.templates((v.OP_MUL, 32, [], True), v.GEN**frame)
        for limb in range(3):
            templates[0][1][v.ARITH_COLUMNS.index(f"va_{limb}")] = v.E(rng.getrandbits(64))
        templates[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.ONE
        for name, exponent in zip(("o_c", "o_d", "o_f"), (3, 4, 5), strict=True):
            templates[1][1][v.JUMP_COLUMNS.index(name)] = v.GEN**exponent
        for row in library.append(templates):
            positions[row] = index
        indices["memory"].update(frame + offset for offset in range(6))
    if unused_word is not None:
        indices["memory"].add(65535)
        library.images["memory"][int(v.GEN**65535)] = tuple(unused_word)
    library.verify()
    log_rows = v.log2_strict(rows)
    assert 8 + 8 * rows < 1 << 16
    layout = v.build_layout(range(16 << 6), 16, (2, log_rows, 2, 2, log_rows, 3))
    bus, counts = v.bus_layout((0, 16, 6), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 17
    channels = [{} for _ in range(3)]
    placements = []
    for side, blocks, places in ((0, layout.push, bus.tables), (1, layout.pull, bus.tables), (2, layout.count, counts.tables)):
        placements.append(tuple(zip(blocks, places, strict=True)))
        for block, place in placements[-1]:
            assert place.index % (1 << place.variables) == 0
            for row_id, (opcode, row) in enumerate(library.rows):
                if opcode == block.owner:
                    coordinates = [form.evaluate(row.__getitem__) for form in block.coordinates]
                    channels[side][place.index + positions[row_id]] = (
                        coordinates[0] if side == 2 else beta + v.dot(e[: len(coordinates)], coordinates)
                    )
    for kind, place, separator in (("memory", bus.framework[1], v.SEP_MEM), ("code", bus.framework[2], v.SEP_BYTECODE)):
        for index in indices[kind]:
            address = int(v.GEN**index)
            for side, count in ((0, v.ONE), (1, v.GEN ** library.reads[kind, address])):
                channels[side][place.index + index] = fingerprint(v, e, beta, separator, address, count, library.images[kind][address])
    assert reduce(mul, channels[0].values()) == reduce(mul, channels[1].values())
    return library, positions, indices, layout, channels, placements, bus.depth


def permute(v, library, original_positions, channels, placements, swaps):
    result, positions = [dict(nodes) for nodes in channels], dict(original_positions)
    for opcode, start, width, edge in swaps:
        left, right = (start + child * width for child in edge)
        assert start % (4 * width) == 0 and 0 <= edge[0] < edge[1] < 4
        for row_id, (owner, _) in enumerate(library.rows):
            if owner == opcode:
                position = positions[row_id]
                if left <= position < left + width:
                    positions[row_id] += right - left
                elif right <= position < right + width:
                    positions[row_id] -= right - left
        for side, blocks in enumerate(placements):
            for block, place in blocks:
                if block.owner == opcode:
                    assert place.index % (4 * width) == 0 and start + 4 * width <= 1 << place.variables
                    a, b = place.index + left, place.index + right
                    for offset in range(width):
                        result[side][a + offset], result[side][b + offset] = result[side].get(b + offset, v.ONE), result[side].get(a + offset, v.ONE)
    for opcode in {opcode for opcode, _ in library.rows}:
        assert sorted(positions[row] for row, (owner, _) in enumerate(library.rows) if owner == opcode) == list(
            range(sum(owner == opcode for owner, _ in library.rows))
        )
    return result, positions


def boundary(v, library, indices, layout, replay):
    point = replay["result"][1]
    weights = {
        kind: {index: weight(v, point[:log], index) for index in indices[kind]}
        for kind, log in (("memory", layout.log_memory), ("code", layout.log_bytecode))
    }
    memory, counters = [v.ZERO] * 3, []
    for kind in ("memory", "code"):
        total = v.ONE
        for index in indices[kind]:
            address = int(v.GEN**index)
            total += weights[kind][index] * (v.ONE + v.GEN ** library.reads[kind, address])
            if kind == "memory":
                for limb, value in enumerate(library.images[kind][address]):
                    memory[limb] += weights[kind][index] * v.E(value)
        counters.append(total)
    return (*[value for children in replay["children"] for value in children], *memory, *counters)


def affine_columns(v, channels, placements, swaps, current):
    sources = []
    for opcode, start, width, edge in swaps:
        assert width == 1 and edge == (0, 1)
        source = []
        for side, blocks in enumerate(placements):
            for block, place in blocks:
                if block.owner == opcode:
                    index = place.index + start
                    delta = channels[side].get(index, v.ONE) + channels[side].get(index + 1, v.ONE)
                    if delta:
                        source.append((side, index // 4, delta))
        sources.append(source)
    columns = [[] for _ in swaps]
    work = [[{index // 4: value for index, value in nodes.items() if index % 4 == child} for child in range(4)] for nodes in channels]
    equality, challenges, combiner = current["equality"], current["challenge"], current["combiner"]
    for coordinate, challenge in enumerate(challenges):
        coefficients = {}
        for source in sources:
            for side, index, _ in source:
                key = side, index // 2
                if key in coefficients:
                    continue
                row = index // 2
                lines = []
                for child in work[side]:
                    left, right = (child.get(2 * row + bit, v.ONE) for bit in (0, 1))
                    lines.append((left, left + right))
                a, b, c, d = lines
                quadratic = (c[0] * d[0], c[0] * d[1] + c[1] * d[0], c[1] * d[1])
                constant, slope = a[0] + b[0], a[1] + b[1]
                cubic = (
                    quadratic[0] * constant,
                    quadratic[0] * slope + quadratic[1] * constant,
                    quadratic[1] * slope + quadratic[2] * constant,
                    quadratic[2] * slope,
                )
                scale = combiner**side * weight(v, equality[coordinate + 1 :], row)
                coefficients[key] = tuple(value * scale for value in quadratic), tuple(value * scale for value in cubic)
        for column, source in zip(columns, sources, strict=True):
            message = [v.ZERO] * 5
            for side, index, delta in source:
                quadratic, cubic = coefficients[side, index // 2]
                constant = delta if index % 2 == 0 else v.ZERO
                squared = delta * delta
                for degree, coefficient in enumerate(cubic):
                    message[degree] += coefficient * constant
                    message[degree + 1] += coefficient * delta
                for degree, coefficient in enumerate(quadratic):
                    if index % 2 == 0:
                        message[degree] += coefficient * squared
                    message[degree + 2] += coefficient * squared
            column.extend(message[1:])
        sources = [
            [(side, index // 2, delta * (challenge if index % 2 else v.ONE + challenge)) for side, index, delta in source] for source in sources
        ]
        work = [[fold(v, child, challenge) for child in children] for children in work]
    for column, source in zip(columns, sources, strict=True):
        terminal = [v.ZERO] * 12
        for side, index, delta in source:
            assert index == 0
            terminal[4 * side] += delta
            terminal[4 * side + 1] += delta
        column.extend(terminal)
    return columns


def larger_rank(v, rows):
    library, positions, indices, layout, nodes, placements, depth = native_library(v, rows)
    print("The larger valid cycle library and production bus/count placements are built", flush=True)
    base = replay(v, nodes, depth, 210)
    print("The baseline sparse transcript passes the complete reference GKR reader", flush=True)
    swaps = [(opcode, start, 1, (0, 1)) for opcode in (v.OP_MUL, v.OP_JUMP) for start in range(0, rows, 4)]
    columns = affine_columns(v, nodes, placements, swaps, base)
    print("All analytic mixed-wire columns are constructed; checking full-reader replays", flush=True)
    base_wire = encode(base["view"][3])
    for selected in ((0,), (len(swaps) - 1,), tuple(range(0, len(swaps), max(1, len(swaps) // 7)))):
        changed, _ = permute(v, library, positions, nodes, placements, [swaps[index] for index in selected])
        actual = replay(v, changed, depth, 210)
        expected = base_wire
        for index in selected:
            expected ^= encode(columns[index])
        assert actual["view"][0] == base["view"][0]
        assert encode(actual["view"][3]) == expected
        assert boundary(v, library, indices, layout, actual)[-5:] == boundary(v, library, indices, layout, base)[-5:]
    wire_columns = [encode(column) for column in columns]
    boundary_columns = [encode(column[-12:]) for column in columns]
    wire_rank = len(binary_basis(wire_columns))
    boundary_rank = len(binary_basis(boundary_columns))
    endpoint_rank = len(binary_basis([encode(column[-16:]) for column in columns]))
    assert endpoint_rank == boundary_rank
    assert wire_rank > boundary_rank
    if rows == 2048:
        assert (wire_rank, boundary_rank) == (1024, 576)
    kernel = kernel_basis(boundary_columns)
    assert len(kernel) == len(swaps) - boundary_rank and all(apply_columns(boundary_columns, mask) == 0 for mask in kernel)
    assert len(binary_basis([apply_columns(wire_columns, mask) for mask in kernel])) == wire_rank - boundary_rank
    mask = next(mask for mask in kernel if apply_columns(wire_columns, mask))
    changed, _ = permute(v, library, positions, nodes, placements, [swap for index, swap in enumerate(swaps) if mask >> index & 1])
    actual = replay(v, changed, depth, 210)
    assert actual["view"][0] == base["view"][0]
    assert boundary(v, library, indices, layout, actual) == boundary(v, library, indices, layout, base)
    assert encode(actual["view"][3]) ^ base_wire == apply_columns(wire_columns, mask)
    print(
        f"{rows}-row banks: {len(swaps)} independent bits, exact wire rank {wire_rank}, boundary rank {boundary_rank}, conditional wire rank {wire_rank - boundary_rank}",
        flush=True,
    )
    print(
        "An explicit boundary-kernel permutation preserves the full earlier wire and all seventeen boundary fields while changing the last-layer wire",
        flush=True,
    )
    print("The last quartic adds no rank after the final boundary: all surviving conditional noise lies in earlier rounds", flush=True)


def audit(v):
    dense_certificate(v)
    library, positions, indices, layout, original, placements, depth = native_library(v)
    cache = {}

    def experiment(swaps, width):
        nodes, reordered = permute(v, library, positions, original, placements, swaps)
        key = tuple(reordered.values())
        if key not in cache:
            cache[key] = replay(v, nodes, depth, 207)
        full = cache[key]
        cut = nodes if width == 1 else [contract(v, channel) for channel in nodes]
        current = full if width == 1 else replay(v, cut, depth - 2, 207)
        if width == 4:
            assert full["view"][0] == (*current["view"][0], *current["view"][3])
        retained = boundary(v, library, indices, layout, full)
        return current, full, retained, cut

    for width in (1, 4):
        swaps = [(opcode, start, width, (0, 1)) for opcode in (v.OP_MUL, v.OP_JUMP) for start in range(0, 16, 4 * width)]
        base, base_full, base_boundary, base_cut = experiment([], width)
        base_wire, base_retained = encode(base["view"][3]), encode(base_boundary)
        columns, boundary_columns, later_columns = [], [], []
        for swap in swaps:
            current, full, retained, cut = experiment([swap], width)
            assert current["view"][0] == base["view"][0]
            assert [contract(v, channel) for channel in cut] == [contract(v, channel) for channel in base_cut]
            columns.append(encode(current["view"][3]) ^ base_wire)
            boundary_columns.append(encode(retained) ^ base_retained)
            later_columns.append(encode(full["view"][3]) ^ encode(base_full["view"][3]))
            for channel in range(3):
                assert current["children"][channel][2:] == base["children"][channel][2:]
                assert (
                    current["children"][channel][0] + current["children"][channel][1] == base["children"][channel][0] + base["children"][channel][1]
                )
        if width == 1:
            assert columns == [encode(column) for column in affine_columns(v, original, placements, swaps, base)]
        for mask in ((1 << len(swaps)) - 1, sum(1 << index for index in range(0, len(swaps), 2))):
            selected = [index for index in range(len(swaps)) if mask >> index & 1]
            current, full, retained, _ = experiment([swaps[index] for index in selected], width)
            expected_wire, expected_boundary = base_wire, base_retained
            for index in selected:
                expected_wire ^= columns[index]
                expected_boundary ^= boundary_columns[index]
            assert encode(current["view"][3]) == expected_wire
            assert encode(retained) == expected_boundary
            if width == 4 and len(selected) == 2:
                mixed = encode(full["view"][3]) ^ encode(base_full["view"][3]) ^ later_columns[0] ^ later_columns[1]
                assert mixed
        shift = 192 * len(base_boundary)
        ranks = [
            len(binary_basis(vectors))
            for vectors in (columns, boundary_columns, [a << shift | b for a, b in zip(columns, boundary_columns, strict=True)])
        ]
        print(
            f"Width-{width} whole-row swaps: all three ancestor frontiers and the earlier wire stay fixed; current wire and final boundary are binary-affine",
            flush=True,
        )
        print(
            f"Exact binary ranks (wire, boundary, joint): {tuple(ranks)}; fresh wire rank after retaining the boundary: {ranks[2] - ranks[1]}",
            flush=True,
        )
    baseline, _, _, _ = experiment([], 1)
    first = (v.OP_MUL, 0, 1, (0, 1))
    second = (v.OP_MUL, 4, 1, (2, 3))
    values = [encode(experiment(swaps, 1)[0]["view"][3]) for swaps in ([], [first], [second], [first, second])]
    assert values[0] ^ values[1] ^ values[2] ^ values[3]
    for swaps in ([first], [second], [first, second]):
        current, _, _, _ = experiment(swaps, 1)
        assert current["view"][0] == baseline["view"][0]
        assert [v.E.sum(children) for children in current["children"]] == [v.E.sum(children) for children in baseline["children"]]
    print(
        "Different child-pair directions create genuine mixed Boolean terms; a coarser affine swap family also becomes nonlinear in the next layer",
        flush=True,
    )
    print("Quartet-sum disclosures survive all within-quartet permutations. These are local valid libraries, not a full VM ZK proof", flush=True)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rank-rows", type=int)
    parser.add_argument("--packed-field", action="store_true")
    args = parser.parse_args()
    module = verifier_module()
    if args.packed_field:
        from zk_audit_field import accelerate

        accelerate(module)
    if args.rank_rows:
        larger_rank(module, args.rank_rows)
    else:
        audit(module)
