"""Joint GKR endpoint/framework hiding, excluding the preceding GKR transcript."""

from fractions import Fraction
from itertools import islice
from random import Random
from types import FunctionType, SimpleNamespace

from zk_bus_packet_audit import counter_columns, geometry, table_packets, weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

CODE_BASE, CODE_FRAMES = 1 << 17, 1 << 23
MEMORY_PC, MEMORY_FRAMES = 1 << 18, (1 << 23) + (1 << 15)
UNUSED = 1 << 24
XOR_PC, XOR_FRAMES = 2048, 1 << 22


def packed(values):
    return sum(int(value) << (192 * i) for i, value in enumerate(values))


def base_columns(verifier, data):
    layout, bus, counter, reader, point, e, y = data
    z, columns = [*y, *point], counter_columns(verifier, counter, reader, point, e)
    assert len(binary_basis(columns)) == 1536
    memory = []
    for row in range(32):
        address = UNUSED + row
        local = weight(verifier, z[: layout.log_memory], address)
        global_weight = weight(verifier, point, (bus.framework[1].index + address) >> 2)
        for limb in range(3):
            coefficient = e[3 + limb] * global_weight
            for bit in range(64):
                scalar = verifier.E(1 << bit)
                memory.append((int(coefficient * scalar) << (192 * (8 + row % 4))) ^ (int(local * scalar) << (192 * (12 + limb))))
    assert len(binary_basis(memory)) == 1152
    columns += memory
    assert len(binary_basis(columns)) == 2688
    inputs, outputs = (reader[verifier.OP_XOR, verifier.ARITH_COLUMNS.index(name)] for name in ("cnt_a", "cnt_c"))
    unit_columns = []
    sigma = bus.framework[1].eq_above(z)
    for row in range(8):
        unit = [verifier.ZERO] * 15
        for placement in (inputs, outputs):
            index = placement.index + row
            unit[8 + index % 4] += e[3] * weight(verifier, point, index >> 2)
        for address in (XOR_FRAMES + 128 * row, XOR_FRAMES + 128 * row + 2):
            index = bus.framework[1].index + address
            unit[8 + index % 4] += e[3] * weight(verifier, point, index >> 2)
            unit[12] += weight(verifier, z[: layout.log_memory], address)
        leak = verifier.dot(verifier.eq_kernel(y), unit[8:12]) + sigma * e[3] * unit[12]
        expected = e[3] * (inputs.eq_above(z) + outputs.eq_above(z)) * weight(verifier, z[: layout.table_log_heights[0]], row)
        assert leak == expected
        unit_columns.append(unit)
        columns.extend(packed([value * verifier.E(1 << bit) for value in unit]) for bit in range(64))
    assert len(binary_basis(columns)) == 2880
    print(
        "Actual source ranks: counters 1536, unused memory 1152, joint 2688; eight XOR payloads lift the fifteen-coordinate view to 2880", flush=True
    )
    return unit_columns


def xor_certificate(verifier, data, units):
    layout, bus, _, _, point, e, y = data
    rng = Random(161)
    values = [rng.getrandbits(64) for _ in range(8)]
    views, libraries = [], []
    for payloads in ([0] * 8, values):
        library, positions = Library(verifier), {}
        library.pc, library.frame = XOR_PC, XOR_FRAMES
        block = library.block(verifier.OP_XOR)
        for row, payload in enumerate(payloads):
            templates = library.templates(block, library.fresh_frame())
            templates[0][1][verifier.ARITH_COLUMNS.index("va_0")] = verifier.E(payload)
            xor, jump = library.append(templates)
            positions[xor], positions[jump] = row, 8 * 192 + row
        library.verify()
        push, pull = table_packets(verifier, library, positions, bus, layout, point, e)
        memory = [verifier.ZERO] * 3
        z = [*y, *point]
        for row, payload in enumerate(payloads):
            for address in (XOR_FRAMES + 128 * row, XOR_FRAMES + 128 * row + 2):
                index = bus.framework[1].index + address
                contribution = verifier.E(payload)
                push[index % 4] += e[3] * weight(verifier, point, index >> 2) * contribution
                pull[index % 4] += e[3] * weight(verifier, point, index >> 2) * contribution
                memory[0] += weight(verifier, z[: layout.log_memory], address) * contribution
        views.append([verifier.ZERO] * 4 + [a + b for a, b in zip(push, pull, strict=True)] + push + memory)
        libraries.append(library)
    assert libraries[0].images["code"] == libraries[1].images["code"]
    assert dict(libraries[0].reads) == dict(libraries[1].reads)
    assert dict(libraries[0].exponents) == dict(libraries[1].exponents)
    delta = [a + b for a, b in zip(*views, strict=True)]
    assert delta == [verifier.E.sum(unit[i] * verifier.E(value) for unit, value in zip(units, values, strict=True)) for i in range(15)]
    print(
        "Eight actual XOR/JUMP cycles: simultaneous K-valued payload changes match every predicted endpoint and memory column, with fixed counters and code",
        flush=True,
    )


def switch_library(verifier, kind, support, bits):
    library, memory_indices, code_indices = Library(verifier), set(), set()
    base = CODE_FRAMES if kind == "code" else MEMORY_FRAMES
    for index, choice in zip(support, bits, strict=True):
        alternatives = []
        for bit in (0, 1):
            frame_index = base + 8 * index + 4 * bit
            pc = CODE_BASE + 2 * index + bit if kind == "code" else MEMORY_PC
            row = library.row(verifier.OP_JUMP, pc, verifier.GEN**frame_index, pc)
            template = [(verifier.OP_JUMP, row)]
            library.register(template)
            alternatives.append(template)
            memory_indices.update(frame_index + offset for offset in range(3))
            code_indices.add(pc)
        library.append(alternatives[choice])
        library.append(alternatives[choice])
    library.verify()
    return library, {"memory": memory_indices, "code": code_indices}


def final_evaluation(verifier, library, kind, indices, point):
    return verifier.ONE + verifier.E.sum(
        (verifier.GEN ** library.reads[kind, int(verifier.GEN**index)] + verifier.ONE) * weight(verifier, point, index) for index in indices
    )


def final_column(verifier, kind, index, memory_point, code_point):
    factor = verifier.ONE + verifier.GEN**2
    base = CODE_FRAMES if kind == "code" else MEMORY_FRAMES
    memory = factor * (verifier.ONE + memory_point[0] * memory_point[1]) * weight(verifier, memory_point[3:], (base >> 3) + index)
    code = factor * weight(verifier, code_point[1:], (CODE_BASE >> 1) + index) if kind == "code" else verifier.ZERO
    return memory, code


def final_counters(verifier, data):
    layout, _, _, _, point, _, y = data
    z = [*y, *point]
    memory_point, code_point = z[: layout.log_memory], z[: layout.log_bytecode]
    columns = {kind: [packed(final_column(verifier, kind, index, memory_point, code_point)) for index in SPARSE] for kind in ("code", "memory")}
    assert len(binary_basis(columns["memory"])) == 192
    assert len(binary_basis(value >> 192 for value in columns["code"])) == 192
    assert len(binary_basis(columns["code"] + columns["memory"])) == 384
    for kind in ("code", "memory"):
        support = (0, 1, 64, 129)
        before, indices = switch_library(verifier, kind, support, [0] * len(support))
        baseline = [final_evaluation(verifier, before, name, indices[name], p) for name, p in (("memory", memory_point), ("code", code_point))]
        for bits in ([1, 0, 0, 0], [0, 1, 0, 1], [1] * len(support)):
            after, other_indices = switch_library(verifier, kind, support, bits)
            assert before.images == after.images and indices == other_indices
            assert len(before.rows) == len(after.rows) == 2 * len(support)
            assert dict(before.exponents) == dict(after.exponents)
            for (_, old), (_, new) in zip(before.rows, after.rows, strict=True):
                assert [old[col] for col in verifier.TABLES[verifier.OP_JUMP].count_columns] == [
                    new[col] for col in verifier.TABLES[verifier.OP_JUMP].count_columns
                ]
            observed = [
                final_evaluation(verifier, after, name, indices[name], p) + baseline[i]
                for i, (name, p) in enumerate((("memory", memory_point), ("code", code_point)))
            ]
            expected = [
                verifier.E.sum(
                    final_column(verifier, kind, index, memory_point, code_point)[i] for index, bit in zip(support, bits, strict=True) if bit
                )
                for i in range(2)
            ]
            assert observed == expected
    print(
        "Two final-counter sources have projected rank 384; valid occupancy switches preserve the full memory/code images and every count leaf",
        flush=True,
    )
    print("Triangular boundary certificate: fifteen-coordinate rank 2880 plus final-counter quotient rank 384 equals 3264", flush=True)


def reservation_certificate():
    counter_rows = {8 * ((bank << 12) + index) + low for bank in range(4) for index in SPARSE for low in range(8)}
    returns = set(range(8 * 192, 8 * 192 + 8))
    assert counter_rows.isdisjoint(returns)
    occupancy_rows = set(islice((row for row in range(1 << 17) if row not in counter_rows and row not in returns), 4 * len(SPARSE)))
    assert len(counter_rows | returns | occupancy_rows) == 16136
    blocks = [{base + 8 * index + low for index in SPARSE for low in (0, 1, 2, 4, 5, 6)} for base in (CODE_FRAMES, MEMORY_FRAMES)]
    blocks += [set(range(UNUSED, UNUSED + 32)), {XOR_FRAMES + 128 * row + low for row in range(8) for low in (0, 1, 2, 64, 65, 66)}]
    assert sum(map(len, blocks)) == len(set.union(*blocks))
    assert min(set.union(*blocks)) > 1000000 + 128 * (5 * 4 * len(SPARSE))
    codes = {CODE_BASE + 2 * index + bit for index in SPARSE for bit in (0, 1)}
    assert codes.isdisjoint({MEMORY_PC, XOR_PC, XOR_PC + 1}) and len({MEMORY_PC, XOR_PC, XOR_PC + 1}) == 3
    assert XOR_PC + 1 < 4096 and 4096 + 2 * (5 * 4 * len(SPARSE)) < min(codes)
    assert max(set.union(*blocks)) < 1 << 25 and max(codes | {MEMORY_PC}) < 1 << 19
    print(
        "Explicit reservations: 16136 disjoint JUMP slots; new cell/code sets avoid each other and the counter library, within the tested public domains",
        flush=True,
    )


def boundary_reader(verifier, data):
    layout, bus, _, _, point, _, y = data
    layout = verifier.build_layout([0] * 16, layout.log_memory, layout.table_log_heights)
    rng = Random(162)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    alpha, beta = [sample() for _ in range(4)], sample()
    packet, framework = [[sample() for _ in range(4)] for _ in range(3)], [sample() for _ in range(5)]
    z = (*y, *point)

    def gkr(depth, transcript):
        assert depth == bus.depth
        return verifier.ONE, z, tuple(verifier.multilinear_eval(children, y) for children in packet)

    values = iter(framework)
    stream = SimpleNamespace(samples=lambda count: alpha if count == 4 else None, sample=lambda: beta, next_scalar=lambda: next(values))
    stream.next_scalars = lambda count: [stream.next_scalar() for _ in range(count)]
    evaluate = FunctionType(verifier.verify_bus_balance.__code__, {**verifier.__dict__, "verify_gkr_grand_products": gkr})
    result = evaluate(layout, stream)
    assert next(values, None) is None
    assert [claim.column for claim in result.claims] == [0, 1, 2, 3, 4]
    assert [claim.value for claim in result.claims] == framework
    assert result.point == z
    print(
        "Actual bus-decomposition reader, with a small code image, consumes all five framework values after the supplied endpoint; preceding GKR is not replayed",
        flush=True,
    )


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    fifteen = span + Fraction(4 * 40 - 17 + 11, size) + Fraction(6, 1 << 256)
    seventeen = 3 * span + Fraction(6 * 40 - 17 + 9, size) + Fraction(6, 1 << 256)
    assert fifteen < Fraction(1, 1 << 157)
    assert seventeen < Fraction(1, 1 << 156)
    print("Uniform error bounds: below 2^-157 for fifteen values and below 2^-156 for the complete seventeen-value boundary", flush=True)
    return fifteen, seventeen


if __name__ == "__main__":
    v, rng = verifier_module(), Random(160)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    layout, bus, counter, reader = geometry(v, [4, 4, 4, 4, 17, 3])
    point, alpha, y = [sample() for _ in range(bus.depth - 2)], [sample() for _ in range(4)], [sample() for _ in range(2)]
    data = layout, bus, counter, reader, point, v.eq_kernel(alpha), y
    reservation_certificate()
    units = base_columns(v, data)
    xor_certificate(v, data, units)
    final_counters(v, data)
    boundary_reader(v, data)
    error_bound()
