"""Joint final GKR packet masks and the residual exposed by memory evaluation."""

from fractions import Fraction
from random import Random

from zk_column_count_audit import Library
from zk_count_children_audit import EDGES, SPARSE
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis


def weight(verifier, point, index):
    result = verifier.ONE
    for bit, coin in enumerate(point):
        result *= coin if index >> bit & 1 else verifier.ONE + coin
    return result


def geometry(verifier, heights, log_memory=25):
    layout = verifier.build_layout(range(16 << 19), log_memory, heights)
    bus = verifier.bus_layout((0, layout.log_memory, layout.log_bytecode), layout.push)
    counts = verifier.bus_layout((), layout.count)
    counter, reader = {}, {}
    for block, placement in zip(layout.count, counts.tables, strict=True):
        ((column,),) = block.coordinates[0].terms
        counter[block.owner, column] = placement
    for block, placement in zip(layout.pull, bus.tables, strict=True):
        if block.coordinates[0].terms[()] == verifier.SEP_STATE:
            continue
        ((column,),) = block.coordinates[2].terms
        reader[block.owner, column] = placement
    return layout, bus, counter, reader


def placement_certificate(verifier):
    rng = Random(158)
    assert all(len(table.count_columns) % 2 == 0 for table in verifier.TABLES)
    assert [verifier.JUMP_COLUMNS[i] for i in verifier.TABLES[verifier.OP_JUMP].count_columns] == ["cnt_c", "cnt_d", "cnt_f", "cnt_bc"]
    shapes = [[0, 0, 0, 0, 17, 3], [32] * 6, [17, 20, 16, 18, 19, 21]]
    shapes += [[rng.randrange(33) for _ in range(4)] + [rng.randrange(17, 33), rng.randrange(3, 33)] for _ in range(64)]
    columns = [verifier.JUMP_COLUMNS.index(name) for name in ("cnt_f", "cnt_bc")]
    for shape in shapes:
        _, bus, counter, reader = geometry(verifier, shape)
        c = [counter[verifier.OP_JUMP, col].index >> shape[4] for col in columns]
        b = [reader[verifier.OP_JUMP, col].index >> shape[4] for col in columns]
        assert c[0] % 2 == 0 and c[1] == c[0] + 1
        assert b[0] == b[1] + 3 and b[0] >> 1 != b[1] >> 1
        assert any(((c[0] >> j & 1) + (b[1] >> j & 1)) != ((c[1] >> j & 1) + (b[0] >> j & 1)) for j in range(bus.depth - shape[4]))
    print(
        "Every tested layout obeys the schema proof: adjacent even/odd count blocks, read blocks three apart, nonidentical selector-product polynomials",
        flush=True,
    )


def counter_columns(verifier, counter, reader, point, e):
    full_point = [verifier.ZERO, verifier.ZERO, *point]
    local = verifier.eq_kernel(point[1:13])
    tags = verifier.eq_kernel(point[13:15])
    vectors = []
    for name in ("cnt_f", "cnt_bc"):
        col = verifier.JUMP_COLUMNS.index(name)
        c = counter[verifier.OP_JUMP, col].eq_above(full_point)
        b = reader[verifier.OP_JUMP, col].eq_above(full_point)
        embedding = weight(verifier, point[15 : counter[verifier.OP_JUMP, col].variables - 2], 0)
        for bank, (first, second) in enumerate(EDGES):
            for index in SPARSE:
                delta = (verifier.ONE + verifier.GEN) * tags[bank] * local[index] * embedding
                outputs = [verifier.ZERO] * 12
                for offset, scale in ((0, c), (4, e[2] * (verifier.ONE + verifier.GEN) * b), (8, e[2] * verifier.GEN * b)):
                    outputs[offset + first] = scale * delta
                    outputs[offset + second] = scale * delta * verifier.GEN**2
                vectors.append(sum(int(value) << (192 * i) for i, value in enumerate(outputs)))
    return vectors


def field_rank(verifier):
    rng = Random(159)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    layout, bus, counter, reader = geometry(verifier, [4, 4, 4, 4, 17, 3])
    point = [sample() for _ in range(bus.depth - 2)]
    e = verifier.eq_kernel([sample() for _ in range(4)])
    vectors = counter_columns(verifier, counter, reader, point, e)
    one_bank = 4 * len(SPARSE)
    assert len(binary_basis(vectors[:one_bank])) == 768
    assert len(binary_basis(vectors)) == 1536
    assert len(binary_basis(value & ((1 << 768) - 1) for value in vectors)) == 768
    memory_start = bus.framework[1].index + (1 << 24)
    for row in range(32):
        coefficient = e[3] * weight(verifier, point, (memory_start + row) >> 2)
        for bit in range(64):
            vectors.append(int(coefficient * verifier.E(1 << bit)) << (192 * (8 + row % 4)))
    assert len(binary_basis(vectors)) == 2304
    print("Actual Boolean/K-limb matrix: one counter column rank 768, both rank 1536, all twelve packet coordinates rank 2304", flush=True)
    return layout, bus, counter, reader, point, e


def table_packets(verifier, library, positions, bus, layout, point, e):
    packets = [[verifier.ZERO] * 4 for _ in range(2)]
    for side, blocks in enumerate((layout.push, layout.pull)):
        for block, placement in zip(blocks, bus.tables, strict=True):
            for row_id, (opcode, row) in enumerate(library.rows):
                if opcode != block.owner:
                    continue
                index = placement.index + positions[row_id]
                leaf = verifier.dot(e[: len(block.coordinates)], [form.evaluate(row.__getitem__) for form in block.coordinates])
                packets[side][index % 4] += weight(verifier, point, index >> 2) * leaf
    return packets


def cycle_and_residual_certificate(verifier, data):
    layout, bus, counter, reader, point, e = data
    library, positions, switches = Library(verifier), {}, []
    columns = [verifier.JUMP_COLUMNS.index(name) for name in ("cnt_f", "cnt_bc")]
    for bank, (first, second) in enumerate(EDGES):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        rows = [library.append(template)[0] for _ in range(4)]
        ordered = (rows[0], rows[3], rows[1], rows[2])
        base = 8 * (bank << 12)
        locations = (base + first, base + second, base + 4 + first, base + 4 + second)
        positions.update(zip(ordered, locations, strict=True))
        for col in columns:
            switches.append(tuple((row, col) for row in ordered))
        for index in range(8):
            if base + index not in locations:
                filler = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
                positions[library.append(filler)[0]] = base + index
    library.verify()
    exponents, counts = dict(library.exponents), dict(library.reads)
    y = [verifier.E(17, 2, 3), verifier.E(29, 5, 7)]
    low = verifier.eq_kernel(y)
    k = verifier.GEN / (verifier.ONE + verifier.GEN)

    def ancestors():
        values = {}
        for row_id, (opcode, row) in enumerate(library.rows):
            for col in columns:
                key = col, positions[row_id] >> 2
                values[key] = values.get(key, verifier.ONE) * row[col]
        return values

    def observe():
        push, pull = table_packets(verifier, library, positions, bus, layout, point, e)
        count = [verifier.ZERO] * 4
        for row_id, (opcode, row) in enumerate(library.rows):
            for col in verifier.TABLES[opcode].count_columns:
                index = counter[opcode, col].index + positions[row_id]
                count[index % 4] += weight(verifier, point, index >> 2) * row[col]
        difference = [a + b for a, b in zip(push, pull, strict=True)]
        residual = verifier.dot(low, [a + k * b for a, b in zip(push, difference, strict=True)])
        return count + difference + push, residual

    baseline, residue = observe()
    products = ancestors()
    singles = []
    for choice in [1 << bit for bit in range(8)] + [0xA5, 0xFF]:
        for bit, switch in enumerate(switches):
            library.set_labels(switch, (1, 2, 0, 3) if choice >> bit & 1 else (0, 3, 1, 2))
        library.verify()
        actual, observed = observe()
        delta = [a + b for a, b in zip(actual, baseline, strict=True)]
        assert dict(library.exponents) == exponents and dict(library.reads) == counts
        assert ancestors() == products
        assert observed == residue
        if len(singles) < 8:
            bit = len(singles)
            bank, column = bit // 2, columns[bit % 2]
            c = counter[verifier.OP_JUMP, column].eq_above([verifier.ZERO, verifier.ZERO, *point])
            b = reader[verifier.OP_JUMP, column].eq_above([verifier.ZERO, verifier.ZERO, *point])
            scale = (verifier.ONE + verifier.GEN) * weight(verifier, point[13:15], bank) * weight(verifier, point[1:13], 0)
            expected = [verifier.ZERO] * 12
            first, second = EDGES[bank]
            for offset, factor in ((0, c), (4, e[2] * (verifier.ONE + verifier.GEN) * b), (8, e[2] * verifier.GEN * b)):
                expected[offset + first], expected[offset + second] = factor * scale, factor * scale * verifier.GEN**2
            assert delta == expected
            singles.append(delta)
        else:
            assert delta == [verifier.E.sum(singles[bit][i] for bit in range(8) if choice >> bit & 1) for i in range(12)]
    full_point = [*y, *point]
    sigma = bus.framework[1].eq_above(full_point)
    for address in range(1 << 24, (1 << 24) + 32):
        for limb in range(3):
            leaf = e[3 + limb] * weight(verifier, full_point, bus.framework[1].index + address)
            opening = sigma * e[3 + limb] * weight(verifier, full_point[: layout.log_memory], address)
            assert leaf + opening == verifier.ZERO
    residuals = []
    for secret in (0, 1):
        real = Library(verifier)
        real.pc, real.frame = library.pc + 16, library.frame + 128
        templates = real.templates(real.block(verifier.OP_XOR), real.fresh_frame())
        templates[0][1][verifier.ARITH_COLUMNS.index("va_0")] = verifier.E(secret)
        real.append(templates)
        real.verify()
        real_positions = {row_id: 8 * 192 if opcode == verifier.OP_JUMP else 0 for row_id, (opcode, _) in enumerate(real.rows)}
        push, pull = table_packets(verifier, real, real_positions, bus, layout, point, e)
        residuals.append(verifier.dot(low, [a + k * (a + b) for a, b in zip(push, pull, strict=True)]))
    input_block = reader[verifier.OP_XOR, verifier.ARITH_COLUMNS.index("cnt_a")].index
    output_block = reader[verifier.OP_XOR, verifier.ARITH_COLUMNS.index("cnt_c")].index
    predicted = e[3] * (weight(verifier, full_point, input_block) + weight(verifier, full_point, output_block))
    assert residuals[0] + residuals[1] == predicted != verifier.ZERO
    print("Valid independent frame/bytecode trades preserve all count roots and attain the predicted joint affine map", flush=True)
    print(
        "After memory evaluation, an exact residual cancels every counter and unused-memory mask but distinguishes two valid XOR/JUMP cycle libraries",
        flush=True,
    )
    print("These are local valid-cycle and sparse placement checks, not a full VM execution or a joint GKR simulator", flush=True)


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    bound = span + Fraction(3 * 40 - 17 + 8, size) + Fraction(3, 1 << 256)
    assert bound < Fraction(1, 1 << 157)
    print("Joint twelve-child packet theorem: exact rational error bound below 2^-157 for 17 <= JUMP height <= bus depth <= 40", flush=True)


if __name__ == "__main__":
    v = verifier_module()
    placement_certificate(v)
    instance = field_rank(v)
    cycle_and_residual_certificate(v, instance)
    error_bound()
