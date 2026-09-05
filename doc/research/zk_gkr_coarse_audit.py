"""An actual first-packet MUL leak and its push-child payload repair."""

from fractions import Fraction
from functools import reduce
from itertools import pairwise
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_bus_packet_audit import table_packets, weight
from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE
from zk_pcs_audit import verifier_module

HEIGHT, NOISE = 18, 32
REAL_PC, REAL_FRAME = 1 << 19, 32
PAD_PC, PAD_FRAME = 32768, 3 << 16


def layout_certificate(verifier):
    layout = verifier.build_layout(range(16 << 20), 20, (4, HEIGHT, 4, 4, 17, 3))
    bus = verifier.bus_layout((0, 20, 20), layout.push)
    assert bus.depth == 22 and layout.stack_log <= verifier.MAX_STACKED_LOG
    blocks = [(block, place) for block, place in zip(layout.push, bus.tables, strict=True) if block.owner == verifier.OP_MUL]
    assert [place.index for _, place in blocks] == [(8 + i) << HEIGHT for i in range(5)]
    assert [block.coordinates[0].terms[()] for block, _ in blocks[:4]] == [
        verifier.SEP_STATE,
        verifier.SEP_BYTECODE,
        verifier.SEP_MEM,
        verifier.SEP_MEM,
    ]
    low, high = 2 << 20, 3 << 20
    assert blocks[0][1].index == low and blocks[3][1].index + (1 << HEIGHT) == high
    for block, place in zip(layout.push, bus.tables, strict=True):
        if block.owner != verifier.OP_MUL:
            assert place.index + (1 << place.variables) <= low or place.index >= high
    assert bus.framework[1].index == 0 and bus.framework[2].index == 1 << 20
    counter_rows = {8 * ((bank << 12) + s) + bit for bank in range(4) for s in SPARSE for bit in range(8)}
    assert counter_rows.isdisjoint(range(60000, 60000 + NOISE + 1))
    frame_intervals = [
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (1 << 17, (1 << 17) + 8 * 128),
        (PAD_FRAME, PAD_FRAME + NOISE * 128),
        (1 << 18, (1 << 18) + (1 << 16)),
        (1 << 19, (1 << 19) + 32),
    ]
    assert all(left[1] <= right[0] for left, right in pairwise(frame_intervals))
    assert frame_intervals[-1][1] < 1 << 20 and REAL_PC + (1 << HEIGHT) - NOISE < 1 << 20
    print(
        "Supported actual layout: first push child 2 is exactly MUL state, bytecode, input-a and input-b; all earlier mask families lie outside it",
        flush=True,
    )
    return layout, bus


def cycles(verifier, secret, payloads):
    library, positions, mask_rows = Library(verifier), {}, []
    real_rows = NOISE
    for offset in range(real_rows):
        row = library.row(verifier.OP_MUL, REAL_PC + offset, verifier.GEN**REAL_FRAME)
        row[verifier.ARITH_COLUMNS.index("va_0")] = verifier.E(secret)
        row[verifier.ARITH_COLUMNS.index("vb_0")] = verifier.ONE
        row_id = library.append([(verifier.OP_MUL, row)])[0]
        positions[row_id] = offset
    closing = library.row(verifier.OP_JUMP, REAL_PC + real_rows, verifier.GEN**REAL_FRAME, REAL_PC)
    for name, exponent in zip(("o_c", "o_d", "o_f"), (64, 65, 66), strict=True):
        closing[verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**exponent
    positions[library.append([(verifier.OP_JUMP, closing)])[0]] = 60000
    library.pc, library.frame = PAD_PC, PAD_FRAME
    block = library.block(verifier.OP_MUL)
    for index, payload in enumerate(payloads):
        templates = library.templates(block, library.fresh_frame())
        for lane, value in enumerate(payload):
            templates[0][1][verifier.ARITH_COLUMNS.index(f"va_{lane}")] = verifier.E(value)
        templates[0][1][verifier.ARITH_COLUMNS.index("vb_0")] = verifier.ONE
        row_id, jump = library.append(templates)
        positions[row_id], positions[jump] = (1 << HEIGHT) - NOISE + index, 60001 + index
        mask_rows.append(row_id)
    library.verify()
    return library, positions, mask_rows


def block_product(verifier, library, e, beta):
    return reduce(
        mul,
        (
            beta + verifier.dot(e[: len(block)], [form.evaluate(row.__getitem__) for form in block])
            for opcode, row in library.rows
            if opcode == verifier.OP_MUL
            for block in verifier.TABLES[opcode].flushes.push[:4]
        ),
        verifier.ONE,
    )


def first_packet(verifier, child):
    root, count = verifier.E(3, 5, 7), verifier.GEN**19
    push = [verifier.GEN, verifier.GEN**2, child, root / (verifier.GEN**3 * child)]
    pull = [verifier.GEN**4, verifier.GEN**5, child, root / (verifier.GEN**9 * child)]
    values, samples = iter([root, count, *push, *pull, count, verifier.ONE, verifier.ONE, verifier.ONE]), 0

    class EndOfPrefix(Exception):
        pass

    class Stream:
        def next_scalar(self):
            return next(values)

        def next_scalars(self, number):
            return [self.next_scalar() for _ in range(number)]

        def sample(self):
            nonlocal samples
            samples += 1
            if samples > 1:
                raise EndOfPrefix
            return verifier.E(11, 13, 17)

        def samples(self, number):
            return [self.sample() for _ in range(number)]

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    try:
        verifier.verify_gkr_grand_products(22, Stream())
        raise AssertionError("an incomplete prefix returned")
    except EndOfPrefix:
        assert next(values, None) is None
    return push[2]


def leak_certificate(verifier):
    e = [verifier.ZERO] * 16
    e[3], beta = verifier.ONE, verifier.E(3, 5, 7)
    values, examples = [], []
    for secret in (0, 1):
        library, _, _ = cycles(verifier, secret, [(0, 0, 0)] * NOISE)
        actual = block_product(verifier, library, e, beta)
        total = sum(opcode == verifier.OP_MUL for opcode, _ in library.rows)
        expected = (beta * (beta + verifier.GEN) * (beta + verifier.ONE)) ** total * beta**NOISE * (beta + verifier.E(secret)) ** (total - NOISE)
        assert actual == expected
        examples.append(library)
        n = 1 << HEIGHT
        full = (beta * (beta + verifier.GEN) * (beta + verifier.ONE)) ** n * beta**NOISE * (beta + verifier.E(secret)) ** (n - NOISE)
        values.append(first_packet(verifier, full))
    assert examples[0].images["code"] == examples[1].images["code"]
    assert dict(examples[0].reads) == dict(examples[1].reads)
    assert dict(examples[0].exponents) == dict(examples[1].exponents)
    assert values[0] != values[1]
    assert Fraction(16 * (1 << HEIGHT), 1 << 192) == Fraction(1, 1 << 170)
    print(
        "Valid local MUL chains and the full-size polynomial specialization certify a nonzero first-child difference of degree at most 2^22",
        flush=True,
    )
    print("The reference GKR accepts both algebraic first packets with the same roots; the full-size VM trace is not instantiated", flush=True)


def repair_certificate(verifier, layout, bus):
    rng = Random(163)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = verifier.eq_kernel([sample() for _ in range(4)]), sample()
    point, y = [sample() for _ in range(bus.depth - 2)], [sample() for _ in range(2)]
    z = [*y, *point]
    left, right = ([[rng.getrandbits(64) for _ in range(3)] for _ in range(NOISE)] for _ in range(2))
    payload_sets = [[(0, 0, 0)] * NOISE, left, right, [[a ^ b for a, b in zip(x, y, strict=True)] for x, y in zip(left, right, strict=True)]]
    cofactors, views, images, counts = [], [], [], []
    for payloads in payload_sets:
        library, positions, mask_rows = cycles(verifier, 1, payloads)
        factors = [
            beta
            + verifier.dot(e[:6], [form.evaluate(library.rows[row_id][1].__getitem__) for form in verifier.TABLES[verifier.OP_MUL].flushes.push[2]])
            for row_id in mask_rows
        ]
        cofactors.append(block_product(verifier, library, e, beta) / reduce(mul, factors, verifier.ONE))
        push, _ = table_packets(verifier, library, positions, bus, layout, point, e)
        memory = [verifier.ZERO] * 3
        for index, payload in enumerate(payloads):
            for address in (PAD_FRAME + 128 * index, PAD_FRAME + 128 * index + 2):
                global_index = bus.framework[1].index + address
                push[global_index % 4] += weight(verifier, point, global_index >> 2) * verifier.dot(e[3:6], [verifier.E(value) for value in payload])
                for lane, value in enumerate(payload):
                    memory[lane] += weight(verifier, z[: layout.log_memory], address) * verifier.E(value)
        views.append(push + memory)
        images.append(library.images["code"])
        counts.append(dict(library.reads))
    assert all(value == cofactors[0] for value in cofactors)
    assert all(image == images[0] for image in images) and all(value == counts[0] for value in counts)
    assert all(verifier.E.sum(values) == verifier.ZERO for values in zip(*views, strict=True))
    _, boundary = error_bound()
    size, base = 1 << 192, 1 << 64
    mixing = Fraction(1 << 767) * Fraction(1 << 96, base**2 - 1) ** NOISE
    decouple = lambda other: Fraction(other + NOISE + 8, size) + Fraction(base**2, (size - 2) ** 2) + mixing
    assert boundary + decouple(1 << bus.depth) + decouple(4 * (1 << HEIGHT) - NOISE) < Fraction(1, 1 << 155)
    print(
        "Thirty-two valid random MUL cycles: the exposed push child has one affine fingerprint factor per word; its seven boundary observations are jointly K-linear",
        flush=True,
    )
    print(
        "Two successive mixed-character hybrids include this push child with the shared root and all seventeen boundary values, below 2^-155 in this layout",
        flush=True,
    )
    print("The matching pull child and the rest of the first/intervening GKR packets are still excluded", flush=True)


if __name__ == "__main__":
    v = verifier_module()
    layout, bus = layout_certificate(v)
    leak_certificate(v)
    repair_certificate(v, layout, bus)
