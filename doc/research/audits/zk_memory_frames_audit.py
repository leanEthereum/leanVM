"""Fixed-prefix obstruction and pin-preserving small-frame PCS certificates.

The coupling covers algebraic wire observations, not bus messages, hashes or FS.
Seeded coins make these exact finite certificates reproducible; the privacy
theorem uses independent uniform coins, not this deterministic generator.
"""

from fractions import Fraction
from random import Random
from types import SimpleNamespace

from zk_pcs_audit import Audit, RightInverse, Tower, edot, kdot, verifier_module


def prefix_obstruction(field, verifier):
    for log_length in (2, 4, 9):
        for query in (2, 3):
            weights = field.novel(log_length, query)
            assert weights[:4] == (1, query, 1, query)
            assert not any(weights[4:])

    for log_memory in range(20, 27):
        memory = 1 << log_memory
        for log_stack in range(log_memory + 2, 29):
            length = 1 << (log_stack - verifier.INITIAL_FOLDING_FACTOR)
            for start in range(0, (1 << log_stack) - 4 * memory + 1, 2 * memory):
                assert start % length == 0 or (start + 2 * memory) % length == 0

    rng, checked = Random(71), 0
    bytecode = [0] * (1 << (11 + verifier.BUS_BITS))
    for _ in range(100):
        log_memory = rng.randrange(20, 27)
        heights = [rng.randrange(0, 22) for _ in range(5)] + [rng.randrange(3, 20)]
        layout = verifier.build_layout(bytecode, log_memory, heights)
        if layout.stack_log > verifier.MAX_STACKED_LOG:
            continue
        length = 1 << (layout.stack_log - verifier.INITIAL_FOLDING_FACTOR)
        offsets = [layout.placements[i].index for i in range(4)]
        assert offsets == [offsets[0] + i * (1 << log_memory) for i in range(4)]
        assert any(offsets[i] % length == 0 for i in (0, 2))
        checked += 1
    assert checked

    floor = (1 - (1 - Fraction(1, 1 << 25)) ** 56) / 2
    assert floor > Fraction(1, 1 << 21)
    for log_stack in range(verifier.MIN_STACKED_LOG, verifier.MAX_STACKED_LOG + 1):
        for rate in range(1, 5):
            queries = verifier.derive_config(log_stack, rate).queries[0]
            domain = 1 << (log_stack - verifier.INITIAL_FOLDING_FACTOR + rate)
            assert (1 - (1 - Fraction(2, domain)) ** queries) / 2 >= floor
    print(f"Prefix leak: native basis identity, all alignment cases, {checked} reference layouts and exact privacy lower bound checked.", flush=True)


def pinned_translation(audit, difference):
    field, k = audit.field, audit.folds[0]
    length, lanes = 1 << (audit.log_size - k), 1 << k
    prefix = 5 * (1 << (audit.queries[0] + 2).bit_length())
    full = [7 ^ lane for lane in range(5)]
    assert lanes == 8 and prefix < length
    alpha = field.eq(audit.challenges[:k])
    phi = field.eq(audit.initial_point[k:])
    points = sorted(set(audit.query_points[0]) - {0, 1})
    observations = [list(field.novel(audit.log_size - k, query)) for query in points]
    observations += [list(row) for row in zip(*(field.coords(value) for value in phi))]
    row_inverse = RightInverse(field, [row[2:prefix] for row in observations])
    lane_inverse = RightInverse(field, [[field.coords(alpha[lane])[j] for lane in full] for j in range(3)])
    original = [difference[lane * length : (lane + 1) * length] for lane in range(lanes)]
    adjusted = [row[:] for row in original]
    assert all(row[:2] == [0, 0] for row in original)
    for row in adjusted:
        target = [kdot(field, weight, row) for weight in observations]
        for i, value in enumerate(row_inverse.solve(target), start=2):
            row[i] ^= value
    for i in range(length):
        folded = edot(field, alpha, [row[i] for row in adjusted])
        for lane, value in zip(full, lane_inverse.solve(field.coords(folded))):
            adjusted[lane][i] ^= value
    for lane, row in enumerate(adjusted):
        assert row[:2] == [0, 0]
        assert all(kdot(field, weight, row) == 0 for weight in observations)
        if lane not in full:
            assert row[prefix:] == original[lane][prefix:]
    assert all(edot(field, alpha, [row[i] for row in adjusted]) == 0 for i in range(length))
    return [value for row in adjusted for value in row]


def pinned_wire_certificate(field):
    cases = [(mode, False) for mode in ("random", "zero", "prefix", "small-subspace")]
    for mode, public_line in cases + [("random", True), ("prefix", True)]:
        weights = None
        if public_line:
            points_rng = Random(17)
            point = [field.random(points_rng) for _ in range(9)]
            weights = [field.mul(lane, column) for lane in field.eq(point[:3]) for column in field.eq(point[3:])]
            challenge = field.random(points_rng)
            weights[0] ^= 1 ^ challenge
            weights[1] ^= challenge
        audit = Audit(field, 9, (3, 2), (5, 3), seed=17, query_mode=mode).run(initial_weights=weights)
        rng = Random(19)
        difference = [rng.getrandbits(field.bits) if i // 64 < 3 and i % 64 >= 40 else 0 for i in range(512)]
        translated = pinned_translation(audit, difference)
        assert translated[:2] == [0, 0]
        assert any(translated[i] for i in range(512) if i // 64 < 3 and i % 64 >= 40)
        assert all(edot(field, row, translated) == 0 for row in audit.rows)
        label = mode + (" with public-input line" if public_line else "")
        print(f"Pinned memory envelope, {label}: legal mask translations cancel all {len(audit.rows)} algebraic observations.", flush=True)


def frame_reservations(field, verifier):
    memory, log_stack, frame, block = 1 << 20, 23, 256, 256
    length = 1 << (log_stack - verifier.INITIAL_FOLDING_FACTOR)
    prefix = 5 * block
    assert memory == 8 * length and frame <= block and block % frame == 0
    starts = [lane * length + offset for lane in range(3) for offset in range(prefix, length, frame)]

    def reserved(address):
        return address // length >= 3 or address % length < prefix

    for start in starts:
        assert start % frame == 0
        assert all(not reserved(address) for address in range(start, start + frame))
    assert len(starts) * frame == 3 * (length - prefix) == 389376
    assert (5 * length + 3 * prefix - 2) + len(starts) * frame + 2 == memory
    assert max(config[0] for rate in verifier.WHIR_QUERIES for config in rate) + 2 < block

    rng = Random(29)
    alpha = field.eq([field.random(rng) for _ in range(6)])
    for memory_limb in range(3):
        lanes = [8 * memory_limb + (7 ^ lane) for lane in range(5)]
        matrix = [[field.coords(alpha[lane])[j] for lane in lanes] for j in range(3)]
        assert len(field.pivots(matrix)) == 3
    print(f"Small-frame reservation: {len(starts)} slots of {frame} cells, public cells excluded, three native-field limb spans checked.", flush=True)


def kernel_vector(field, matrix):
    width = len(matrix[0])
    columns = field.pivots(matrix)
    free = next(i for i in range(width) if i not in columns)
    rows = field.pivots(list(zip(*matrix)))
    if rows:
        inverse = RightInverse(field, [matrix[i] for i in rows])
        vector = inverse.solve([matrix[i][free] for i in rows])
    else:
        vector = [0] * width
    vector[free] ^= 1
    assert any(vector) and all(kdot(field, row, vector) == 0 for row in matrix)
    return vector


def root_kernel_certificate(field):
    rng = Random(103)
    addresses = [1]
    for _ in range(511):
        addresses.append(field.kmul(addresses[-1], 2))
    for mode in ("random", "zero", "prefix", "small-subspace"):
        audit = Audit(field, 9, (3, 2), (5, 3), seed=17, query_mode=mode).run()
        alpha, full = field.eq(audit.challenges[:3]), list(range(3, 8))
        lane = kernel_vector(field, [[field.coords(alpha[i])[j] for i in full] for j in range(3)])
        observations = [list(field.novel(6, point)) for point in sorted(set(audit.query_points[0]))]
        observations += list(zip(*(field.coords(value) for value in field.eq(audit.initial_point[3:]))))
        bus, beta = field.eq([field.random(rng) for _ in range(4)]), field.random(rng)

        def fingerprint(word, coefficients=tuple(bus[3:6])):
            return edot(field, coefficients, field.coords(word))

        used = set()
        for bank in range(4):
            start, width = 2 + 9 * bank, 9
            column = kernel_vector(field, [row[start : start + width] for row in observations])
            direction = [0] * 512
            for index, coefficient in zip(full, lane):
                for j, value in enumerate(column):
                    direction[index * 64 + start + j] = field.kmul(coefficient, value)
            support = {i for i, value in enumerate(direction) if value}
            assert support and not used.intersection(support)
            assert all(i % 64 >= 2 for i in support)
            used.update(support)
            assert all(edot(field, row, direction) == 0 for row in audit.rows)
            factors = []
            for index in sorted(support):
                word = field.random(rng)
                constant = beta ^ field.mul(bus[0], 2) ^ field.mul(bus[1], addresses[index]) ^ bus[2]
                factors.append((direction[index], word, constant))
            roots = [field.mul(constant ^ fingerprint(word), field.kinv(coefficient)) for coefficient, word, constant in factors]
            assert len(set(roots)) == len(roots)
            for _ in range(3):
                parameter = field.random(rng)
                direct, polynomial = 1, 1
                for coefficient, word, constant in factors:
                    direct = field.mul(direct, constant ^ fingerprint(word ^ field.mul(coefficient, parameter)))
                    polynomial = field.mul(polynomial, constant ^ fingerprint(word) ^ field.mul(coefficient, fingerprint(parameter)))
                assert direct == polynomial
        print(f"Root kernel, {mode}: four disjoint E-valued banks preserve every audited opening and have the asserted bus polynomial.", flush=True)


def joint_root_bound():
    base, extension, queries, banks = 1 << 64, 1 << 192, 228, 12
    degree = 5 * (queries + 4)
    collisions = 4 * banks * degree * (degree - 1) // 2
    character = Fraction(degree * (1 << 96), base**2 - degree)
    mixing = Fraction(1 << 95) * character**banks
    decouple = Fraction((1 << 40) + 8 + banks * degree + collisions, extension) + Fraction(base**2, (extension - 2) ** 2) + mixing
    envelope = Fraction(3 * (22 + 12), extension)
    assert character < Fraction(1, 1 << 21)
    assert mixing < Fraction(1, 1 << 157)
    assert decouple + envelope < Fraction(1, 1 << 151)
    assert 2 + banks * (queries + 4) <= 1 << 17
    print("Shared root plus the three-limb memory envelope: exact combined bound below 2^-151 using existing reserved words.", flush=True)


def actual_lane_schedule_certificate(field):
    log_stack, length, memory = 11, 32, 256
    offsets = [lane * length for lane in (16, 24, 32)]
    for mode in ("random", "prefix"):
        rng = Random(317)
        memory_point = [field.random(rng) for _ in range(8)]
        memory_weights = field.eq(memory_point)
        public_coin = field.random(rng)
        weights = [field.random(rng) for _ in range(1 << log_stack)]
        for offset in offsets:
            scale, public_scale = field.random(rng), field.random(rng)
            weights[offset : offset + memory] = [field.mul(scale, value) for value in memory_weights]
            weights[offset] ^= field.mul(public_scale, 1 ^ public_coin)
            weights[offset + 1] ^= field.mul(public_scale, public_coin)
        audit = Audit(field, log_stack, (6, 2), (1, 1), seed=17, query_mode=mode).run(initial_weights=weights)
        local = SimpleNamespace(
            field=field,
            log_size=8,
            folds=(3,),
            queries=(1,),
            challenges=audit.challenges[:3],
            query_points=audit.query_points[:1],
            initial_point=memory_point[5:] + memory_point[:5],
        )
        translated = [0] * (1 << log_stack)
        for offset in offsets:
            difference = [rng.getrandbits(field.bits) if i // length < 3 and i % length >= 20 else 0 for i in range(memory)]
            translated[offset : offset + memory] = pinned_translation(local, difference)
        assert any(translated)
        assert all(edot(field, row, translated) == 0 for row in audit.rows)

        alpha = field.eq(audit.challenges[:3])
        full = list(range(3, 8))
        lane = kernel_vector(field, [[field.coords(alpha[i])[j] for i in full] for j in range(3)])
        observations = [list(field.novel(5, point)) for point in sorted(set(audit.query_points[0]))]
        observations += list(zip(*(field.coords(value) for value in field.eq(memory_point[:5]))))
        column = kernel_vector(field, [row[2:7] for row in observations])
        parameter = field.coords(field.random(rng))
        direction = [0] * (1 << log_stack)
        for offset, coordinate in zip(offsets, parameter):
            for index, coefficient in zip(full, lane):
                for j, value in enumerate(column, start=2):
                    direction[offset + index * length + j] = field.kmul(field.kmul(coefficient, value), coordinate)
        assert any(direction) and all(edot(field, row, direction) == 0 for row in audit.rows)
        print(
            f"Six-bit lane schedule over native fields, {mode}: memory coupling and root kernels survive arbitrary non-memory weights and public pins.",
            flush=True,
        )


if __name__ == "__main__":
    reference = verifier_module()
    tower = Tower(64, reference)
    prefix_obstruction(tower, reference)
    pinned_wire_certificate(tower)
    frame_reservations(tower, reference)
    root_kernel_certificate(tower)
    joint_root_bound()
    actual_lane_schedule_certificate(tower)
