"""Valid swaps covering all nineteen non-value BLAKE2s terminal columns."""

from collections import Counter
from fractions import Fraction
from random import Random

from zk_column_count_audit import Library
from zk_flock_coset_audit import reordered_index
from zk_flock_skip_audit import check_rows, witness
from zk_memory_frames_audit import joint_root_bound
from zk_metadata_audit import SPARSE
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis
from zk_three_point_audit import THREE_POINT_SUPPORT, three_point_error

OPERANDS = ("o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md")
PROGRAM = ("pc", *OPERANDS)
BASE_OFFSETS = (0, 1, 2, 3, 8, 10, 12)
SECTORS = (3, 5, 6, 7)
METADATA_ROWS = tuple(3 * 2048 + 768 + index for index in range(5))


def logical_pair(bank, index):
    if bank < 8:
        sector, tag = SECTORS[bank // 2], bank % 2
        left = (sector << 8) | (tag << 1) | ((index & 63) << 2) | ((index >> 6) << 11)
    else:
        sector = 5 if bank == 8 else 3
        left = (sector << 8) | ((index & 127) << 1) | ((64 + (index >> 7)) << 11)
    return left, left + 1


def build(verifier):
    library = Library(verifier)
    reserved = {2 * index + side for index in SPARSE for side in (0, 1)}
    available = iter(slot for slot in range(1 << 16) if slot not in reserved)
    frames, pairs, placement = set(), [[] for _ in range(10)], {}

    def fresh():
        slot = next(available)
        assert slot not in frames
        frames.add(slot)
        return verifier.GEN ** (1280 + 32 * slot)

    def cycle(pc, frame, changed=None):
        rows = library.templates((verifier.OP_BLAKE2S, pc, [], True), frame)
        if changed is not None:
            rows[0][1][verifier.BLAKE2S_COLUMNS.index(OPERANDS[changed])] = verifier.GEN**20
        for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18)):
            rows[-1][1][verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
        return library.append(rows)[0]

    for bank in range(10):
        for index in range(4096) if bank == 9 else SPARSE:
            if bank < 8:
                first = cycle(1024 + 4 * bank, fresh())
                second = cycle(1026 + 4 * bank, fresh(), bank - 1 if bank else None)
            elif bank == 8:
                slots = (2 * index, 2 * index + 1)
                assert not frames.intersection(slots)
                frames.update(slots)
                first, second = (cycle(1056, verifier.GEN ** (1280 + 32 * slot)) for slot in slots)
            else:
                frame = fresh()
                first, second = cycle(1058, frame), cycle(1058, frame)
            left, right = logical_pair(bank, index)
            assert left not in placement and right not in placement
            placement[left], placement[right] = first, second
            pairs[bank].append((index, first, second, left, right))
    assert len(placement) == 16256 and len(library.rows) == 32512
    assert len(frames) == 16256 - 4096 and not set(METADATA_ROWS).intersection(placement)
    assert all((index & 2047) not in THREE_POINT_SUPPORT and index >> 11 < 96 for index in placement)
    assert [reordered_index(index) for index in METADATA_ROWS] == list(range(432, 437))
    assert max(1280 + 32 * slot + 31 for slot in frames) < 1 << 22
    assert len(library.images["code"]) == 36
    baseline = witness(verifier, [0] * 16)
    check_rows(verifier, baseline)
    expected = {
        verifier.BLAKE2S_COLUMNS.index(name): (baseline[0] >> (64 * slot)) & ((1 << 64) - 1)
        for slot, name in enumerate(verifier.BLAKE2S_SLOTS)
        if name
    }
    assert all(int(row[column]) == value for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S for column, value in expected.items())
    library.verify()
    print("16256 BLAKE2s rows and their returns: valid fixed bytecode, closed state cycles and complete read chains.", flush=True)
    return library, pairs, placement


def certificates(verifier, library, pairs):
    field, rng = Tower(64, verifier), Random(439)
    point = [field.random(rng) for _ in range(18)]
    physical_point = [point[bit] for bit in (0, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 3, 4, 5, 6)]
    columns = verifier.BLAKE2S_COLUMNS
    counts = tuple(columns[column] for column in verifier.TABLES[verifier.OP_BLAKE2S].count_columns)
    names = (*PROGRAM, "fp", *counts)
    selected = [columns.index(name) for name in names]
    value_columns = [column for column in range(37) if column not in selected]
    assert len(selected) == 19 and len(value_columns) == 18
    program, directions = [], []

    def weight(index, at=point):
        result = 1
        for bit, coin in enumerate(at):
            result = field.mul(result, coin if index >> bit & 1 else coin ^ 1)
        return result

    for bank, group in enumerate(pairs):
        normalized, weights = [], []
        for index, first, second, left, right in group:
            a, b = library.rows[first][1], library.rows[second][1]
            assert all(a[column] == b[column] for column in value_columns)
            coefficient = weight(left) ^ weight(right)
            if index == 0:
                assert coefficient == weight(reordered_index(left), physical_point) ^ weight(reordered_index(right), physical_point)
            if bank < 9:
                difference = [int(a[column] + b[column]) for column in selected]
                scale = int(verifier.GEN ** (64 * index)) if bank == 8 else 1
                projection = difference[:8] if bank < 8 else difference[8:9]
                normalized.append([field.kmul(value, field.kinv(scale)) for value in projection])
                weights.append(field.mul(coefficient, scale))
                directions.append(sum(field.mul(coefficient, value) << (192 * column) for column, value in enumerate(difference)))
                if bank == 8:
                    assert not any(difference[:8])
            else:
                assert not any(a[column] != b[column] for column in selected[:9])
                for count in counts:
                    difference = a[columns.index(count)] + b[columns.index(count)]
                    expected = (verifier.GEN ** (2 * index) if count == "cnt_bc" else verifier.ONE) * (verifier.ONE + verifier.GEN)
                    assert difference == expected
                    if index in SPARSE:
                        directions.append(field.mul(coefficient, int(difference)) << (192 * names.index(count)))
        if bank < 9:
            assert all(row == normalized[0] for row in normalized)
            assert len(binary_basis(weights)) == 192
            if bank < 8:
                program.append(normalized[0])
    assert len(field.pivots(program)) == 8
    assert len(binary_basis(directions)) == 19 * 192
    print("Native joint metadata rank 3648, with program rank eight and one full scalar span per triangular direction.", flush=True)
    return selected, value_columns


def randomize(verifier, library, pairs, selected, value_columns):
    rng = Random(443)
    original = [(opcode, row[:]) for opcode, row in library.rows]
    for bank, group in enumerate(pairs):
        for index, first, second, _, _ in group:
            if bank < 9:
                if rng.getrandbits(1):
                    library.rows[first], library.rows[second] = library.rows[second], library.rows[first]
            elif index in SPARSE:
                a, b = library.rows[first][1], library.rows[second][1]
                for column in selected[9:]:
                    if rng.getrandbits(1):
                        a[column], b[column] = b[column], a[column]
    for before, after in zip(original, library.rows):
        opcode, a = before
        assert opcode == after[0]
        if opcode == verifier.OP_BLAKE2S:
            assert all(a[column] == after[1][column] for column in value_columns)
        else:
            assert a == after[1]
    for table in verifier.TABLES:
        for column in table.count_columns:
            assert Counter(int(row[column]) for opcode, row in original if opcode == table.opcode) == Counter(
                int(row[column]) for opcode, row in library.rows if opcode == table.opcode
            )
    library.verify()
    print("Independent swaps preserve every compression value at its position, all other-table rows, memory, final counts and the bus.", flush=True)


def error_bound():
    size = 1 << 192
    sparse = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())
    sparse += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    metadata = 4 * sparse + Fraction(108, size)
    joint = three_point_error() + Fraction(4187, size) + metadata
    assert joint < Fraction(1, 1 << 156)
    assert joint_root_bound() + joint < Fraction(1, 1 << 151)
    assert 32 * (196608 - 4096) == 6160384
    assert (3 * ((1 << 22) - 1280) - 6160384) // 256 == 25073
    assert 192512 <= 3 * (((1 << 22) - 1280) // 32) == 393096
    print("Exact joint error below 2^-156 for all 37 BLAKE2s columns and established Flock endpoints; middle rounds and PCS excluded.", flush=True)
    print("Their cross-subsystem joint view with the memory envelope and shared bus root remains below 2^-151.", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    library, pairs, placement = build(verifier)
    selected, value_columns = certificates(verifier, library, pairs)
    randomize(verifier, library, pairs, selected, value_columns)
    error_bound()
