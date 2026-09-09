"""Cross-parent same-frame swaps for the twelve transmitted GKR children."""

import argparse
import subprocess
from collections import Counter
from fractions import Fraction
from pathlib import Path
from random import Random

from zk_column_count_audit import Library
from zk_flock_columns_audit import METADATA_ROWS, OPERANDS, PROGRAM
from zk_flock_coset_audit import novel_factors, reordered_index
from zk_flock_pair_opening_audit import blake_bus_forms, evaluate
from zk_flock_skip_audit import check_rows, witness
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import RightInverse, Tower, kdot, verifier_module
from zk_stacked_audit import binary_basis
from zk_three_point_audit import THREE_POINT_SUPPORT, three_point_error
from zk_two_point_audit import DENSE_FIXED, dense_fixed_error

SHORT_SUPPORT = list(range(64)) + [low | (1 << bit) for bit in range(6, 11) for low in range(64)]
PC_SUPPORT = [index for index in DENSE_FIXED if index != 192]
PC_BITS = (3, 4, 5, 6, 7, 13, 11, 12, 14, 15, 16, 17)
COUNT_BITS = (3, 4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17)
WIDE_BITS = (2, 3, 4, 5, 6, 11, 12, 13, 14, 15, 16, 17)
OPERAND_BITS = (4, 5, 6, 7, 11, 12, 13, 14, 15, 16, 17)


def pair(kind, bank, index):
    if kind == "operand":
        left, bits, distance = (7 << 8) | (bank << 1), OPERAND_BITS, 1
    elif kind == "wide":
        left, bits, distance = (6 << 8) | bank, WIDE_BITS, 128
    else:
        left = ((3 if kind == "pc" else 5) << 8) | bank
        bits, distance = PC_BITS if kind == "pc" else COUNT_BITS, 4
    left |= sum(((index >> number) & 1) << bit for number, bit in enumerate(bits))
    assert left & distance == 0
    return left, left | distance


def families(wide):
    result = [("operand", 8, SHORT_SUPPORT), ("pc", 4, PC_SUPPORT), ("count", 4, DENSE_FIXED)]
    if wide:
        result.append(("wide", 4, DENSE_FIXED))
    return result


def placement_certificate(wide=False):
    occupied = {}
    for kind, banks, support in families(wide):
        for bank in range(banks):
            for index in support:
                for logical in pair(kind, bank, index):
                    assert logical not in occupied
                    occupied[logical] = kind, bank, index
    assert len(occupied) == 26616 + (10240 if wide else 0)
    assert not set(occupied).intersection(METADATA_ROWS)
    assert all((logical & 2047) not in THREE_POINT_SUPPORT and logical >> 11 < 96 for logical in occupied)
    for child in range(4):
        for index in DENSE_FIXED:
            left, right = map(reordered_index, pair("count", child, index))
            assert left ^ right == 4 and left & 3 == right & 3 == child
            if wide:
                left, right = map(reordered_index, pair("wide", child, index))
                assert left ^ right == 8 and left & 3 == right & 3 == child
    print(f"{len(occupied)} paired-source rows occupy disjoint complementary positions, with all four GKR child slots covered.", flush=True)
    return occupied


def build(verifier, wide=False):
    library, groups = Library(verifier), {}
    reserved = {2 * index + side for index in SHORT_SUPPORT for side in (0, 1)}
    available = iter(slot for slot in range(1 << 16) if slot not in reserved)
    frames = set()

    def frame(slot=None):
        if slot is None:
            slot = next(available)
        assert slot not in frames
        frames.add(slot)
        return verifier.GEN ** (1280 + 32 * slot)

    def cycle(pc, address, changed=None, controls=16):
        rows = library.templates((verifier.OP_BLAKE2S, pc, [], True), address)
        if changed is not None:
            rows[0][1][verifier.BLAKE2S_COLUMNS.index(OPERANDS[changed])] = verifier.GEN**20
        for name, offset in zip(("o_c", "o_d", "o_f"), range(controls, controls + 3)):
            rows[-1][1][verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
        return library.append(rows)[0]

    for kind, banks, support in families(wide):
        for bank in range(banks):
            group = groups[kind, bank] = []
            for number, index in enumerate(support):
                if kind == "operand" and bank < 7:
                    first = cycle(1024 + 4 * bank, frame())
                    second = cycle(1026 + 4 * bank, frame(), bank)
                elif kind == "operand":
                    first, second = (cycle(1052, frame(2 * index + side)) for side in (0, 1))
                else:
                    address = frame()
                    pc = 1056 + 4 * bank if kind == "pc" else (1080 if kind == "wide" else 1072) + 2 * bank
                    first = cycle(pc, address)
                    second = cycle(pc + 2 if kind == "pc" else pc, address, controls=24 if kind == "pc" else 16)
                    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
                    assert all(library.rows[first][1][column] == verifier.ONE for column in counts[:-1])
                    assert all(library.rows[second][1][column] == verifier.GEN for column in counts[:-1])
                    if kind in ("count", "wide"):
                        assert number == (index & 255) + 256 * ((index >> 8).bit_length())
                        assert library.rows[first][1][counts[-1]] == verifier.GEN ** (2 * number)
                        assert library.rows[second][1][counts[-1]] == verifier.GEN ** (2 * number + 1)
                group.append((index, first, second, *pair(kind, bank, index)))
    size = 26616 + (10240 if wide else 0)
    assert len(library.rows) == 2 * size and len(library.images["code"]) == 54 + (8 if wide else 0)
    assert len(frames) == 16380 + (5120 if wide else 0)
    assert max(1280 + 32 * slot + 31 for slot in frames) < 1 << 22
    baseline = witness(verifier, [0] * 16)
    check_rows(verifier, baseline)
    values = {
        verifier.BLAKE2S_COLUMNS.index(name): (baseline[0] >> (64 * slot)) & ((1 << 64) - 1)
        for slot, name in enumerate(verifier.BLAKE2S_SLOTS)
        if name
    }
    assert all(int(row[column]) == value for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S for column, value in values.items())
    library.verify()
    print(
        f"{size} compressions and their returns are valid at {len(library.images['code'])} public code locations, with complete read chains.",
        flush=True,
    )
    return library, groups


def certificate(verifier, library, groups):
    field, rng = Tower(64, verifier), Random(521)
    terminal = [field.random(rng) for _ in range(18)]
    parent = [verifier.E(*field.coords(field.random(rng))) for _ in range(24)]
    point = [verifier.ZERO, verifier.ZERO, *parent]
    alphas = [verifier.E(*field.coords(field.random(rng))) for _ in range(4)]
    forms, positions = blake_bus_forms(verifier, point, alphas)
    columns = verifier.BLAKE2S_COLUMNS
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    selected = [columns.index(name) for name in (*PROGRAM, "fp")] + list(counts)
    value_columns = [column for column in range(37) if column not in selected]
    matrix = [[form.terms.get((column,), verifier.ZERO) for column in counts] for form in forms]
    left, right = (counts.index(columns.index(name)) for name in ("cnt_cv1", "cnt_out0"))
    assert all(a == verifier.GEN * b for a, b in zip(matrix[0], matrix[1]))
    assert matrix[1][left] * matrix[2][right] != matrix[1][right] * matrix[2][left]
    residual = verifier.Form(dict(forms[0].terms))
    residual.add_scaled(forms[1], verifier.GEN)
    selector = verifier.eq_eval(parent[16:], [verifier.E((185 >> bit) & 1) for bit in range(8)])
    fingerprint = verifier.eq_eval(alphas, [verifier.ONE, verifier.ZERO, verifier.ZERO, verifier.ZERO])
    assert residual.terms[columns.index("pc"),] == (verifier.ONE + verifier.GEN) * fingerprint * selector
    assert positions[1]["cnt_bc"] == 185

    def equality(index, at):
        value = 1
        for bit, coin in enumerate(at):
            value = field.mul(value, coin if index >> bit & 1 else coin ^ 1)
        return value

    def packed(values):
        return sum(value << (192 * index) for index, value in enumerate(values))

    parent_int = [int(value) for value in parent[:16]]
    query = (1 << 18) + 1234
    factors = novel_factors(field, 18, query)

    def raw_weight(physical):
        value = 1
        for bit, factor in enumerate(factors):
            if physical >> bit & 1:
                value = field.kmul(value, factor)
        return value

    directions, counter_interface, four_kernel = [], [], []
    child_pc_weights = [[] for _ in range(4)]
    for (kind, bank), group in groups.items():
        if kind == "wide":
            continue
        for _, first, second, logical_left, logical_right in group:
            a, b = library.rows[first][1], library.rows[second][1]
            assert all(a[column] == b[column] for column in value_columns)
            physical_left, physical_right = map(reordered_index, (logical_left, logical_right))
            terminal_weight = equality(logical_left, terminal) ^ equality(logical_right, terminal)
            child_weights = [0] * 4
            for physical in (physical_left, physical_right):
                child_weights[physical & 3] ^= equality(physical >> 2, parent_int)
            source_raw = raw_weight(physical_left) ^ raw_weight(physical_right)
            if kind != "count":
                difference = [int(a[column] + b[column]) for column in selected]
                metadata = [field.mul(terminal_weight, value) for value in difference]
                form_delta = [int(form.evaluate(a.__getitem__) + form.evaluate(b.__getitem__)) for form in forms]
                children = [field.mul(child_weights[child], value) for child in range(4) for value in form_delta]
                residual_delta = form_delta[0] ^ field.mul(int(verifier.GEN), form_delta[1])
                prior_counts = [field.mul(child_weights[child], value) for child in range(4) for value in difference[9:]]
                residuals = [field.mul(weight, residual_delta) for weight in child_weights]
                assert a[columns.index("cnt_cv1")] + b[columns.index("cnt_cv1")] == a[columns.index("cnt_out0")] + b[columns.index("cnt_out0")]
                directions.append(packed([*metadata, *children]))
                four_kernel.append(packed([*metadata, *children]))
                counter_interface.append(packed([*metadata, *prior_counts, *residuals]))
                if kind == "pc":
                    assert all(a[column] == b[column] for column in selected[1:9])
                    assert all(weight == 0 for child, weight in enumerate(child_weights) if child != bank)
                    child_pc_weights[bank].append(terminal_weight | (child_weights[bank] << 192))
            else:
                assert all(weight == 0 for child, weight in enumerate(child_weights) if child != bank)
                for number, column in enumerate(counts):
                    difference = int(a[column] + b[column])
                    metadata = field.mul(terminal_weight, difference) << ((9 + number) * 192)
                    count_delta = field.mul(child_weights[bank], difference)
                    children = sum(field.mul(int(matrix[side][number]), count_delta) << ((19 + 3 * bank + side) * 192) for side in range(3))
                    raw = field.kmul(source_raw, difference) if columns[column] in ("cnt_cv1", "cnt_out0") else 0
                    second_raw = field.kmul(raw, field.kinv(query)) if bank & 1 else raw
                    second_raw = field.kmul(second_raw, query ^ 1) if bank & 1 else second_raw
                    directions.append(metadata | children | (raw << (31 * 192)) | (second_raw << (31 * 192 + 64)))
                    kernel = field.kmul(raw_weight(physical_left & ~7), difference) if columns[column] in ("cnt_cv1", "cnt_out0") else 0
                    four_kernel.append(metadata | children | (kernel << (31 * 192 + 64 * bank)))
                    counter_interface.append(
                        metadata | (count_delta << ((19 + 10 * bank + number) * 192)) | (raw << (63 * 192)) | (second_raw << (63 * 192 + 64))
                    )
    assert all(len(binary_basis(weights)) == 384 for weights in child_pc_weights)
    assert len(binary_basis(counter_interface)) == 63 * 192 + 128 == 12224
    assert len(binary_basis(directions)) == 31 * 192 + 128 == 6080
    assert len(binary_basis(four_kernel)) == 31 * 192 + 256 == 6208
    print(
        "Native joint ranks: 12224 for the retained count/residual map, 6080 for metadata, all twelve actual GKR children and both raw query values.",
        flush=True,
    )
    print("The core also retains four coset-kernel coordinates jointly with the actual metadata and children, at native rank 6208.", flush=True)
    return selected, value_columns


def randomize(verifier, library, groups, selected, value_columns):
    rng = Random(523)
    original = [(opcode, row[:]) for opcode, row in library.rows]
    for (kind, _), group in groups.items():
        for _, first, second, _, _ in group:
            if kind in ("count", "wide"):
                a, b = library.rows[first][1], library.rows[second][1]
                for column in selected[9:]:
                    if rng.getrandbits(1):
                        a[column], b[column] = b[column], a[column]
            elif rng.getrandbits(1):
                library.rows[first], library.rows[second] = library.rows[second], library.rows[first]
    for (opcode, a), (after_opcode, b) in zip(original, library.rows):
        assert opcode == after_opcode
        assert all(a[column] == b[column] for column in value_columns) if opcode == verifier.OP_BLAKE2S else a == b
    for table in verifier.TABLES:
        for column in table.count_columns:
            before = Counter(int(row[column]) for opcode, row in original if opcode == table.opcode)
            after = Counter(int(row[column]) for opcode, row in library.rows if opcode == table.opcode)
            assert before == after
    library.verify()
    print("Independent local swaps preserve the full bus, fixed compression values and all count products, without a global shuffle.", flush=True)


def collapse_certificate(verifier):
    field = Tower(64, verifier)
    for kind, banks, support in families(False):
        for bank in range(banks):
            for index in support:
                left, right = map(reordered_index, pair(kind, bank, index))
                assert left >> 3 == right >> 3
    for query in (1 << 18, (1 << 18) + 1234, (1 << 19) - 2):
        factors = novel_factors(field, 18, query)

        def novel(index, at=factors):
            value = 1
            for bit, factor in enumerate(at):
                if index >> bit & 1:
                    value = field.kmul(value, factor)
            return value

        for child in range(4):
            left, right = map(reordered_index, pair("wide", child, 0))
            left, right = left & ~7, right & ~7
            assert novel(left) ^ novel(right)
    assert 98304 - 36856 == 61448
    assert 196608 - 4 * len(PC_SUPPORT) - 8 * len(DENSE_FIXED) == 181252
    assert 32 * 181252 == 5800064
    assert (3 * ((1 << 22) - 1280) - 5800064) // 256 == 26480
    print("The core preserves aligned eight-row sums, retaining the known fixed-completion PCS obstruction.", flush=True)
    print(
        "Four independent wider count banks break that invariant without changing the proved boundary error; full PCS privacy is still open.",
        flush=True,
    )


def coset_certificate(verifier):
    field = Tower(64, verifier)
    difference = int(verifier.ONE + verifier.GEN)
    for coset in (1 << 18, ((1 << 18) + 1234) & ~7, (1 << 19) - 8):
        factors = novel_factors(field, 18, coset)

        def coordinates(coefficients, at=factors):
            result = [0] * 8
            for index, value in coefficients.items():
                for bit in range(3, 18):
                    if index >> bit & 1:
                        value = field.kmul(value, at[bit])
                result[index & 7] ^= value
            return result

        matrix = [field.novel(3, coset + offset) for offset in range(8)]
        inverse = RightInverse(field, matrix)
        for kind in ("count", "wide"):
            for child in range(4):
                for index in (0, 1, 1279):
                    left, right = map(reordered_index, pair(kind, child, index))
                    coefficients = {left: difference, right: difference}
                    low = coordinates(coefficients)
                    values = [evaluate(field, coefficients, coset + offset) for offset in range(8)]
                    assert values == [kdot(field, row, low) for row in matrix]
                    assert inverse.solve(values) == low
                    assert all(value == 0 for slot, value in enumerate(low) if slot not in (child, child + 4))
                    quotient = low[child] ^ low[child + 4]
                    assert (quotient == 0) == (kind == "count")
                    assert low[child] or low[child + 4]
    print("Exact eight-point interpolation: the core fills four paired-coefficient kernels, and wider banks fill their four quotients.", flush=True)


def short_span_error():
    size = 1 << 192
    initial = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())

    def remaining(dimension):
        return min(Fraction(1), Fraction(size, size - 1) ** 5 * Fraction(2) ** (192 - 6 * dimension))

    result = initial + remaining(64)
    for dimension in range(32, 64):
        result += Fraction(((1 << 32) - 1) ** 2, (size - 1) * ((1 << (64 - dimension)) - 1)) * remaining(dimension)
    assert result + Fraction(33, size) < Fraction(1, 1 << 158)
    return result


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    result = three_point_error() + 2 * short_span_error() + 2 * span
    result += sum((dense_fixed_error(bits) for bits in (64, 192, 193, 256)), Fraction()) + Fraction(4355, size)
    assert result < Fraction(1, 1 << 155)
    assert joint_root_bound() + result < Fraction(1, 1 << 151)
    frames = 196608 - 4 * len(PC_SUPPORT) - 4 * len(DENSE_FIXED)
    assert frames == 186372 and 32 * frames == 5963904
    assert (3 * ((1 << 22) - 1280) - 32 * frames) // 256 == 25840
    print("Exact joint boundary error below 2^-155; including the memory envelope and shared root remains below 2^-151.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="check every valid cycle, the joint native ranks and randomized bus")
    parser.add_argument("--wide", action="store_true", help="include the additional banks crossing aligned eight-row blocks")
    arguments = parser.parse_args()
    placement_certificate(arguments.wide)
    error_bound()
    verifier = verifier_module()
    collapse_certificate(verifier)
    if arguments.wide:
        coset_certificate(verifier)
    if arguments.full:
        library, groups = build(verifier, arguments.wide)
        selected, value_columns = certificate(verifier, library, groups)
        randomize(verifier, library, groups, selected, value_columns)
    positions = [reordered_index(pair("count", 0, index)[0]) for index in DENSE_FIXED]
    if arguments.wide:
        positions += [reordered_index(pair("wide", 0, index)[0]) for index in DENSE_FIXED]
    subprocess.run(
        [
            "cargo",
            "run",
            "--release",
            "-p",
            "lean_vm",
            "--example",
            "zk_flock_pair_opening_audit",
            "--",
            "--child-coset-certificate" if arguments.wide else "--child-kernel-certificate",
        ],
        input=" ".join(map(str, positions)),
        text=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
