"""Valid fixed-multiset JUMP padding and its eleven-column masking certificate."""

import argparse
from collections import Counter
from fractions import Fraction
from random import Random

from zk_frame_audit import jump_row
from zk_jump_audit import complete_bank_layout
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

SPARSE = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
TAGS = (14, 18, 20, 22, 30, 34, 36, 38)
PENULTIMATE_TAGS = (20, 36, 68, 132, 136, 140, 144, 148)
PROGRAM = ("pc", "o_c", "o_d", "o_f", "v_pc")
FRAMES = ("fp", "v_fp")
COUNTS = ("cnt_c", "cnt_d", "cnt_f", "cnt_bc")


def padding(verifier, branch=None, include_counts=True):
    tags = TAGS if branch is None else tuple(tag + branch for tag in PENULTIMATE_TAGS)
    if not include_counts:
        tags = tags[:7]
    return_tags = (29, 45) if branch is None else (152 + 2 * branch, 153 + 2 * branch)
    stride, code_shift, frame_shift = (1, 0, 0) if branch is None else (2, 512 * branch, 4000000 * branch)
    rows, pairs = {}, [[] for _ in tags]
    returns = iter(tag + 256 * index for tag in return_tags for index in range(4096))
    for bank, tag in enumerate(tags):
        first, second, third = (verifier.GEN ** (code_shift + 256 + 4 * bank + j) for j in range(3))
        for index in range(4096) if bank == 7 else SPARSE:
            frame_a, frame_b, frame_c = (verifier.GEN ** (frame_shift + 1000000 + 200000 * bank + 32 * index + j) for j in (0, 8, 16))
            row = lambda pc, frame, offsets, dest, dest_frame: jump_row(verifier, pc, frame, offsets, dest, dest_frame)
            if bank < 4:
                offsets = [0, 1, 2]
                if bank:
                    offsets[bank - 1] = 6
                selected = [row(first, frame_a, (0, 1, 2), third, frame_a), row(second, frame_b, offsets, third, frame_b)]
                extra = [row(third, frame_a, (3, 4, 5), first, frame_a), row(third, frame_b, (3, 4, 5), second, frame_b)]
            elif bank == 4:
                selected = [row(first, frame_a, (0, 1, 2), second, frame_a), row(first, frame_b, (0, 1, 2), third, frame_b)]
                extra = [row(second, frame_a, (3, 4, 5), first, frame_a), row(third, frame_b, (3, 4, 5), first, frame_b)]
            elif bank == 5:
                selected = [row(first, frame_a, (0, 1, 2), first, frame_b), row(first, frame_b, (0, 1, 2), first, frame_a)]
                extra = []
            elif bank == 6:
                selected = [row(first, frame_a, (0, 1, 2), first, frame_b), row(first, frame_b, (0, 1, 2), first, frame_c)]
                extra = [row(first, frame_c, (0, 1, 2), first, frame_a)]
            else:
                selected = [row(first, frame_a, (0, 1, 2), first, frame_a) for _ in range(2)]
                extra = []
            left, right = tag + 256 * index, tag + stride + 256 * index
            rows[left], rows[right] = selected
            pairs[bank].append((index, left, right))
            for item in extra:
                rows[next(returns)] = item
    assert len(rows) == (19392 if include_counts else 11200)
    columns = verifier.JUMP_COLUMNS
    memories, bytecodes = {}, {}

    def read(image, address, values):
        address = int(address)
        values = tuple(map(int, values))
        previous, count = image.get(address, (values, verifier.ONE))
        assert previous == values
        image[address] = values, count * verifier.GEN
        return count

    for item in rows.values():
        get = lambda name, item=item: item[columns.index(name)]
        for operand, value, count in zip(("o_c", "o_d", "o_f"), ("v_cond", "v_pc", "v_fp"), COUNTS):
            item[columns.index(count)] = read(memories, get("fp") * get(operand), (get(value), verifier.ZERO, verifier.ZERO))
        item[columns.index("cnt_bc")] = read(
            bytecodes, get("pc"), (verifier.GEN**verifier.OP_JUMP, *(get(name) for name in ("o_c", "o_d", "o_f")), verifier.ZERO, verifier.ZERO)
        )
    field = Tower(64, verifier)
    planes, _, _ = complete_bank_layout(field, 12, 8)
    old_extra = {tag + 256 * index for tag in (6, 7, 10, 11) for index in SPARSE} | {12 + 256 * index for index in range(1792)}
    assert not any(index % 256 in planes or index in old_extra for index in rows)
    return rows, pairs, memories, bytecodes


def check_bus(verifier, rows, memories, bytecodes):
    table = verifier.TABLES[verifier.OP_JUMP]
    pushes, pulls = Counter(), Counter()
    for item in rows.values():
        assert table.constraints(item) == (verifier.ZERO, verifier.ZERO)
        for counts, blocks in ((pushes, table.flushes.push), (pulls, table.flushes.pull)):
            counts.update(tuple(int(form.evaluate(item.__getitem__)) for form in block) for block in blocks)
    for separator, image in ((verifier.SEP_MEM, memories), (verifier.SEP_BYTECODE, bytecodes)):
        for address, (values, final) in image.items():
            pushes[(int(separator), address, 1, *values)] += 1
            pulls[(int(separator), address, int(final), *values)] += 1
    assert pushes == pulls


def certificates(verifier, rows, pairs, branch=None):
    field, rng = Tower(64, verifier), Random(103)
    point = [field.random(rng) for _ in range(20)]
    selector_start = 1 if branch is None else 2
    high, selectors = field.eq(point[8:]), field.eq(point[selector_start:8])
    columns = verifier.JUMP_COLUMNS
    program_vectors, frame_vectors, directions = [], [], []
    for bank, positions in enumerate(pairs[:7]):
        names = PROGRAM if bank < 5 else FRAMES
        normalized = []
        for index, left, right in positions:
            difference = [int(rows[left][columns.index(name)] + rows[right][columns.index(name)]) for name in names]
            scale = int(verifier.GEN ** (32 * index)) if bank >= 5 else 1
            normalized.append([field.kmul(value, field.kinv(scale)) for value in difference])
            assert (left ^ right) == 1 << (selector_start - 1)
            if branch is not None:
                assert left % 2 == right % 2 == branch
            coefficient = field.mul(selectors[(left % 256) >> selector_start], high[index])
            direction = [
                field.mul(coefficient, int(rows[left][columns.index(name)] + rows[right][columns.index(name)]))
                for name in (*PROGRAM, *FRAMES, *COUNTS)
            ]
            if bank >= 5:
                assert not any(direction[:5])
            directions.append(sum(value << (192 * column) for column, value in enumerate(direction)))
            if index == 0:
                weights = []
            weights.append(field.mul(coefficient, scale))
        assert all(vector == normalized[0] for vector in normalized)
        assert len(binary_basis(weights)) == 192
        (program_vectors if bank < 5 else frame_vectors).append(normalized[0])
    assert len(field.pivots(program_vectors)) == 5
    assert len(field.pivots(frame_vectors)) == 2
    for column, name in enumerate(COUNTS, 7):
        weights = []
        for index, left, right in pairs[7]:
            if index not in SPARSE:
                continue
            difference = rows[left][columns.index(name)] + rows[right][columns.index(name)]
            expected = verifier.GEN ** (2 * index) * (verifier.ONE + verifier.GEN) if name == "cnt_bc" else verifier.ONE + verifier.GEN
            assert difference == expected
            weights.append(field.mul(field.mul(selectors[(left % 256) >> selector_start], high[index]), int(difference)))
            directions.append(weights[-1] << (192 * column))
        assert len(binary_basis(weights)) == 192
    assert len(binary_basis(directions)) == 11 * 192
    print("Metadata map: joint binary rank 2112; diagonal ranks 5 and 2 over the base field and 192 for every scalar bank", flush=True)
    return directions


def randomize(verifier, rows, pairs):
    rng = Random(104)
    randomized = {index: item[:] for index, item in rows.items()}
    for bank in pairs[:7]:
        for _, left, right in bank:
            if rng.getrandbits(1):
                randomized[left], randomized[right] = randomized[right], randomized[left]
    for index, left, right in pairs[7]:
        if index not in SPARSE:
            continue
        for name in COUNTS:
            if rng.getrandbits(1):
                column = verifier.JUMP_COLUMNS.index(name)
                randomized[left][column], randomized[right][column] = randomized[right][column], randomized[left][column]
    for index in rows:
        for name in ("v_cond", "w", "b"):
            column = verifier.JUMP_COLUMNS.index(name)
            assert randomized[index][column] == rows[index][column]
    for name in COUNTS:
        column = verifier.JUMP_COLUMNS.index(name)
        assert Counter(int(item[column]) for item in rows.values()) == Counter(int(item[column]) for item in randomized.values())
    return randomized


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert 3 * span + Fraction(98, size) < Fraction(1, 1 << 156)
    assert 4 * span + Fraction(371, size) < Fraction(1, 1 << 155)
    assert 4 * span + Fraction(369, size) < Fraction(1, 1 << 155)
    print(
        "Exact error bounds: eleven metadata terminals below 2^-156; joint isolated constraint view and all fourteen terminals below 2^-155",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--penultimate", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    combined, randomized, memory_image, code_image, directions = {}, {}, {}, {}, []
    for branch in (0, 1) if args.penultimate else (None,):
        rows, pairs, memories, bytecodes = padding(verifier, branch)
        for destination, source in ((combined, rows), (memory_image, memories), (code_image, bytecodes)):
            assert not destination.keys() & source.keys()
            destination.update(source)
        randomized.update(randomize(verifier, rows, pairs))
        directions.extend(value << (2112 * (branch or 0)) for value in certificates(verifier, rows, pairs, branch))
    check_bus(verifier, combined, memory_image, code_image)
    check_bus(verifier, randomized, memory_image, code_image)
    assert len(binary_basis(directions)) == 2112 * (2 if args.penultimate else 1)
    print(f"{len(combined)} additional rows: both bus multisets balance against unchanged memory and final counters; disjoint masks", flush=True)
    if args.penultimate:
        print("Penultimate metadata: joint binary rank 4224 for both eleven-column halves", flush=True)
    error_bound()
