"""Exact ISA count-root normalization with a fixed number of added JUMP rows."""

from math import isqrt

from zk_frame_audit import jump_row
from zk_metadata_audit import COUNTS, check_bus
from zk_pcs_audit import verifier_module


def four_squares_small(value):
    pairs = {}
    for first in range(isqrt(value) + 1):
        for second in range(isqrt(value - first * first) + 1):
            pairs[first * first + second * second] = first, second
    for total, pair in pairs.items():
        if value - total in pairs:
            return (*pair, *pairs[value - total])
    raise AssertionError("four-square representation missing")


def multiplicities(cap, exponent, center):
    assert 0 <= exponent <= cap <= 4 * center * center
    quotient, residue = divmod(cap - exponent, 4)
    squares = four_squares_small(quotient)
    assert sum(value * value for value in squares) == quotient
    repeats = [count for value in squares for count in (center + value, center - value)]
    assert min(repeats) >= 0 and sum(repeats) == 8 * center
    added = 4 * sum(count * (count - 1) // 2 for count in repeats) + residue
    assert exponent + added == 16 * center * (center - 1) + cap
    return repeats, residue, added


def normalizer_rows(verifier, repeats, residue):
    rows, memories, code = {}, {}, {}
    g, columns = verifier.GEN, verifier.JUMP_COLUMNS
    read_numbers = {}

    def register(pc, frame, offsets):
        row = jump_row(verifier, pc, frame, offsets, pc, frame)
        opcode = (int(g**verifier.OP_JUMP), *(int(g**offset) for offset in offsets), 0, 0)
        assert int(pc) not in code
        code[int(pc)] = opcode, verifier.ONE
        for offset, value in zip(offsets, (verifier.ONE, pc, frame)):
            address = int(frame * g**offset)
            image = (int(value), 0, 0)
            if address in memories:
                assert memories[address] == (image, verifier.ONE)
            else:
                memories[address] = image, verifier.ONE
        return row

    def append(template):
        row = template[:]
        get = lambda name: row[columns.index(name)]
        for operand, name in zip(("o_c", "o_d", "o_f"), COUNTS):
            address = int(get("fp") * get(operand))
            image, count = memories[address]
            row[columns.index(name)] = count
            memories[address] = image, count * g
            read_numbers[("memory", address)] = read_numbers.get(("memory", address), 0) + 1
        address = int(get("pc"))
        image, count = code[address]
        row[columns.index("cnt_bc")] = count
        code[address] = image, count * g
        read_numbers[("code", address)] = read_numbers.get(("code", address), 0) + 1
        rows[len(rows)] = row

    heavy = [register(g ** (2048 + 4 * index), g ** (100000 + 8 * index), (0, 1, 2)) for index in range(8)]
    units = []
    for slot in range(3):
        alias_pc, neutral_pc = g ** (2100 + 4 * slot), g ** (2101 + 4 * slot)
        alias = register(alias_pc, alias_pc, (200000, 200001, 200001))
        neutral = register(neutral_pc, g ** (300000 + 8 * slot), (0, 1, 2))
        units.append((neutral, alias))
    assert len(memories) == 39 and len(code) == 14
    for template, count in zip(heavy, repeats):
        for _ in range(count):
            append(template)
    for slot, alternatives in enumerate(units):
        append(alternatives[int(slot < residue)])
    check_bus(verifier, rows, memories, code)
    exponent = sum(count * (count - 1) // 2 for count in read_numbers.values())
    root = verifier.ONE
    for row in rows.values():
        for name in COUNTS:
            root *= row[columns.index(name)]
    assert root == g**exponent
    return rows, memories, code, exponent, root


def power_two_layout(base_jump, other_reads):
    base_jump += (5 - base_jump) % 8
    read_bound = 4 * base_jump + other_reads
    cap = read_bound * (read_bound - 1) // 2
    minimum = isqrt(cap // 4)
    while 4 * minimum * minimum < cap:
        minimum += 1
    height = (base_jump + 8 * minimum + 2).bit_length()
    size = 1 << height
    center, remainder = divmod(size - base_jump - 3, 8)
    assert not remainder and center >= minimum
    assert base_jump + 8 * center + 3 == size and cap <= 4 * center * center
    return size, center, cap


if __name__ == "__main__":
    verifier = verifier_module()
    cap, center = 1024, 16
    for exponent in range(cap + 1):
        multiplicities(cap, exponent, center)
    memory_image = code_image = None
    for exponent in (*range(8), 127, 128, 511, 512, 1021, 1022, 1023, 1024):
        repeats, residue, added = multiplicities(cap, exponent, center)
        rows, memories, code, actual, root = normalizer_rows(verifier, repeats, residue)
        assert len(rows) == 8 * center + 3 and actual == added
        assert verifier.GEN**exponent * root == verifier.GEN ** (16 * center * (center - 1) + cap)
        images = ({address: values for address, (values, _) in memories.items()}, {address: values for address, (values, _) in code.items()})
        if memory_image is not None:
            assert images == (memory_image, code_image)
        memory_image, code_image = images
    print(
        "Count-root normalizer: every deficit through 1024 has fixed padding length; sixteen ISA cases balance and reach one public root with identical memory images",
        flush=True,
    )
    for base, other in ((0, 0), (64, 90), (1 << 16, 1 << 18), (1 << 20, 1 << 22)):
        power_two_layout(base, other)
    print(
        "Power-of-two scheduling: public base length and read bounds determine a fitting public repetition center; no witness-dependent size announcement",
        flush=True,
    )
