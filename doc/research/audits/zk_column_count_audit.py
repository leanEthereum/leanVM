"""Valid-cycle normalization of every count-column product, excluding internal GKR."""

import sys
from collections import Counter, defaultdict
from random import Random
from struct import pack, unpack

from zk_count_root_audit import four_squares_small
from zk_pcs_audit import verifier_module


class Library:
    def __init__(self, verifier):
        self.v = verifier
        self.rows = []
        self.images = {"memory": {}, "code": {}}
        self.reads = defaultdict(int)
        self.labels = {}
        self.exponents = defaultdict(int)
        self.pc = 4096
        self.frame = 1000000
        self.absorber = (verifier.OP_MUL, verifier.ARITH_COLUMNS.index("cnt_a"))

    def fresh_frame(self):
        result = self.v.GEN**self.frame
        self.frame += 128
        return result

    def row(self, opcode, pc, frame, destination=None, pointer=None):
        v, table = self.v, self.v.TABLES[opcode]
        values = {"pc": v.GEN**pc, "fp": frame}
        values.update({table.columns[column]: v.ONE for column in table.count_columns})
        if opcode in (v.OP_XOR, v.OP_MUL):
            values.update(o_a=v.ONE, o_b=v.GEN, o_c=v.GEN**2)
        elif opcode == v.OP_SET:
            values.update(o=v.ONE)
        elif opcode == v.OP_DEREF:
            values.update(
                o1=v.ONE,
                o2=v.GEN,
                o3=v.GEN**2,
                ptr=frame if pointer is None else pointer,
            )
        elif opcode == v.OP_JUMP:
            values.update(
                o_c=v.ONE,
                o_d=v.GEN,
                o_f=v.GEN**2,
                v_cond=v.ONE,
                v_pc=v.GEN**destination,
                v_fp=frame,
                w=v.ONE,
                b=v.ONE,
            )
        else:
            assert opcode == v.OP_BLAKE2S
            values.update({f"o_{index}": v.GEN**index for index in range(4)})
            values.update(o_v=v.GEN**8, o_out=v.GEN**10, o_md=v.GEN**12)
            iv = list(v.BLAKE2S_IV)
            iv[0] ^= 0x01010020
            chaining = pack("<8I", *iv)
            digest = v.blake2s_hash(bytes(64)).value
            for name, data in (
                ("cv0", chaining[:16]),
                ("cv1", chaining[16:]),
                ("out0", digest[:16]),
                ("out1", digest[16:]),
            ):
                low, high = unpack("<2Q", data)
                values[f"{name}_lo"], values[f"{name}_hi"] = v.E(low), v.E(high)
            values.update(md_lo=v.E(64), md_hi=v.E(0xFFFFFFFF))
        return [values.get(name, v.ZERO) for name in table.columns]

    def memory_reads(self, opcode, row):
        for block in self.v.TABLES[opcode].flushes.pull:
            if block[0].evaluate(row.__getitem__) != self.v.SEP_MEM:
                continue
            ((column,),) = block[2].terms
            assert block[2].terms[(column,)] == self.v.ONE
            values = tuple(form.evaluate(row.__getitem__) for form in block)
            yield column, values[1], values[3:]

    def block(self, opcode, adapters=False):
        sample = self.row(opcode, self.pc, self.v.ONE, self.pc + 1)
        selected = [column for column, _, _ in self.memory_reads(opcode, sample) if (opcode, column) != self.absorber] if adapters else []
        closes = opcode != self.v.OP_JUMP or bool(selected)
        result = opcode, self.pc, selected, closes
        self.pc += 1 + len(selected) + int(closes) + 1
        return result

    def templates(self, block, frame, pointer=None):
        v = self.v
        opcode, pc, selected, closes = block
        target = self.row(opcode, pc, frame, pc + 1 if selected or closes else pc, pointer)
        result = [(opcode, target)]
        reads = {column: (address, values) for column, address, values in self.memory_reads(opcode, target)}
        for index, column in enumerate(selected):
            row = self.row(v.OP_MUL, pc + index + 1, frame)
            names = v.ARITH_COLUMNS
            address, values = reads[column]
            row[names.index("o_a")] = address / frame
            row[names.index("o_b")] = v.GEN ** (32 + 2 * index)
            row[names.index("o_c")] = v.GEN ** (33 + 2 * index)
            for lane, value in enumerate(values):
                row[names.index(f"va_{lane}")] = value
            result.append((v.OP_MUL, row))
        if closes:
            row = self.row(v.OP_JUMP, pc + len(selected) + 1, frame, pc)
            for name, offset in zip(("o_c", "o_d", "o_f"), (64, 65, 66)):
                row[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
            result.append((v.OP_JUMP, row))
        return result

    def register(self, templates):
        for opcode, row in templates:
            for block in self.v.TABLES[opcode].flushes.pull:
                values = tuple(int(form.evaluate(row.__getitem__)) for form in block)
                if values[0] == int(self.v.SEP_STATE):
                    continue
                kind = "memory" if values[0] == int(self.v.SEP_MEM) else "code"
                previous = self.images[kind].setdefault(values[1], values[3:])
                assert previous == values[3:]

    def append(self, templates):
        self.register(templates)
        result = []
        for opcode, template in templates:
            row, row_id = template[:], len(self.rows)
            for block in self.v.TABLES[opcode].flushes.pull:
                values = tuple(int(form.evaluate(row.__getitem__)) for form in block)
                if values[0] == int(self.v.SEP_STATE):
                    continue
                kind = "memory" if values[0] == int(self.v.SEP_MEM) else "code"
                ((column,),) = block[2].terms
                address = kind, values[1]
                label = self.reads[address]
                row[column] = self.v.GEN**label
                self.labels[row_id, column] = address, label
                self.reads[address] += 1
                self.exponents[opcode, column] += label
            self.rows.append((opcode, row))
            result.append(row_id)
        return result

    def set_labels(self, locations, labels):
        for location, label in zip(locations, labels, strict=True):
            row_id, column = location
            address, previous = self.labels[location]
            opcode, row = self.rows[row_id]
            row[column] = self.v.GEN**label
            self.exponents[opcode, column] += label - previous
            self.labels[location] = address, label

    def route(self, target, receiver, shift):
        size = len(target)
        total = size + len(receiver)
        assert size > 0 and receiver and 0 <= shift <= size * len(receiver)
        addresses = {self.labels[location][0] for location in (*target, *receiver)}
        assert len(addresses) == 1 and self.reads[next(iter(addresses))] == total
        quotient, remainder = divmod(shift, size)
        selected = [quotient + index + int(index >= size - remainder) for index in range(size)]
        complement = [index for index in range(total) if index not in selected]
        assert sum(selected) == size * (size - 1) // 2 + shift
        assert sorted(selected + complement) == list(range(total))
        self.set_labels(target, selected)
        self.set_labels(receiver, complement)

    def memory_exponents(self):
        return {
            (table.opcode, column): self.exponents[table.opcode, column]
            for table in self.v.TABLES
            for column in table.count_columns
            if table.columns[column] != "cnt_bc"
        }

    def verify(self):
        v, pushes, pulls = self.v, Counter(), Counter()
        for opcode, row in self.rows:
            table = v.TABLES[opcode]
            assert all(value == v.ZERO for value in table.constraints(row))
            for counter, blocks in (
                (pushes, table.flushes.push),
                (pulls, table.flushes.pull),
            ):
                counter.update(tuple(int(form.evaluate(row.__getitem__)) for form in block) for block in blocks)
        for kind, separator in (("memory", v.SEP_MEM), ("code", v.SEP_BYTECODE)):
            for address, values in self.images[kind].items():
                pushes[(int(separator), address, 1, *values)] += 1
                pulls[
                    (
                        int(separator),
                        address,
                        int(v.GEN ** self.reads[kind, address]),
                        *values,
                    )
                ] += 1
        assert pushes == pulls
        grouped = defaultdict(list)
        for address, label in self.labels.values():
            grouped[address].append(label)
        assert all(sorted(labels) == list(range(self.reads[address])) for address, labels in grouped.items())
        for table in v.TABLES:
            for column in table.count_columns:
                root = v.ONE
                for opcode, row in self.rows:
                    if opcode == table.opcode:
                        root *= row[column]
                assert root == v.GEN ** self.exponents[table.opcode, column]


def repeats(cap, value, center, scale=1):
    quotient, residue = divmod(cap - value, scale)
    squares = four_squares_small(quotient)
    assert max(squares) <= center
    return [count for square in squares for count in (center + square, center - square)], residue


def base_trace(library, multiplicities, scatter=False):
    for opcode, repeated in enumerate(multiplicities):
        block = library.block(opcode)
        main = library.templates(block, library.fresh_frame())
        alternate = library.templates(block, library.fresh_frame())
        fillers = [library.templates(library.block(opcode), library.fresh_frame()) for _ in range(3)]
        for template in (main, alternate, *fillers):
            library.register(template)
        for index in range(repeated):
            library.append(alternate if scatter and index % 2 else main)
        for template in fillers[: 3 - repeated]:
            library.append(template)


def normalize_bytecode(library, opcode, cap, center, reuse_frames=False):
    v = library.v
    column = v.TABLES[opcode].columns.index("cnt_bc")
    counts, residue = repeats(cap, library.exponents[opcode, column], center)
    assert not residue
    before_memory = library.memory_exponents()
    before_code = library.exponents[opcode, column]
    for count in counts:
        block = library.block(opcode)
        candidates = [library.templates(block, library.fresh_frame()) for _ in range(1 if reuse_frames else 2 * center)]
        for template in candidates:
            library.register(template)
        for template in candidates * count if reuse_frames else candidates[:count]:
            library.append(template)
    assert library.exponents[opcode, column] == 4 * center * (center - 1) + cap
    increment = 4 * center * (center - 1) + cap - before_code
    for (source, target), value in library.memory_exponents().items():
        expected = increment if reuse_frames and source in (opcode, v.OP_JUMP) else 0
        assert value - before_memory[source, target] == expected


def router_banks(library, size, opcodes=range(6)):
    opcodes = tuple(opcodes)
    banks = []
    for opcode in opcodes:
        block = library.block(opcode, adapters=True)
        template = library.templates(block, library.fresh_frame())
        occurrences = [library.append(template) for _ in range(size)]
        for index, column in enumerate(block[2]):
            target = [(rows[0], column) for rows in occurrences]
            receiver = [(rows[index + 1], library.absorber[1]) for rows in occurrences]
            library.route(target, receiver, 0)
            banks.append(((opcode, column), target, receiver))
    assert len(banks) == sum(len(library.v.TABLES[opcode].count_columns) - 1 - int(opcode == library.absorber[0]) for opcode in opcodes)
    return banks


def normalize_memory(library, uncertain, cap=111, center=7):
    v = library.v
    counts, residue = repeats(cap, uncertain, center, 3)
    block = library.block(v.OP_JUMP)
    before = library.memory_exponents()
    for count in counts:
        template = library.templates(block, library.fresh_frame())
        library.register(template)
        for _ in range(count):
            library.append(template)
    for slot in range(2):
        block = library.block(v.OP_DEREF)
        alias, neutral = library.fresh_frame(), library.fresh_frame()
        alternatives = (
            library.templates(block, neutral, neutral * v.GEN**3),
            library.templates(block, alias, alias * v.GEN),
        )
        for template in alternatives:
            library.register(template)
        library.append(alternatives[int(slot < residue)])
    difference = sum(library.memory_exponents().values()) - sum(before.values())
    assert uncertain + difference == 12 * center * (center - 1) + cap


def power_two_fill(library, opcodes=None, reuse_frames=False):
    v = library.v
    if opcodes is None:
        opcodes = (v.OP_XOR, v.OP_MUL, v.OP_SET, v.OP_DEREF, v.OP_BLAKE2S, v.OP_JUMP)
    for opcode in opcodes:
        count = sum(source == opcode for source, _ in library.rows)
        target = 1 << (count - 1).bit_length()
        block = library.block(opcode)
        template = library.templates(block, library.fresh_frame()) if reuse_frames else None
        if template is not None:
            library.register(template)
        for _ in range(target - count):
            library.append(template if reuse_frames else library.templates(block, library.fresh_frame()))


def run(verifier, multiplicities, preserve_compression=False):
    library = Library(verifier)
    base_trace(library, multiplicities)
    active = tuple(table.opcode for table in verifier.TABLES if not preserve_compression or table.opcode != verifier.OP_BLAKE2S)
    if preserve_compression:
        assert multiplicities[verifier.OP_BLAKE2S] == 1
        block = library.block(verifier.OP_BLAKE2S)
        for _ in range(5):
            library.append(library.templates(block, library.fresh_frame()))
    preserved = [(opcode, row[:]) for opcode, row in library.rows if opcode not in active]
    original = library.memory_exponents()
    for opcode in (
        verifier.OP_XOR,
        verifier.OP_MUL,
        verifier.OP_SET,
        verifier.OP_DEREF,
        verifier.OP_BLAKE2S,
    ):
        if opcode in active:
            normalize_bytecode(library, opcode, 3, 2)
    normalize_bytecode(library, verifier.OP_JUMP, 73, 9)
    banks = router_banks(library, 8, active)
    baseline = {column: value - original[column] for column, value in library.memory_exponents().items()}
    normalize_memory(library, sum(original.values()))
    total = sum(library.memory_exponents().values())
    for (opcode, column), target, receiver in banks:
        constant = baseline[opcode, column] + (168 if opcode == verifier.OP_JUMP else 0)
        bound = (
            55 if opcode == verifier.OP_JUMP else 5 if opcode == verifier.OP_DEREF and verifier.TABLES[opcode].columns[column] == "cnt_local" else 3
        )
        shift = constant + bound - library.exponents[opcode, column]
        library.route(target, receiver, shift)
        assert library.exponents[opcode, column] == constant + bound
    assert sum(library.memory_exponents().values()) == total
    power_two_fill(
        library,
        (
            *[opcode for opcode in active if opcode != verifier.OP_JUMP],
            verifier.OP_JUMP,
        ),
    )
    library.verify()
    assert preserved == [(opcode, row) for opcode, row in library.rows if opcode not in active]
    counts = tuple(sum(opcode == table.opcode for opcode, _ in library.rows) for table in verifier.TABLES)
    assert all(count > 0 and count & (count - 1) == 0 for count in counts)
    roots = tuple(library.exponents[table.opcode, column] for table in verifier.TABLES for column in table.count_columns)
    images = tuple(library.images[kind] for kind in ("memory", "code"))
    return counts, roots, images


def prepare_reused(verifier, multiplicities, scatter):
    library = Library(verifier)
    assert multiplicities[verifier.OP_BLAKE2S] == 1
    base_trace(library, multiplicities, scatter)
    block = library.block(verifier.OP_BLAKE2S)
    for _ in range(5):
        library.append(library.templates(block, library.fresh_frame()))
    preserved = [row[:] for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    original = library.memory_exponents()
    initial_code = {table.opcode: library.exponents[table.opcode, table.columns.index("cnt_bc")] for table in verifier.TABLES}
    assert initial_code[verifier.OP_JUMP] <= 28
    active = tuple(opcode for opcode in range(6) if opcode != verifier.OP_BLAKE2S)
    frame_start = library.frame
    for opcode in active:
        cap, center = (73, 9) if opcode == verifier.OP_JUMP else (3, 2)
        normalize_bytecode(library, opcode, cap, center, reuse_frames=True)
    assert library.frame - frame_start == 40 * 128
    bounds = {}
    for (opcode, column), value in library.memory_exponents().items():
        if opcode == verifier.OP_BLAKE2S:
            assert value == original[opcode, column] == 0
            bounds[opcode, column] = 0, 0
            continue
        constant = 361 if opcode == verifier.OP_JUMP else 11
        assert value == original[opcode, column] + constant - initial_code[opcode]
        low, high = (333, 416) if opcode == verifier.OP_JUMP else (8, 14)
        assert low <= value <= high
        bounds[opcode, column] = low, high
    low_total = sum(low for low, _ in bounds.values())
    high_total = sum(high for _, high in bounds.values())
    assert (low_total, high_total) == (1079, 1388)
    before_routers = library.memory_exponents()
    banks = router_banks(library, 14, active)
    fixed_router = {column: value - before_routers[column] for column, value in library.memory_exponents().items()}
    uncertain = sum(before_routers.values()) - low_total
    normalize_memory(library, uncertain, cap=high_total - low_total, center=11)
    total = sum(library.memory_exponents().values())
    assert total == sum(fixed_router.values()) + low_total + 12 * 11 * 10 + 309
    for (opcode, column), target, receiver in banks:
        upper = bounds[opcode, column][1]
        if opcode == verifier.OP_JUMP:
            upper += 543
        elif opcode == verifier.OP_DEREF and verifier.TABLES[opcode].columns[column] == "cnt_local":
            upper += 2
        shift = fixed_router[opcode, column] + upper - library.exponents[opcode, column]
        assert 0 <= shift <= 186 < 14 * 14
        library.route(target, receiver, shift)
        assert library.exponents[opcode, column] == fixed_router[opcode, column] + upper
    assert sum(library.memory_exponents().values()) == total
    assert library.frame - frame_start == 57 * 128
    assert preserved == [row for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    return library, (tuple(initial_code.values()), tuple(original.values()))


def run_reused(verifier, multiplicities, scatter):
    library, before = prepare_reused(verifier, multiplicities, scatter)
    active = tuple(opcode for opcode in range(6) if opcode != verifier.OP_BLAKE2S)
    preserved = [row[:] for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    frame_start = library.frame
    power_two_fill(library, active, reuse_frames=True)
    assert library.frame - frame_start == 5 * 128
    library.verify()
    assert preserved == [row for opcode, row in library.rows if opcode == verifier.OP_BLAKE2S]
    counts = tuple(sum(opcode == table.opcode for opcode, _ in library.rows) for table in verifier.TABLES)
    roots = tuple(library.exponents[table.opcode, column] for table in verifier.TABLES for column in table.count_columns)
    images = tuple(library.images[kind] for kind in ("memory", "code"))
    return (counts, roots, images), before


if __name__ == "__main__":
    verifier, rng = verifier_module(), Random(127)
    expected = None
    cases = [
        (0,) * 6,
        (1,) * 6,
        (2,) * 6,
        (3,) * 6,
        *(tuple(rng.randrange(4) for _ in range(6)) for _ in range(4)),
    ]
    if sys.argv[1:] == ["--reuse-frames"]:
        for case in cases:
            case = (*case[: verifier.OP_BLAKE2S], 1)
            previous_input = None
            for scatter in (False, True):
                result, before = run_reused(verifier, case, scatter)
                if previous_input is not None:
                    assert before[0] == previous_input[0]
                    if max(case) >= 2:
                        assert before[1] != previous_input[1]
                previous_input = before
                if expected is not None:
                    assert result == expected
                expected = result
                print(
                    f"Reused-frame completion: base {case}, scatter={scatter}, fixed rows {result[0]}, all 28 products and images agree; 62 added frames, BLAKE2s unchanged",
                    flush=True,
                )
        sys.exit(0)
    assert not sys.argv[1:], "optional flag: --reuse-frames"
    for case in cases:
        result = run(verifier, case)
        if expected is not None:
            assert result == expected
        expected = result
        print(
            f"All-column normalization: base repetition choices {case}, fixed row counts {result[0]}, all 28 count products and full memory/code images agree",
            flush=True,
        )
    expected = None
    for case in cases:
        case = (*case[: verifier.OP_BLAKE2S], 1)
        result = run(verifier, case, preserve_compression=True)
        if expected is not None:
            assert result == expected
        expected = result
        print(
            f"Noncompression normalization: base choices {case}, fixed rows {result[0]}, all 28 products and images agree; BLAKE2s rows unchanged",
            flush=True,
        )
