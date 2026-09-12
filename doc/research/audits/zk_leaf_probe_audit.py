"""Canonical leaf probe histograms and legal eight-address count completion."""

from collections import Counter

from zk_column_count_audit import Library, power_two_fill
from zk_pcs_audit import verifier_module


def maximal_pair_word(total, pair):
    states = {0: (0, ())}
    for _ in range(42):
        following = {}
        for subtotal, (score, word) in states.items():
            for digit in range(8):
                if subtotal + digit <= total:
                    candidate = score + int(digit in (pair, 7 - pair)), (*word, digit)
                    if subtotal + digit not in following or candidate[0] > following[subtotal + digit][0]:
                        following[subtotal + digit] = candidate
        states = following
    return states[total]


def public_prefix(verifier):
    return (verifier.E(17, 19, 0), verifier.E(29, 31, 0), *(verifier.ZERO for _ in range(6)))


def set_word(verifier, row, columns, prefix, value):
    for limb, word in enumerate((value.c0, value.c1, value.c2)):
        row[columns.index(f"{prefix}_{limb}")] = verifier.E(word)


def range_cycles(library, word):
    v, values = library.v, public_prefix(library.v)
    for digit in word:
        frame = library.fresh_frame()
        first = library.row(v.OP_DEREF, 4000, frame, pointer=v.GEN**digit)
        first[v.DEREF_COLUMNS.index("o2")] = v.ONE
        first[v.DEREF_COLUMNS.index("o3")] = v.GEN**3
        set_word(v, first, v.DEREF_COLUMNS, "v3", values[digit])
        multiply = library.row(v.OP_MUL, 4001, frame)
        for name, exponent in (("va", digit), ("vb", 7 - digit)):
            set_word(v, multiply, v.ARITH_COLUMNS, name, v.GEN**exponent)
        second = library.row(v.OP_DEREF, 4002, frame, pointer=v.GEN ** (7 - digit))
        for name, offset in (("o1", 1), ("o2", 0), ("o3", 4)):
            second[v.DEREF_COLUMNS.index(name)] = v.GEN**offset
        set_word(v, second, v.DEREF_COLUMNS, "v3", values[7 - digit])
        closing = library.row(v.OP_JUMP, 4003, frame, 4000)
        for name, offset in (("o_c", 5), ("o_d", 6), ("o_f", 7)):
            closing[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        library.append([(v.OP_DEREF, first), (v.OP_MUL, multiply), (v.OP_DEREF, second), (v.OP_JUMP, closing)])


def complete_digits(library, word, caps):
    v, values = library.v, public_prefix(library.v)
    histogram = Counter(address for digit in word for address in (digit, 7 - digit))
    assert sum(histogram.values()) == 84 and sum(caps) == 314
    added = 0
    for address, target in enumerate(caps):
        frame = library.fresh_frame()
        read = library.row(v.OP_DEREF, 4010, frame, pointer=v.GEN**address)
        read[v.DEREF_COLUMNS.index("o2")] = v.ONE
        read[v.DEREF_COLUMNS.index("o3")] = v.GEN
        set_word(v, read, v.DEREF_COLUMNS, "v3", values[address])
        closing = library.row(v.OP_JUMP, 4011, frame, 4010)
        for name, offset in (("o_c", 2), ("o_d", 3), ("o_f", 4)):
            closing[v.JUMP_COLUMNS.index(name)] = v.GEN**offset
        library.register([(v.OP_DEREF, read), (v.OP_JUMP, closing)])
        deficit = target - histogram[address]
        assert deficit >= 0
        for _ in range(deficit):
            library.append([(v.OP_DEREF, read), (v.OP_JUMP, closing)])
        added += deficit
    assert added == 230
    assert tuple(library.reads["memory", int(v.GEN**j)] for j in range(8)) == tuple(caps)


def main():
    verifier = verifier_module()
    for total, maxima in ((195, (41, 41, 42, 33)), (191, (41, 41, 41, 34))):
        caps = (*maxima, *maxima[::-1])
        roots = set()
        for pair in range(4):
            score, word = maximal_pair_word(total, pair)
            assert score == maxima[pair] and len(word) == 42 and sum(word) == total
            library = Library(verifier)
            range_cycles(library, word)
            complete_digits(library, word, caps)
            for opcode in (verifier.OP_XOR, verifier.OP_SET, verifier.OP_BLAKE2S):
                template = library.templates(library.block(opcode), library.fresh_frame())
                for _ in range(8 if opcode == verifier.OP_BLAKE2S else 1):
                    library.append(template)
            power_two_fill(library)
            library.verify()
            assert tuple(library.reads["memory", int(verifier.GEN**j)] for j in range(8)) == caps
            assert tuple(sum(opcode == table.opcode for opcode, _ in library.rows) for table in verifier.TABLES) == (1, 64, 1, 512, 512, 8)
            roots.add(sum(library.exponents.values()))
            print(f"Target sum {total}, pair {pair}: exact maximum {score}, 230 valid top-ups, fixed protected counters {caps}.", flush=True)
        assert len(roots) > 1
        print(f"Target sum {total}: helper/table count roots still vary, so all-column normalization remains necessary.", flush=True)
    print("The eight-count completion is a probe/ISA certificate, not a valid signature preimage or a full joint ZK simulator.", flush=True)


if __name__ == "__main__":
    main()
