"""Metadata-column obstruction and a joint metadata/endpoint repair certificate."""

from fractions import Fraction
from random import Random

from zk_column_count_audit import Library
from zk_flock_coset_audit import library_messages, reordered_index
from zk_flock_skip_audit import check_rows, witness
from zk_pcs_audit import RightInverse, Tower, edot, verifier_module
from zk_three_point_audit import THREE_POINT_SUPPORT, three_point_error


def packed_words(triple):
    return [(triple[0] >> (64 * slot)) & ((1 << 64) - 1) for slot in range(256)]


def valid_cycles(verifier, triples):
    library = Library(verifier)
    library.pc = 1024
    block = library.block(verifier.OP_BLAKE2S)
    for index, triple in enumerate(triples):
        templates = library.templates(block, verifier.GEN ** (1280 + 32 * index))
        for name, offset in zip(("o_c", "o_d", "o_f"), (16, 17, 18)):
            templates[-1][1][verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
        words = packed_words(triple)
        for slot, name in enumerate(verifier.BLAKE2S_SLOTS):
            if name:
                templates[0][1][verifier.BLAKE2S_COLUMNS.index(name)] = verifier.E(words[slot])
        library.append(templates)
    library.verify()
    return library


def obstruction(verifier):
    field = Tower(64, verifier)
    baseline = witness(verifier, [0] * 16)
    pinned = packed_words(baseline)
    coefficient = pinned[1]
    assert coefficient

    def test(words):
        return field.kmul(pinned[1], words[0]) ^ field.kmul(pinned[0], words[1])

    for message in library_messages():
        assert test(packed_words(witness(verifier, message))) == 0
    zero = witness(verifier, [0] * 16, cv=[0] * 8, counter=0, flags=(0, 0))
    assert test(packed_words(zero)) == 0
    cv = list(verifier.BLAKE2S_IV)
    cv[0] ^= 0x01010021
    private = witness(verifier, [0] * 16, cv=cv)
    for triple in (baseline, zero, private):
        check_rows(verifier, triple)
    assert test(packed_words(private)) == coefficient
    first, second = (valid_cycles(verifier, [triple, baseline, zero]) for triple in (baseline, private))
    assert first.images["code"] == second.images["code"]
    assert first.reads == second.reads and first.exponents == second.exponents

    rng = Random(409)
    for _ in range(8):
        real = rng.sample(range(32), 8)
        columns = [[pinned[limb] if index % 2 else 0 for index in range(32)] for limb in range(2)]
        for index in real:
            for limb in range(2):
                columns[limb][index] = pinned[limb]
        weights = field.eq([field.random(rng) for _ in range(5)])
        before = field.mul(pinned[1], edot(field, weights, columns[0])) ^ field.mul(pinned[0], edot(field, weights, columns[1]))
        assert before == 0
        for index in real:
            columns[0][index] ^= 1
        after = field.mul(pinned[1], edot(field, weights, columns[0])) ^ field.mul(pinned[0], edot(field, weights, columns[1]))
        assert after == field.mul(coefficient, edot(field, [weights[index] for index in real], [1] * len(real)))
    assert (1 - Fraction(18, 1 << 192)) / 2 > Fraction(1, 2) - Fraction(1, 1 << 188)
    print("All 128 pinned profiles and zero-CV fillers obey the same disclosed-column invariant; a valid private CV change violates it.", flush=True)


def metadata_bank(verifier):
    field, rng = Tower(64, verifier), Random(419)
    logical = [768 + offset for offset in range(5)]
    assert all((index >> 7).bit_count() == 2 for index in logical)
    assert all(index not in THREE_POINT_SUPPORT for index in logical)
    physical = [reordered_index(index) for index in logical]
    assert physical == list(range(48, 53))
    point = [field.random(rng) for _ in range(18)]
    weights = []
    for index in physical:
        weight = 1
        for bit, coin in enumerate(point):
            weight = field.mul(weight, coin if index >> bit & 1 else 1 ^ coin)
        weights.append(weight)
    inverse = RightInverse(field, [[field.coords(weight)[limb] for weight in weights] for limb in range(3)])
    metadata = [[rng.getrandbits(64) for _ in range(6)] for _ in weights]
    shifts = [field.random(rng) for _ in range(6)]
    before = [edot(field, weights, [row[column] for row in metadata]) for column in range(6)]
    for column, shift in enumerate(shifts):
        for row, change in zip(metadata, inverse.solve(field.coords(shift))):
            row[column] ^= change
    after = [edot(field, weights, [row[column] for row in metadata]) for column in range(6)]
    assert after == [value ^ shift for value, shift in zip(before, shifts)]
    triples = []
    for row in metadata:
        cv = [word >> shift & ((1 << 32) - 1) for word in row[:4] for shift in (0, 32)]
        flags = tuple(row[5] >> shift & ((1 << 32) - 1) for shift in (0, 32))
        triple = witness(verifier, [rng.getrandbits(32) for _ in range(16)], cv=cv, counter=row[4], flags=flags)
        check_rows(verifier, triple)
        words = packed_words(triple)
        assert [words[slot] for slot in (0, 1, 2, 3, 18, 19)] == row
        triples.append(triple)
    valid_cycles(verifier, triples)
    padding_rows = 96 * 2048
    payload = 3 * ((1 << 22) - 1280)
    assert 32 * padding_rows == 6291456 < payload
    assert padding_rows // 8 == 24576 and (payload - 32 * padding_rows) // 256 == 24561
    assert three_point_error() + Fraction(2205 + 1918 + 42 + 1 + 21, 1 << 192) < Fraction(1, 1 << 158)
    print("Five disjoint general-compression rows give a surjective native metadata map; their translations remain valid closed cycles.", flush=True)
    print("Joint endpoint/all-eighteen-value-claims ledger remains below 2^-158; non-value columns and middle rounds are excluded.", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    obstruction(verifier)
    metadata_bank(verifier)
