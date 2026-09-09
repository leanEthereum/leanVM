"""Correlated SET payload products and their balance identities, excluding full GKR."""

from fractions import Fraction
from functools import reduce
from itertools import combinations, product
from operator import mul
from random import Random

from zk_bytecode_frontier_audit import BANKS, CODE_BASES
from zk_bytecode_public_library_audit import FRAME_BASE, set_library
from zk_column_count_audit import Library
from zk_gkr_first_packet_audit import fingerprint
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations, table_products

BITS = 3840


def small_field_degeneracies():
    f, base = Field(6, 0b1000011), 4
    multiply = lambda *values: reduce(lambda a, b: f.mul[a][b], values, 1)
    frobenius = [multiply(a, a, a, a) for a in range(f.size)]
    subfield = {a for a in range(f.size) if frobenius[a] == a}
    assert len(subfield) == base
    bad, total, samples = 0, (f.size - 2) ** 3, []
    for t0, t1, t2 in product(range(2, f.size), repeat=3):
        a, b = multiply(t1, f.inv[t0]), t1
        c, d = multiply(t2, f.inv[multiply(t0, t1)]), multiply(t2, f.inv[t1])
        pairs = (a, b), (c, d)
        fixed = [tuple(frobenius[x] for x in pair) == pair for pair in pairs]
        assert fixed == [t0 in subfield and t1 in subfield, t0 in subfield and multiply(t2, f.inv[t1]) in subfield]
        conjugates, current = [], pairs[1]
        for h in range(3):
            collision = pairs[0] == current
            assert collision == (t2 == multiply(t1, t1) if h == 0 else t0 in subfield and a == current[0])
            conjugates.append(collision)
            current = tuple(frobenius[x] for x in current)
        excluded = any((*fixed, *conjugates))
        bad += excluded
        if not excluded and len(samples) < 20:
            samples.append(pairs)
    bound = Fraction(1, f.size - 2) + Fraction(2 * base**2 + 2 * base, (f.size - 2) ** 2)
    assert Fraction(bad, total) <= bound
    rng = Random(175)
    for pairs in samples:
        shifts = [rng.sample(range(f.size), 3) for _ in pairs]
        root_samples = []
        for x, y in product(subfield, repeat=2):
            roots = [offset ^ multiply(a, x) ^ multiply(b, y) for (a, b), offsets in zip(pairs, shifts, strict=True) for offset in offsets]
            root_samples.append(roots)
        for i in range(6):
            assert sum(roots[i] in subfield for roots in root_samples) <= base
        for i, j in combinations(range(6), 2):
            for h in range(3):
                equal = 0
                for roots in root_samples:
                    value = roots[j]
                    for _ in range(h):
                        value = frobenius[value]
                    equal += roots[i] == value
                assert equal <= base
    print("Exhaustive GF(4)/GF(64) coefficient-degeneracy classification and affine root-collision bounds pass", flush=True)


def exponent_certificate():
    rows = ((-1, 1, 0, 0), (0, 1, 0, 0), (1, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 1), (0, 0, 1, 0))
    assert [rows[i] for i in (2, 1, 5, 3)] == [tuple(int(i == j) for j in range(4)) for i in range(4)]
    for modulus in (3, 7, 9):
        for exponents in product(range(modulus), repeat=4):
            image = tuple(sum(a * b for a, b in zip(row, exponents, strict=True)) % modulus for row in rows)
            assert any(image) == any(exponents)
    print("The six-root character map has an integer unit minor, including composite character orders", flush=True)


def actual_products(v):
    rng = Random(176)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    alpha, beta = [sample() for _ in range(4)], sample()
    e, t = v.eq_kernel(alpha), [x / (v.ONE + x) for x in alpha]
    code_pair = e[6] / e[5], e[7] / e[5]
    memory_pair = e[4] / e[3], e[5] / e[3]
    assert code_pair == (t[1] / t[0], t[1])
    assert memory_pair == (t[2] / (t[0] * t[1]), t[2] / t[1])
    q_base = 1 << 64
    assert all(tuple(x**q_base for x in pair) != pair for pair in (code_pair, memory_pair))
    assert all(code_pair != tuple(x ** (q_base**h) for x in memory_pair) for h in range(3))
    support = (0, 64)
    words = [[[[rng.getrandbits(64) for _ in range(3)] for _ in range(2)] for _ in support] for _ in range(BANKS)]

    def combine(bits):
        combined, locals_ = Library(v), []
        for bank in range(BANKS):
            local, _ = set_library(
                v,
                support,
                words[bank],
                bits[bank * len(support) : (bank + 1) * len(support)],
                code_base=CODE_BASES[bank],
                frame_base=FRAME_BASE + 8 * BITS * bank,
                compact=True,
            )
            for kind in combined.images:
                assert combined.images[kind].keys().isdisjoint(local.images[kind])
                combined.images[kind].update(local.images[kind])
            combined.append(local.rows)
            locals_.append(local)
        combined.verify()
        return combined, locals_

    def framework(library, kind, final):
        separator = v.SEP_BYTECODE if kind == "code" else v.SEP_MEM
        return reduce(
            mul,
            (
                fingerprint(v, e, beta, separator, address, v.GEN ** library.reads[kind, address] if final else v.ONE, payload)
                for address, payload in library.images[kind].items()
            ),
            v.ONE,
        )

    def word_coordinates(library, bank, index, alternative):
        pc = CODE_BASES[bank] + 4 * support[index] + 2 * alternative
        frame = FRAME_BASE + 8 * BITS * bank + 8 * index + 4 * alternative
        code = [fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN**pc), v.GEN**label, library.images["code"][int(v.GEN**pc)]) for label in range(3)]
        memory = [
            fingerprint(v, e, beta, v.SEP_MEM, int(v.GEN**frame), v.GEN**label, library.images["memory"][int(v.GEN**frame)]) for label in range(3)
        ]
        jump = [
            fingerprint(v, e, beta, v.SEP_BYTECODE, int(v.GEN ** (pc + 1)), v.GEN**label, library.images["code"][int(v.GEN ** (pc + 1))])
            for label in (0, 2)
        ]
        return code[2] / code[0] * jump[1] / jump[0], code[0] * code[1], memory[1] * memory[2], memory[0] * memory[1]

    vectors = [[0] * (BANKS * len(support))]
    vectors += [[int(i == selected) for i in range(len(vectors[0]))] for selected in range(len(vectors[0]))]
    vectors += [[1] * len(vectors[0]), [i % 2 for i in range(len(vectors[0]))]]
    baseline, initial = None, None
    for bits in vectors:
        library, locals_ = combine(bits)
        sets = [table_products(v, library, v.OP_SET, side, e, beta) for side in ("push", "pull")]
        jumps = [table_products(v, library, v.OP_JUMP, side, e, beta) for side in ("push", "pull")]
        bc_seed, mem_seed = framework(library, "code", False), framework(library, "memory", False)
        code_final = [framework(local, "code", True) for local in locals_]
        assert reduce(mul, code_final, v.ONE) == bc_seed * sets[0][1] / sets[1][1] * jumps[0][1] / jumps[1][1]
        memory_ratio = reduce(mul, jumps[0][2:], v.ONE) / reduce(mul, jumps[1][2:], v.ONE)
        assert framework(library, "memory", True) == mem_seed * sets[0][2] / sets[1][2] * memory_ratio
        per_bank = []
        for bank, local in enumerate(locals_):
            push, pull = [table_products(v, local, v.OP_SET, side, e, beta) for side in ("push", "pull")]
            per_bank.append((code_final[bank], pull[1], push[2], pull[2]))
        if baseline is None:
            baseline, initial = library, per_bank
        assert library.images == baseline.images and dict(library.exponents) == dict(baseline.exponents)
        expected = [list(row) for row in initial]
        for i, bit in enumerate(bits):
            if bit:
                bank, index = divmod(i, len(support))
                before, after = [word_coordinates(library, bank, index, alternative) for alternative in (0, 1)]
                expected[bank] = [x * y / z for x, y, z in zip(expected[bank], after, before, strict=True)]
        assert per_bank == [tuple(row) for row in expected]
    print("Actual four-bank cycles obey the six-factor ratio formulas and both exact framework/SET/JUMP balance identities", flush=True)


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    coefficient = Fraction(17 * (1 << 32) + 51, base - 6)
    bias = coefficient**2
    assert bias < Fraction(1, 1 << 55)
    group = (size - 1) ** 4
    term = (group - 1) * ((1 + bias) / 2) ** BITS
    assert term < Fraction(1, 4)
    assert 2 * size**12 * term < Fraction(1, 1 << 766)
    bad_coins = Fraction(8, size) + Fraction(1, size - 2) + Fraction(2 * base**2 + 2 * base, (size - 2) ** 2)
    zero_factors = Fraction((1 << 24) + 40 * BANKS * BITS, size)
    assert Fraction(1, 1 << 160) + bad_coins + zero_factors < Fraction(1, 1 << 159)
    assert Fraction(1, 1 << 383) / Fraction(1, 1 << 160) == Fraction(1, 1 << 223)
    print("Rational four-coordinate bounds: mean below 2^-383, setup exception below 2^-223 at threshold 2^-160", flush=True)
    print("With honest-coin/zero exclusions, decoupling is below 2^-159; controls and complementary cofactors still require simulation", flush=True)


if __name__ == "__main__":
    small_field_degeneracies()
    exponent_certificate()
    verifier = verifier_module()
    actual_products(verifier)
    reservations(verifier, BITS)
    concrete_bound()
