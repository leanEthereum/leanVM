"""Exact certificates for marginal hiding of the shared bus product root."""

from fractions import Fraction
from random import Random

from zk_jump_audit import einv
from zk_pcs_audit import Tower, verifier_module


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    low_rank = Fraction(base**2, (size - 2) ** 2)
    mixing = Fraction(1 << 95) * Fraction(1 << 96, base**2 - 1) ** 8
    bound = Fraction((1 << 40) + 16, size) + low_rank + mixing
    assert mixing < Fraction(1, 1 << 160)
    assert bound < Fraction(1, 1 << 151)
    print("Eight-word bus-root bound: exact rational upper bound below 2^-151 for at most 2^40 other factors", flush=True)


def normalized_rank_check():
    field, base, size = Tower(2), 4, 64
    inverse = [0] + [einv(field, value) for value in range(1, size)]
    bad = 0
    for t0 in range(2, size):
        for t1 in range(2, size):
            for t2 in range(2, size):
                first = field.mul(t0, field.mul(t1, inverse[t2]))
                rank_one = t0 < base and first < base
                bad += rank_one
                if t0 < base:
                    assert (len(field.pivots(field.expand([[first, 1, t0]]))) < 2) == rank_one
    assert Fraction(bad, (size - 2) ** 3) <= Fraction(base**2, (size - 2) ** 2)
    print("Memory-fingerprint rank: exhaustive normalized GF(4)/GF(64) check matches the rank-one criterion", flush=True)


def multiplicative_mixing():
    field, base, size = Tower(2), 4, 64
    space = list(range(base**2))
    for shifts in ([0] * 8, [16] * 8, [0, 16, 32, 48] * 2):
        counts, total = [0] * size, 1
        counts[1] = 1
        for shift in shifts:
            values = [shift ^ value for value in space if shift ^ value]
            next_counts = [0] * size
            for left, count in enumerate(counts):
                if count:
                    for right in values:
                        next_counts[field.mul(left, right)] += count
            counts, total = next_counts, total * len(values)
        distance = sum((abs(Fraction(counts[value], total) - Fraction(1, size - 1)) for value in range(1, size)), Fraction()) / 2
        bound_squared = Fraction(size - 2, 4) * Fraction(size, (base**2 - 1) ** 2) ** 8
        assert distance**2 <= bound_squared
    print("Multiplicative mixing: exact eight-factor coset convolutions satisfy the character-sum bound in GF(64)", flush=True)


def actual_fingerprint(verifier):
    field, rng = Tower(64, verifier), Random(61)
    ext = lambda value: verifier.E(*field.coords(value))
    alpha = [ext(field.random(rng)) for _ in range(verifier.BUS_BITS)]
    weights = verifier.eq_kernel(alpha)
    beta = ext(field.random(rng))
    coefficients = [int(weights[i]) for i in (3, 4, 5)]
    assert len(field.pivots(field.expand([coefficients]))) >= 2
    product = verifier.ONE
    for index in range(8):
        words = [rng.getrandbits(64) for _ in range(3)]
        address = verifier.GEN ** (index + 2)
        seed = (verifier.SEP_MEM, address, verifier.ONE, *(verifier.E(word) for word in words))
        leaf = beta + verifier.dot(weights[:6], seed)
        affine = beta + verifier.dot(weights[:3], seed[:3]) + verifier.dot(weights[3:6], seed[3:])
        assert leaf == affine
        product *= leaf
    assert product != verifier.ZERO
    print("Actual fingerprint: eight unused seed/finalization factors use exactly slots 3, 4, 5 of eq(alpha)", flush=True)


if __name__ == "__main__":
    concrete_bound()
    normalized_rank_check()
    multiplicative_mixing()
    actual_fingerprint(verifier_module())
