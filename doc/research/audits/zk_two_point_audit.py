"""Two-point binary-span bound and actual-field certificates for padding swaps."""

from fractions import Fraction
from random import Random

from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

SPARSE_TWO = list(range(64)) + [i | (1 << j) for j in range(6, 14) for i in range(64)]


def error_bounds():
    size = 1 << 192
    first_five = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())

    def power(exponent):
        return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)

    def average(ambient):
        bound = min(Fraction(1), power(ambient + 1 - 9 * 64))
        for dimension in range(32, 64):
            probability = Fraction(((1 << 32) - 1) ** 2, (size - 1) * ((1 << (64 - dimension)) - 1))
            bound += probability * min(Fraction(1), power(ambient + 1 - 9 * dimension))
        return bound

    core = 2 * first_five + 2 * average(192) + average(384)
    unweighted = core + Fraction(28, size) + Fraction(56, size - 1)
    weighted = unweighted + Fraction(56, size)
    assert (Fraction(size, size - 1) ** 16) < 2
    assert core < unweighted < weighted < Fraction(1, 1 << 148)
    return core, unweighted, weighted


def certificate(verifier):
    field, rng = Tower(64, verifier), Random(123)
    weights = [field.eq([field.random(rng) for _ in range(14)]) for _ in range(2)]
    assert len(SPARSE_TWO) == 576
    for exponent in (0, 2):
        vectors = []
        for index in SPARSE_TWO:
            scale = int(verifier.GEN ** (exponent * index))
            vectors.append(field.mul(scale, weights[0][index]) | (field.mul(scale, weights[1][index]) << 192))
        assert len(binary_basis(vectors)) == 384
    print("Two-point span: 576 Boolean coins give binary rank 384 at two actual-field points, with and without geometric counter weights", flush=True)


if __name__ == "__main__":
    error_bounds()
    print("Exact rational bound: ordinary and geometrically weighted two-point failure probabilities are below 2^-148", flush=True)
    certificate(verifier_module())
