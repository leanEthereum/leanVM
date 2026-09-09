"""Two-point binary-span bound and actual-field certificates for padding swaps."""

from fractions import Fraction
from functools import cache
from random import Random

from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

SPARSE_TWO = list(range(64)) + [i | (1 << j) for j in range(6, 14) for i in range(64)]
COMPACT_TWO = list(range(128)) + [i | (1 << j) for j in range(7, 11) for i in range(128)]
SPARSE_FIXED = [index for index in SPARSE_TWO if index < 1 << 12]
DENSE_FIXED = list(range(256)) + [low | (1 << bit) for bit in range(8, 12) for low in range(256)]


@cache
def dense_fixed_error(observed_bits=256):
    assert 0 <= observed_bits <= 384
    size = 1 << 192

    @cache
    def tail(before, after):
        return min(Fraction(1), Fraction(((1 << before) - 1) ** 2, (size - 1) * ((1 << (2 * before - after)) - 1)))

    @cache
    def remaining(steps, dimension):
        if steps == 0:
            return min(Fraction(1), Fraction(size, size - 1) ** 4 * Fraction(2) ** (192 + observed_bits - 5 * dimension))
        maximum = min(2 * dimension, 192)
        return min(
            Fraction(1),
            remaining(steps - 1, maximum)
            + sum((tail(dimension, after) * remaining(steps - 1, after) for after in range(dimension, maximum)), Fraction()),
        )

    first_five = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())
    error = first_five + remaining(3, 32) + Fraction(12, size)
    if observed_bits <= 320:
        assert error + Fraction(24, size) < Fraction(1, 1 << 160)
    return error


def fixed_observation_error(observed_bits=64):
    assert 0 <= observed_bits <= 192
    size = 1 << 192
    first_five = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())

    def remaining(dimension):
        return min(Fraction(1), Fraction(size, size - 1) ** 6 * Fraction(2) ** (192 + observed_bits - 7 * dimension))

    averaged = remaining(64)
    for dimension in range(32, 64):
        probability = Fraction(((1 << 32) - 1) ** 2, (size - 1) * ((1 << (64 - dimension)) - 1))
        averaged += probability * remaining(dimension)
    error = first_five + averaged + Fraction(12, size)
    if observed_bits in (64, 128, 192):
        assert error < Fraction(1, 1 << {64: 154, 128: 127, 192: 63}[observed_bits])
    return error


def fixed_observation_certificate(verifier):
    field, rng = Tower(64, verifier), Random(479)
    weights = field.eq([field.random(rng) for _ in range(12)])
    assert len(SPARSE_FIXED) == 448
    for bits in (64, 128, 192):
        observations = [1 << index if index < bits else rng.getrandbits(bits) for index in range(len(SPARSE_FIXED))]
        assert len(binary_basis(observations)) == bits
        vectors = [weights[index] | (value << 192) for index, value in zip(SPARSE_FIXED, observations)]
        assert len(binary_basis(vectors)) == 192 + bits
        fixed_observation_error(bits)
    adaptive = [weights[index] & 1 for index in SPARSE_FIXED]
    assert len(binary_basis(adaptive)) == 1
    assert len(binary_basis([weights[index] | (value << 192) for index, value in zip(SPARSE_FIXED, adaptive)])) == 192
    print("A random extension evaluation and fixed 64/128/192-bit disclosures have native joint ranks 256/320/384 on 448 bits.", flush=True)
    print("Uniform fixed-disclosure error bounds: below 2^-154, 2^-127 and 2^-63; only the 64-bit case has the target margin.", flush=True)
    print("Control: a disclosure chosen from the evaluation point can be dependent; the fixed-map hypothesis is necessary.", flush=True)
    assert len(DENSE_FIXED) == 1280 and set(SPARSE_FIXED) < set(DENSE_FIXED)
    for bits in (192, 256, 320):
        observations = [1 << index if index < bits else rng.getrandbits(bits) for index in range(len(DENSE_FIXED))]
        vectors = [weights[index] | (value << 192) for index, value in zip(DENSE_FIXED, observations)]
        assert len(binary_basis(vectors)) == 192 + bits
        dense_fixed_error(bits)
    assert dense_fixed_error(352) < Fraction(1, 1 << 158)
    assert dense_fixed_error(384) > Fraction(1, 1 << 128)
    print(
        "The 1280-bit support retains up to 320 fixed bits with error below 2^-160, also for geometric weights; 384 exceeds this proof budget.",
        flush=True,
    )


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


def compact_error_bounds():
    size = 1 << 192

    def power(exponent):
        return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)

    def tail(before, after):
        assert before <= after < 2 * before
        return Fraction(((1 << before) - 1) ** 2, (size - 1) * ((1 << (2 * before - after)) - 1))

    def singleton(dimension):
        return min(Fraction(1), power(193 - 5 * dimension))

    def seventh_average(before):
        return singleton(2 * before) + sum((tail(before, after) * singleton(after) for after in range(before, 2 * before)), Fraction())

    first_five = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    joint_sixth = Fraction(((1 << 32) - 1) ** 2, (size - 1) ** 2)
    joint_seventh = Fraction(((1 << 64) - 1) ** 2, (size - 1) ** 2)
    joint_seventh += 2 * sum((tail(32, d) * Fraction(((1 << (64 - d)) - 1) ** 2, size - 1) for d in range(32, 64)), Fraction())
    projected = seventh_average(64) + sum((tail(32, d) * seventh_average(d) for d in range(32, 64)), Fraction())
    core = 2 * first_five + joint_sixth + joint_seventh + 2 * projected + power(385 - 5 * 128)
    ordinary = core + Fraction(22, size) + Fraction(44, size - 1)
    weighted = ordinary + Fraction(44, size)
    assert Fraction(size, size - 1) ** 8 < 2
    assert core < ordinary < weighted < Fraction(1, 1 << 158)
    assert ordinary + Fraction(4294, size) < Fraction(1, 1 << 158)
    return core, ordinary, weighted


def compact_certificate(verifier):
    field, rng = Tower(64, verifier), Random(223)
    weights = [field.eq([field.random(rng) for _ in range(11)]) for _ in range(2)]
    assert len(COMPACT_TWO) == 640 and max(COMPACT_TWO) < 1 << 11
    for exponent in (0, 2):
        vectors = []
        for index in COMPACT_TWO:
            scale = int(verifier.GEN ** (exponent * index))
            vectors.append(field.mul(scale, weights[0][index]) | (field.mul(scale, weights[1][index]) << 192))
        assert len(binary_basis(vectors)) == 384
    compact_error_bounds()
    bytecode = [0] * (1 << (11 + verifier.BUS_BITS))
    layout = verifier.build_layout(bytecode, 25, (19, 19, 19, 19, 20, 18))
    assert layout.stack_log == 28
    assert layout.placements[verifier.QFLOCK].variables == 26
    placed = 4 * (1 << 25) + (1 << 11) + (15 + 15 + 8 + 15) * (1 << 19) + 14 * (1 << 20) + 275 * (1 << 18)
    assert placed == 248776704 and verifier.log2_ceil(placed) == layout.stack_log
    assert (placed + (1 << 22) - 1) // (1 << 22) == 60
    assert [layout.placements[column].index >> 22 for column in range(3)] == [16, 24, 32]
    for rate in range(1, 5):
        verifier.derive_config(layout.stack_log, rate)
    assert 96 * len(COMPACT_TWO) == 61440
    assert (128 - 96) * (1 << 11) == 65536
    oversized = verifier.build_layout(bytecode, 25, (19, 19, 19, 19, 20, 21))
    assert oversized.stack_log > verifier.MAX_STACKED_LOG
    print("Compact two-point span: 640 bits on 11 coordinates have native binary rank 384; exact error bound below 2^-158.", flush=True)
    print("Flock batch log 18 fits a native stack-log-28 memory layout; the former batch-log-21 layout exceeds the PCS cap.", flush=True)


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
    compact_certificate(verifier_module())
    fixed_observation_certificate(verifier_module())
