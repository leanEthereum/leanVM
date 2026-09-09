"""Three-point binary span and the message/digest interface, not full Flock ZK."""

from fractions import Fraction
from functools import cache
from random import Random

from zk_flock_coset_audit import library_messages, reordered_index
from zk_flock_skip_audit import witness
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

THREE_POINT_SUPPORT = list(range(256)) + [low | (1 << bit) for bit in range(8, 11) for low in range(256)]


def three_point_error():
    size, bits = 1 << 192, 192

    def power(exponent):
        return Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)

    def final_error(support, dimension):
        return min(Fraction(1), power(support * bits + 1 - 4 * dimension))

    @cache
    def tail(before, after):
        return min(Fraction(1), Fraction(((1 << before) - 1) ** 2, (size - 1) * ((1 << (2 * before - after)) - 1)))

    @cache
    def singleton(steps, dimension):
        if steps == 0:
            return final_error(1, dimension)
        maximum = min(2 * dimension, bits)
        return singleton(steps - 1, maximum) + sum(
            (tail(dimension, after) * singleton(steps - 1, after) for after in range(dimension, maximum)), Fraction()
        )

    first_five = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    pair_six = Fraction(((1 << 32) - 1) ** 2, (size - 1) ** 2)
    pair_seven = Fraction(((1 << 64) - 1) ** 2, (size - 1) ** 2)
    pair_seven += 2 * sum((tail(32, d) * Fraction(((1 << (64 - d)) - 1) ** 2, size - 1) for d in range(32, 64)), Fraction())
    eighth = Fraction(((1 << 128) - 1) ** 2, (size - 1) ** 3) + 3 * Fraction(((1 << 96) - 1) ** 2, (size - 1) ** 2)
    pair_intersection = Fraction(((1 << 128) - 1) ** 2, (size - 1) ** 2) + 2 * Fraction(((1 << 96) - 1) ** 2, size - 1)
    pair_average = final_error(2, 256) + sum(
        (min(Fraction(1), pair_intersection / ((1 << (256 - d)) - 1)) * final_error(2, d) for d in range(128, 256)), Fraction()
    )
    single_average = singleton(3, 32)
    core = 3 * first_five + 3 * (pair_six + pair_seven) + eighth + 3 * single_average + 3 * pair_average + final_error(3, 256)
    ordinary = core + Fraction(33, size) + Fraction(66, size - 1)
    assert Fraction(size, size - 1) ** 9 < 2
    assert single_average < Fraction(1, 1 << 250) and pair_average < Fraction(1, 1 << 250)
    assert ordinary + Fraction(2205 + 1918 + 42 + 1 + 21, size) < Fraction(1, 1 << 158)
    return ordinary


def certificate(verifier):
    field, rng = Tower(64, verifier), Random(431)
    weights = [field.eq([field.random(rng) for _ in range(11)]) for _ in range(3)]
    columns = [sum(weight[index] << (192 * coordinate) for coordinate, weight in enumerate(weights)) for index in THREE_POINT_SUPPORT]
    assert len(THREE_POINT_SUPPORT) == 1024 and len(binary_basis(columns)) == 576
    baseline = witness(verifier, [0] * 16)[0]
    slots = (*range(4, 8), *range(10, 18))
    differences = []
    for message in library_messages()[:96]:
        difference = witness(verifier, message)[0] ^ baseline
        differences.append([(difference >> (64 * slot)) & ((1 << 64) - 1) for slot in slots])
    assert len(field.pivots(differences)) == 12
    assert all(768 + offset not in THREE_POINT_SUPPORT for offset in range(5))
    assert [reordered_index(3 * 2048 + 768 + offset) for offset in range(5)] == list(range(432, 437))
    lane_counts = [0] * 16
    for bank in range(96):
        for sparse in THREE_POINT_SUPPORT:
            lane_counts[reordered_index(sparse + (bank << 11)) >> 14] += 1
    assert lane_counts == [6144] * 16
    assert 96 * len(THREE_POINT_SUPPORT) == 98304
    assert 96 * (2048 - len(THREE_POINT_SUPPORT)) == 98304
    three_point_error()
    print("Three-point support: 1024 binary choices on eleven coordinates, native joint rank 576 and exact error below 2^-158.", flush=True)
    print("The twelve message/digest features have fixed base-field rank twelve; the general metadata bank stays disjoint.", flush=True)


if __name__ == "__main__":
    certificate(verifier_module())
