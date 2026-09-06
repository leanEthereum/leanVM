"""Exact packed-integer field multiplication for optional large research audits."""

from random import Random


def mask(bits, group):
    return sum(((1 << group) - 1) << (8 * start) for start in range(0, bits, group))


SPREAD = tuple((7 * group, mask(64, group)) for group in (32, 16, 8, 4, 2, 1))
GATHER = tuple((7 * group // 2, mask(128, group)) for group in (2, 4, 8, 16, 32, 64, 128))
PARITY, LOW = mask(128, 1), (1 << 64) - 1


def spread(value):
    for shift, selected in SPREAD:
        value = (value | value << shift) & selected
    return value


def packed_mul(left, right):
    if not left or not right:
        return 0
    if left == 1:
        return right
    if right == 1:
        return left
    product = (spread(left) * spread(right)) & PARITY
    for shift, selected in GATHER:
        product = (product | product >> shift) & selected
    low, high = product & LOW, product >> 64
    folded = low ^ high ^ (high << 1) ^ (high << 3) ^ (high << 4)
    overflow = folded >> 64
    return ((folded & LOW) ^ overflow ^ (overflow << 1) ^ (overflow << 3) ^ (overflow << 4)) & LOW


def accelerate(verifier):
    reference = verifier._base_mul
    assert reference is not packed_mul
    for bit in range(64):
        assert spread(1 << bit) == 1 << (8 * bit)
        for other in range(64):
            assert packed_mul(1 << bit, 1 << other) == reference(1 << bit, 1 << other)
    rng = Random(211)
    values = [0, 1, LOW, LOW >> 1, 0xAAAAAAAAAAAAAAAA, 0x5555555555555555, *[rng.getrandbits(64) for _ in range(64)]]
    for left in values:
        for right in values:
            assert packed_mul(left, right) == reference(left, right)
    verifier._base_mul = packed_mul
    print(
        "Packed GF(2^64) multiplication matches all basis products, carry-heavy patterns and seeded random cases; only this audit instance is changed",
        flush=True,
    )
