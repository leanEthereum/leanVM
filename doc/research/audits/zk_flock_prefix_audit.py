"""Joint skip and within-block Flock messages from valid compression choices."""

from fractions import Fraction
from random import Random
from types import SimpleNamespace

from zk_count_mixed_audit import echelon
from zk_flock_skip_audit import (
    check_rows,
    cycle_certificate,
    skip_halves,
    tables,
    witness,
)
from zk_pcs_audit import verifier_module


def quirky_tables(verifier, triple, point, batch_bits=0):
    lagrange = verifier.lagrange_weights(64, point)
    return [
        [verifier.E.sum(weight for bit, weight in enumerate(lagrange) if packed >> (64 * row + bit) & 1) for row in range(1 << (8 + batch_bits))]
        for packed in triple
    ]


def prefix(verifier, triple, halves, equality, point, challenge, batch_bits=0):
    assert len(equality) == 8 + batch_bits and len(challenge) == 8
    wire = [first + equality[7] * (first + second) for first, second in zip(*halves)]
    running = verifier.lagrange_interpolate(128, [verifier.ZERO] * 64 + wire, point)
    initial = running
    z, a, b = quirky_tables(verifier, triple, point, batch_bits)
    for coordinate, coin in enumerate(challenge):
        polynomial = [verifier.ZERO] * 3
        for row, scale in enumerate(verifier.eq_kernel(equality[coordinate + 1 :])):
            aa, bb, zz = a[2 * row], b[2 * row], z[2 * row]
            da, db, dz = aa + a[2 * row + 1], bb + b[2 * row + 1], zz + z[2 * row + 1]
            for output, value in enumerate((aa * bb + zz, aa * db + da * bb + dz, da * db)):
                polynomial[output] += scale * value
        assert running == polynomial[0] + equality[coordinate] * (polynomial[1] + polynomial[2])
        wire.extend(polynomial[1:])
        running = verifier.poly_eval(polynomial, coin)
        z, a, b = [[values[2 * row] + coin * (values[2 * row] + values[2 * row + 1]) for row in range(len(values) // 2)] for values in (z, a, b)]
    assert running == verifier.E.sum(scale * (aa * bb + zz) for scale, aa, bb, zz in zip(verifier.eq_kernel(equality[8:]), a, b, z))
    scalars, coins = iter(wire[64:]), iter(challenge)
    replay = SimpleNamespace(next_scalars=lambda count: tuple(next(scalars) for _ in range(count)), sample=lambda: next(coins))
    replay.sumcheck_round_poly = lambda count, claim, eq: verifier.Transcript.sumcheck_round_poly(replay, count, claim, eq)
    recovered_point, recovered_claim = verifier.sumcheck(replay, initial, 3, equality[:8])
    assert recovered_point == tuple(challenge) and recovered_claim == running
    return wire


def batch_certificate(verifier, messages, lookup, equality, point, challenge, rng):
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    equality = [*equality[:7], sample()]
    batch_point = [sample(), sample()]
    weights = verifier.eq_kernel(batch_point)
    triples = [witness(verifier, message) for message in messages[:4]]
    halves = [skip_halves(verifier, triple, lookup) for triple in triples]
    individual = [prefix(verifier, triple, half, equality, point, challenge) for triple, half in zip(triples, halves)]
    combined = tuple(sum(triple[column] << ((1 << 14) * index) for index, triple in enumerate(triples)) for column in range(3))
    combined_halves = [[verifier.dot(weights, [half[branch][output] for half in halves]) for output in range(64)] for branch in (0, 1)]
    joint = prefix(verifier, combined, combined_halves, [*equality, *batch_point], point, challenge, batch_bits=2)
    assert joint == [verifier.dot(weights, [values[output] for values in individual]) for output in range(80)]
    print("Four-compression dense replay agrees with weighted per-compression features and the reference sumcheck verifier", flush=True)


def bound_certificate():
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    degree = 63 + sum(2 * (126 + 2 * coordinate + int(coordinate < 7)) for coordinate in range(8))
    assert degree == 2205
    assert delta + Fraction(degree + 12 + 14 + 1, size) < Fraction(1, 1 << 157)
    print("Joint-prefix minor degree 2205; sparse-span error plus 2232/2^192 is below 2^-157", flush=True)


def audit(verifier):
    rng = Random(152)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    point, challenge = sample(), [sample() for _ in range(8)]
    equality = [*verifier.FIXED_CHALLENGES, verifier.ZERO]
    lookup = tables(verifier)
    baseline = witness(verifier, [0] * 16)
    check_rows(verifier, baseline)
    base = prefix(verifier, baseline, skip_halves(verifier, baseline, lookup), equality, point, challenge)
    differences, messages = [], []
    for index in range(128):
        message = [rng.getrandbits(32) for _ in range(16)]
        messages.append(message)
        triple = witness(verifier, message)
        check_rows(verifier, triple)
        values = prefix(verifier, triple, skip_halves(verifier, triple, lookup), equality, point, challenge)
        differences.append([a + b for a, b in zip(values, base)])
        if index % 8 == 7:
            print(f"Verified {index + 1} complete compression-prefix directions", flush=True)
    rank = len(echelon(verifier, differences))
    print(f"Joint skip and eight within-block rounds: extension rank {rank}/79", flush=True)
    assert rank == 79
    batch_certificate(verifier, messages, lookup, equality, point, challenge, rng)
    cycle_certificate(verifier, messages)
    bound_certificate()


if __name__ == "__main__":
    audit(verifier_module())
