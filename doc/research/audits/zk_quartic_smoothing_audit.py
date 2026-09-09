"""Quartic smoothing with fixed endpoint values and a fixed sum of slopes."""

from fractions import Fraction
from itertools import product
from math import comb
from random import Random
from types import SimpleNamespace

from zk_audit_field import accelerate
from zk_count_children_audit import polynomial_product
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module


def coefficients(mul, endpoints, slopes):
    polynomial = [1]
    for constant, slope in zip(endpoints, slopes, strict=True):
        out = [0] * (len(polynomial) + 1)
        for degree, value in enumerate(polynomial):
            out[degree] ^= mul(value, constant)
            out[degree + 1] ^= mul(value, slope)
        polynomial = out
    return polynomial


def walsh(values):
    result = list(values)
    width = 1
    while width < len(result):
        for start in range(0, len(result), 2 * width):
            for index in range(start, start + width):
                a, b = result[index], result[index + width]
                result[index], result[index + width] = a + b, a - b
        width *= 2
    return result


def exhaustive(bits):
    field = Field(bits, {3: 0b1011, 4: 0b10011}[bits])
    size, mul = field.size, lambda a, b: field.mul[a][b]
    endpoint_sets = ((1, 2, 3, 4), (2, 1, 4, 3), (3, 4, 1, 2))
    transforms = []
    for endpoints, total, scale in zip(endpoint_sets, (0, 1, 3), (1, 2, mul(2, 2)), strict=True):
        counts = [0] * size**4
        for first in product(range(size), repeat=3):
            slopes = (*first, total ^ first[0] ^ first[1] ^ first[2])
            polynomial = coefficients(mul, endpoints, slopes)
            key = sum(mul(scale, value) << (bits * j) for j, value in enumerate(polynomial[1:]))
            counts[key] += 1
        transform = walsh(counts)
        assert transform[0] == size**3
        assert max(map(abs, transform[1:])) <= 6 * size**2
        transforms.append(transform)
    convolution = walsh([a * b * c for a, b, c in zip(*transforms, strict=True)])
    assert all(value >= 0 and value % size**4 == 0 for value in convolution)
    counts = [value // size**4 for value in convolution]
    total, uniform = size**9, size**5
    assert sum(counts) == total
    distance = Fraction(sum(abs(value - uniform) for value in counts), 2 * total)
    assert distance <= Fraction(108, size)
    assert distance < Fraction(1, size)
    print(f"GF(2^{bits}) exhaustive three-channel convolution: exact TV {distance}; every fixed-sum slope triple enumerated", flush=True)


def trace(v, value):
    result, power = v.ZERO, value
    for _ in range(192):
        result += power
        power *= power
    assert result in (v.ZERO, v.ONE)
    return result


def obstruction(v, endpoints, total, frequency):
    a, b, c, d = endpoints
    t1, t2, t3, t4 = frequency
    u = {(0, 0): t2 * b * c, (1, 0): t3 * c, (0, 1): t3 * b, (1, 1): t4}
    linear = {
        (0, 0): t1 * (a + d) * b * c + t2 * total * b * c,
        (1, 0): t2 * c * (a + b + d) + t3 * total * c,
        (0, 1): t2 * b * (a + c + d) + t3 * total * b,
        (2, 0): t3 * c,
        (0, 2): t3 * b,
        (1, 1): t3 * (a + b + c + d) + t4 * total,
        (2, 1): t4,
        (1, 2): t4,
    }
    result = dict(u)
    for (i, j), value in linear.items():
        index = 2 * i, 2 * j
        result[index] = result.get(index, v.ZERO) + value * value
    return u, linear, {index: value for index, value in result.items() if value}


def native_certificate(v):
    rng = Random(218)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    endpoints, total = [sample() for _ in range(4)], sample()
    a, b, c, d = endpoints
    assert b and c and b != c and a != d

    def evaluate(polynomial, left, right):
        return v.E.sum(value * left**i * right**j for (i, j), value in polynomial.items())

    for highest in range(4):
        frequency = [sample() if j <= highest else v.ZERO for j in range(4)]
        quadratic, linear, constraint = obstruction(v, endpoints, total, frequency)
        assert constraint
        assert max(sum(index) for index in constraint) <= (0, 2, 4, 6)[highest]
        if highest == 3:
            assert constraint[4, 2] == frequency[3] ** 2
        elif highest == 2:
            assert constraint[4, 0] == (frequency[2] * c) ** 2
        elif highest == 1:
            assert constraint.get((2, 0), v.ZERO) == (frequency[1] * c * (a + b + d)) ** 2
            assert constraint.get((0, 2), v.ZERO) == (frequency[1] * b * (a + c + d)) ** 2
        else:
            assert constraint == {(0, 0): (frequency[0] * (a + d) * b * c) ** 2}
        for _ in range(3):
            left, middle, right = sample(), sample(), sample()
            slopes = [left, middle, right, total + left + middle + right]
            actual = polynomial_product(v, zip(endpoints, slopes, strict=True))
            zero = polynomial_product(v, zip(endpoints, [v.ZERO, middle, right, total + middle + right], strict=True))
            difference = v.dot(frequency, [x + y for x, y in zip(actual[1:], zero[1:], strict=True)])
            u, w = evaluate(quadratic, middle, right), evaluate(linear, middle, right)
            assert difference == u * left**2 + w * left
            assert evaluate(constraint, middle, right) == u + w * w
            assert trace(v, difference) == trace(v, (u ** (1 << 191) + w) * left)
    print("Actual-field phase and absolute-trace identities hold; triangular monomials certify a nonzero degree-at-most-six obstruction", flush=True)
    assert Fraction(108 + 12 + 3, 1 << 192) < Fraction(1, 1 << 185)
    print(
        "Three fixed-sum slope channels smooth four coefficients within 108/2^192; endpoint, selector and combiner exclusions fit below 2^-185",
        flush=True,
    )


def two_round_reader(v):
    rng = Random(223)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    tau, challenge, eta, equality, combiner = [sample() for _ in range(5)]
    values = [[sample() for _ in range(4)] for _ in range(3)]
    slopes = [[sample() for _ in range(4)] for _ in range(3)]
    active = [[(value + tau * slope, slope) for value, slope in zip(row, change, strict=True)] for row, change in zip(values, slopes, strict=True)]
    fixed = [[(sample(), sample()) for _ in range(4)] for _ in range(2)] + [[(v.ONE, v.ZERO)] * 4]
    penultimate, last = [v.ZERO] * 5, [v.ZERO] * 5
    children = []
    for side in range(3):
        active_weight = eta if side < 2 else v.ONE + eta
        for lines, scale in ((active[side], active_weight), (fixed[side], v.ONE + active_weight)):
            for degree, coefficient in enumerate(polynomial_product(v, lines)):
                penultimate[degree] += combiner**side * scale * coefficient
        other = [constant + tau * slope for constant, slope in fixed[side]]
        lines = [(old if side < 2 else new, old + new) for old, new in zip(other, values[side], strict=True)]
        children.append([constant + challenge * slope for constant, slope in lines])
        for degree, coefficient in enumerate(polynomial_product(v, lines)):
            last[degree] += combiner**side * coefficient
    assert v.poly_eval(penultimate, tau) == last[0] + eta * v.E.sum(last[1:])

    def shift(polynomial):
        return [v.E.sum(value * tau ** (j - i) for j, value in enumerate(polynomial) if j >= i and comb(j, i) % 2) for i in range(5)]

    assert shift(penultimate)[0] == v.poly_eval(penultimate, tau) and shift(shift(penultimate)) == penultimate
    stream, coins = iter([*penultimate[1:], *last[1:]]), iter((tau, challenge))
    transcript = SimpleNamespace(next_scalars=lambda n: [next(stream) for _ in range(n)], sample=lambda: next(coins))
    transcript.sumcheck_round_poly = lambda n, claim, eq: v.Transcript.sumcheck_round_poly(transcript, n, claim, eq)
    incoming = penultimate[0] + equality * v.E.sum(penultimate[1:])
    point, claim = v.sumcheck(transcript, incoming, 5, [equality, eta])
    assert point == (tau, challenge) and next(stream, None) is None and next(coins, None) is None
    assert claim == v.E.sum(combiner**side * row[0] * row[1] * row[2] * row[3] for side, row in enumerate(children))
    print("The actual two-round reader accepts the active/fixed-half decomposition, incoming claim and children; centering is invertible", flush=True)


if __name__ == "__main__":
    exhaustive(3)
    exhaustive(4)
    verifier = verifier_module()
    accelerate(verifier)
    native_certificate(verifier)
    two_round_reader(verifier)
