"""Smoothing a coupled push/pull pair while respecting a native count relation."""

from fractions import Fraction
from itertools import product
from math import comb
from random import Random
from types import SimpleNamespace

from zk_audit_field import accelerate
from zk_count_children_audit import polynomial_product
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module
from zk_quartic_smoothing_audit import coefficients, obstruction, trace, walsh


def translate(v, polynomial, left, right):
    result = {}
    for (i, j), value in polynomial.items():
        for a in range(i + 1):
            for b in range(j + 1):
                if comb(i, a) % 2 and comb(j, b) % 2:
                    result[a, b] = result.get((a, b), v.ZERO) + value * left ** (i - a) * right ** (j - b)
    return result


def combined_obstruction(v, endpoints, other, total, shift, combiner, frequency):
    quadratic, linear, _ = obstruction(v, endpoints, total, frequency)
    second = obstruction(v, other, total + v.E.sum(shift), frequency)
    for target, source in zip((quadratic, linear), second[:2], strict=True):
        for index, value in translate(v, source, shift[1], shift[2]).items():
            target[index] = target.get(index, v.ZERO) + combiner * value
    result = dict(quadratic)
    for (i, j), value in linear.items():
        result[2 * i, 2 * j] = result.get((2 * i, 2 * j), v.ZERO) + value * value
    return quadratic, linear, {index: value for index, value in result.items() if value}


def native_certificate(v):
    rng = Random(225)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    endpoints, other, total, combiner = [sample() for _ in range(4)], [sample() for _ in range(4)], sample(), sample()
    a, b, c, d = endpoints
    aa, bb, cc, dd = other
    factors = (
        b * c * (a + d) + combiner * bb * cc * (aa + dd),
        c * (a + b + d) + combiner * cc * (aa + bb + dd),
        c + combiner * cc,
        v.ONE + combiner,
    )
    assert all(factors)
    total_endpoints, total_other = v.E.sum(endpoints), v.E.sum(other)
    assert factors[0] == b * c * (total_endpoints + b + c) + combiner * bb * cc * (total_other + bb + cc)
    assert factors[1] == c * (total_endpoints + c) + combiner * cc * (total_other + cc)
    assert not combined_obstruction(v, endpoints, endpoints, total, [v.ZERO] * 4, v.ONE, [sample() for _ in range(4)])[2]

    def evaluate(polynomial, left, right):
        return v.E.sum(value * left**i * right**j for (i, j), value in polynomial.items())

    def phase(first, middle, right, shift, frequency):
        slopes = [first, middle, right, total + first + middle + right]
        push = polynomial_product(v, zip(endpoints, slopes, strict=True))
        pull = polynomial_product(v, zip(other, [a + b for a, b in zip(slopes, shift, strict=True)], strict=True))
        return v.dot(frequency, [a + combiner * b for a, b in zip(push[1:], pull[1:], strict=True)])

    for highest, monomial in enumerate(((0, 0), (2, 0), (4, 0), (4, 2))):
        frequency = [sample() if j <= highest else v.ZERO for j in range(4)]
        for _ in range(3):
            shift = [sample() for _ in range(4)]
            quadratic, linear, constraint = combined_obstruction(v, endpoints, other, total, shift, combiner, frequency)
            assert constraint[monomial] == (frequency[highest] * factors[highest]) ** 2
            assert max(sum(index) for index in constraint) <= (0, 2, 4, 6)[highest]
            left, middle, right = sample(), sample(), sample()

            observed = phase(left, middle, right, shift, frequency) + phase(v.ZERO, middle, right, shift, frequency)
            u, w = evaluate(quadratic, middle, right), evaluate(linear, middle, right)
            assert observed == u * left**2 + w * left
            assert evaluate(constraint, middle, right) == u + w * w
            assert trace(v, observed) == trace(v, (u ** (1 << 191) + w) * left)
    print(
        "Coupled quartic phase identities hold for arbitrary slope offsets; four explicit factors certify nonzero degree-at-most-six obstructions",
        flush=True,
    )


def exhaustive(bits):
    field, rng = Field(bits, {3: 0b1011, 4: 0b10011}[bits]), Random(226)
    size, mul, combiner = field.size, lambda a, b: field.mul[a][b], 2
    while True:
        endpoints, other = [rng.randrange(size) for _ in range(4)], [rng.randrange(size) for _ in range(4)]
        a, b, c, d = endpoints
        aa, bb, cc, dd = other
        factors = (
            c ^ mul(combiner, cc),
            mul(c, a ^ b ^ d) ^ mul(combiner, mul(cc, aa ^ bb ^ dd)),
            mul(mul(b, c), a ^ d) ^ mul(combiner, mul(mul(bb, cc), aa ^ dd)),
        )
        if all(factors):
            break
    transforms = []
    for group, (values, total, scale) in enumerate(((endpoints, 3, 1), ((1, 2, 3, 4), 0, 3), ((2, 1, 4, 3), 1, 4))):
        counts = [0] * size**4
        for first in product(range(size), repeat=3):
            slopes = (*first, total ^ first[0] ^ first[1] ^ first[2])
            polynomial = coefficients(mul, values, slopes)
            if group == 0:
                shifted = [value ^ offset for value, offset in zip(slopes, (1, 2, 4, 6), strict=True)]
                second = coefficients(mul, other, shifted)
                polynomial = [a ^ mul(combiner, b) for a, b in zip(polynomial, second, strict=True)]
            counts[sum(mul(scale, value) << (bits * j) for j, value in enumerate(polynomial[1:]))] += 1
        transform = walsh(counts)
        assert transform[0] == size**3 and max(map(abs, transform[1:])) <= 6 * size**2
        transforms.append(transform)
    convolution = walsh([a * b * c for a, b, c in zip(*transforms, strict=True)])
    assert all(value >= 0 and value % size**4 == 0 for value in convolution)
    counts = [value // size**4 for value in convolution]
    assert sum(counts) == size**9
    distance = Fraction(sum(abs(value - size**5) for value in counts), 2 * size**9)
    assert distance <= Fraction(108, size) and distance < Fraction(1, 4)
    print(f"GF(2^{bits}) exhaustive coupled-pair plus two-quartic convolution: exact TV {distance}", flush=True)


def three_round_reader(v):
    rng = Random(227)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    challenges, equalities = [sample() for _ in range(3)], [sample() for _ in range(3)]
    combiner, factor = sample(), sample()
    work = [[[sample() for _ in range(8)] for _ in range(4)] for _ in range(3)]
    for child in range(4):
        work[1][child][5] = work[0][child][5] + factor * work[2][child][0]
        work[2][child][4:] = [v.ONE] * 4
        pp, qq, cc = work[0][child], work[1][child], work[2][child]
        hp, hq, hc = pp[4] + pp[5], qq[4] + qq[5], cc[0] + cc[1]
        p, q, c = pp[4] + challenges[0] * hp, qq[4] + challenges[0] * hq, cc[0] + challenges[0] * hc
        assert hq == hp + (p + q + factor * c + factor * challenges[0] * hc) / (v.ONE + challenges[0])
    wire, messages = [], []
    for coordinate, challenge in enumerate(challenges):
        message = [v.ZERO] * 5
        weights = v.eq_kernel(equalities[coordinate + 1 :])
        for side, children in enumerate(work):
            for row, weight in enumerate(weights):
                lines = [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in children]
                for degree, value in enumerate(polynomial_product(v, lines)):
                    message[degree] += combiner**side * weight * value
        if messages:
            assert v.poly_eval(messages[-1], challenges[coordinate - 1]) == message[0] + equalities[coordinate] * v.E.sum(message[1:])
        messages.append(message)
        wire.extend(message[1:])
        work = [
            [[child[2 * row] + challenge * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in side]
            for side in work
        ]
    incoming = messages[0][0] + equalities[0] * v.E.sum(messages[0][1:])
    stream, coins = iter(wire), iter(challenges)
    transcript = SimpleNamespace(next_scalars=lambda n: [next(stream) for _ in range(n)], sample=lambda: next(coins))
    transcript.sumcheck_round_poly = lambda n, claim, eq: v.Transcript.sumcheck_round_poly(transcript, n, claim, eq)
    point, claim = v.sumcheck(transcript, incoming, 5, equalities)
    assert point == tuple(challenges) and next(stream, None) is None and next(coins, None) is None
    assert claim == v.E.sum(combiner**side * rows[0][0] * rows[1][0] * rows[2][0] * rows[3][0] for side, rows in enumerate(work))
    print(
        "The native count coupling and slope-shift formula agree; the actual three-round sumcheck reader accepts all linking claims and children",
        flush=True,
    )


if __name__ == "__main__":
    exhaustive(3)
    exhaustive(4)
    verifier = verifier_module()
    accelerate(verifier)
    native_certificate(verifier)
    three_round_reader(verifier)
