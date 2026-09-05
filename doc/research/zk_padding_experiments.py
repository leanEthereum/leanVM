"""Small-field experiments for the ZK padding investigation, not a ZK implementation."""

from collections import Counter
from itertools import product
from random import Random


class Field:
    def __init__(self, bits, modulus):
        self.size = 1 << bits
        self.mul = [[self.multiply(a, b, modulus) for b in range(self.size)] for a in range(self.size)]
        self.inv = [0] + [next(b for b in range(1, self.size) if self.mul[a][b] == 1) for a in range(1, self.size)]

    def multiply(self, a, b, modulus):
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & self.size:
                a ^= modulus
        return out

    def rank(self, matrix):
        matrix = [list(row) for row in matrix]
        if not matrix:
            return 0
        rank = 0
        for col in range(len(matrix[0])):
            pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col]), None)
            if pivot is None:
                continue
            matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
            matrix[rank] = [self.mul[self.inv[matrix[rank][col]]][x] for x in matrix[rank]]
            for i in range(rank + 1, len(matrix)):
                factor = matrix[i][col]
                if factor:
                    matrix[i] = [x ^ self.mul[factor][y] for x, y in zip(matrix[i], matrix[rank])]
            rank += 1
            if rank == len(matrix):
                break
        return rank


def eq_weights(field, point):
    weights = [1]
    for r in point:
        weights = [field.mul[1 ^ r][x] for x in weights] + [field.mul[r][x] for x in weights]
    return weights


def scalar_product(field, left, right):
    out = 0
    for a, b in zip(left, right):
        out ^= field.mul[a][b]
    return out


def simulated_terminal_c(field, messages, terminal_b, equality, challenges):
    claim = cursor = 0
    for round_index, coordinate in enumerate(reversed(range(len(challenges)))):
        at_one = 0 if round_index == 0 else messages[cursor]
        cursor += int(round_index != 0)
        quadratic = messages[cursor]
        cursor += 1
        r = equality[coordinate]
        at_zero = field.mul[claim ^ field.mul[r][at_one]][field.inv[1 ^ r]]
        challenge = challenges[coordinate]
        claim = at_zero ^ field.mul[challenge][at_zero ^ at_one ^ field.mul[1 ^ challenge][quadratic]]
    assert cursor == len(messages) - 1
    return claim ^ field.mul[messages[-1]][terminal_b]


def multiplication_view_matrix(field, b, equality, challenges):
    """Linear dependence on a of a high-variable-first zerocheck of a*b+c=0.

    Each original row has c=a*b. The coordinates are the first quadratic
    coefficient, then G(1) and the quadratic coefficient per later round,
    followed by the terminal a evaluation. The terminal b is handled separately.
    """
    size = len(b)
    a = [[int(i == j) for j in range(size)] for i in range(size)]
    c = [[field.mul[b[i]][x] for x in row] for i, row in enumerate(a)]
    b = list(b)
    messages = []
    for coordinate in reversed(range(len(challenges))):
        half = len(b) // 2
        weights = eq_weights(field, equality[:coordinate])
        at_one = [0] * size
        quadratic = [0] * size
        for i, weight in enumerate(weights):
            slope_b = b[i] ^ b[i + half]
            for j in range(size):
                at_one[j] ^= field.mul[weight][field.mul[a[i + half][j]][b[i + half]] ^ c[i + half][j]]
                quadratic[j] ^= field.mul[weight][field.mul[a[i][j] ^ a[i + half][j]][slope_b]]
        if messages:
            messages.append(at_one)
        messages.append(quadratic)
        r = challenges[coordinate]
        a = [[x ^ field.mul[r][x ^ y] for x, y in zip(lo, hi)] for lo, hi in zip(a[:half], a[half:])]
        c = [[x ^ field.mul[r][x ^ y] for x, y in zip(lo, hi)] for lo, hi in zip(c[:half], c[half:])]
        b = [x ^ field.mul[r][x ^ y] for x, y in zip(b[:half], b[half:])]
    messages.append(a[0])
    return messages, b[0]


def multiplication_view_direct(field, a, b, equality, challenges):
    a, b = list(a), list(b)
    c = [field.mul[x][y] for x, y in zip(a, b)]
    messages = []
    for coordinate in reversed(range(len(challenges))):
        half = len(a) // 2
        weights = eq_weights(field, equality[:coordinate])
        at_one = quadratic = 0
        for i, weight in enumerate(weights):
            at_one ^= field.mul[weight][field.mul[a[i + half]][b[i + half]] ^ c[i + half]]
            quadratic ^= field.mul[weight][field.mul[a[i] ^ a[i + half]][b[i] ^ b[i + half]]]
        if messages:
            messages.append(at_one)
        messages.append(quadratic)
        r = challenges[coordinate]
        a, b, c = ([x ^ field.mul[r][x ^ y] for x, y in zip(v[:half], v[half:])] for v in (a, b, c))
    messages.append(a[0])
    return tuple(messages), b[0], c[0]


def sparse_padding_matrix(field, positions, b_values, equality, challenges):
    """The minor at zero real b, without materializing the real rows."""
    width = len(positions)
    a = {p: [int(i == j) for j in range(width)] for i, p in enumerate(positions)}
    b = dict(zip(positions, b_values))
    c = {p: [field.mul[b[p]][x] for x in row] for p, row in a.items()}
    zero = [0] * width
    messages = []
    for coordinate in reversed(range(len(challenges))):
        half = 1 << coordinate
        pairs = sorted({p % half for p in a})
        at_one = [0] * width
        quadratic = [0] * width
        for i in pairs:
            weight = 1
            for j, r in enumerate(equality[:coordinate]):
                weight = field.mul[weight][r if i & (1 << j) else 1 ^ r]
            lo, hi = a.get(i, zero), a.get(i + half, zero)
            for j in range(width):
                at_one[j] ^= field.mul[weight][field.mul[hi[j]][b.get(i + half, 0)] ^ c.get(i + half, zero)[j]]
                quadratic[j] ^= field.mul[weight][field.mul[lo[j] ^ hi[j]][b.get(i, 0) ^ b.get(i + half, 0)]]
        if messages:
            messages.append(at_one)
        messages.append(quadratic)
        r = challenges[coordinate]
        a = {i: [x ^ field.mul[r][x ^ y] for x, y in zip(a.get(i, zero), a.get(i + half, zero))] for i in pairs}
        c = {i: [x ^ field.mul[r][x ^ y] for x, y in zip(c.get(i, zero), c.get(i + half, zero))] for i in pairs}
        b = {i: b.get(i, 0) ^ field.mul[r][b.get(i, 0) ^ b.get(i + half, 0)] for i in pairs}
    messages.append(a[0])
    return messages


def comb_positions(log_size):
    return [0, 1] + [i + j for i in (1 << k for k in range(1, log_size)) for j in range(2)]


def comb_certificates():
    field = Field(8, 0x11B)
    rng = Random(1)
    for log_size in range(2, 33):
        positions = comb_positions(log_size)
        for attempt in range(100):
            equality = [rng.randrange(2, field.size) for _ in range(log_size)]
            challenges = [rng.randrange(2, field.size) for _ in range(log_size)]
            b_values = [rng.randrange(field.size) for _ in positions]
            matrix = sparse_padding_matrix(field, positions, b_values, equality, challenges)
            if log_size <= 6:
                b = [0] * (1 << log_size)
                for i, value in zip(positions, b_values):
                    b[i] = value
                dense, _ = multiplication_view_matrix(field, b, equality, challenges)
                assert matrix == [[row[i] for i in positions] for row in dense]
            if field.rank(matrix) == 2 * log_size:
                break
        else:
            raise AssertionError(f"No nonsingular minor for log size {log_size}")
    print("Comb padding: nonsingular minors certified for every log size 2..32 using 2n valid padding rows")


def subfield_expansion():
    field = Field(6, 0x43)
    small = Field(2, 0b111)
    omega = next(x for x in range(2, field.size) if field.mul[x][x] ^ x ^ 1 == 0)
    embed = [0, 1, omega, omega ^ 1]
    generator = next(x for x in range(field.size) if x not in embed)
    square = field.mul[generator][generator]
    coordinates = {embed[a] ^ field.mul[generator][embed[b]] ^ field.mul[square][embed[c]]: (a, b, c) for a, b, c in product(range(4), repeat=3)}
    assert len(coordinates) == field.size
    for a, b in product(range(4), repeat=2):
        assert embed[small.mul[a][b]] == field.mul[embed[a]][embed[b]]
    return field, small, embed, coordinates


def base_field_ranks():
    field, small, embed, coordinates = subfield_expansion()
    rng = Random(2)
    for log_size in (5, 6, 7, 8):
        positions = [8 * i + j for i in comb_positions(log_size - 3) for j in range(8)]
        histogram = Counter()
        for _ in range(100):
            equality = [rng.randrange(2, field.size) for _ in range(log_size)]
            challenges = [rng.randrange(2, field.size) for _ in range(log_size)]
            b = [rng.choice(embed) for _ in range(1 << log_size)]
            matrix, _ = multiplication_view_matrix(field, b, equality, challenges)
            expanded = [[coordinates[row[i]][limb] for i in positions] for row in matrix for limb in range(3)]
            histogram[small.rank(expanded)] += 1
        print(f"GF(4) padding / GF(64) challenges: N={1 << log_size}, padding={len(positions)}, target rank={6 * log_size}, ranks={dict(histogram)}")


def terminal_subfield_span():
    field, small, embed, coordinates = subfield_expansion()
    for point in product(range(2, field.size), repeat=2):
        weights = eq_weights(field, point)
        matrix = [[coordinates[x][limb] for x in weights] for limb in range(3)]
        assert (small.rank(matrix) == 3) == all(r not in embed for r in point)
    print("Cubic extension span: a two-dimensional Boolean subcube spans the extension exactly when both challenges are outside the base field")


def two_row_distance():
    field = Field(2, 0b111)
    distributions = []
    for secret_a, secret_b in ((0, 0), (1, 0)):
        distribution = Counter()
        for pad_a, pad_b in product(range(field.size), repeat=2):
            view, terminal_b, _ = multiplication_view_direct(field, [secret_a, pad_a], [secret_b, pad_b], [2], [2])
            distribution[view + (terminal_b,)] += 1
        distributions.append(distribution)
    left, right = distributions
    distance = sum(abs(left[key] - right[key]) for key in left.keys() | right.keys()) / (2 * field.size**2)
    assert distance == 0.75
    print(f"Two valid rows over GF(4), full zerocheck view: statistical distance {distance}")


def three_direction_terminal():
    field = Field(2, 0b111)
    weights = eq_weights(field, [2, 2])
    for secret_a, secret_b in product(range(field.size), repeat=2):
        outputs = Counter()
        for u, v, w in product(range(field.size), repeat=3):
            a = [secret_a, u, 0, w]
            b = [secret_b, 0, v, 1]
            c = [field.mul[x][y] for x, y in zip(a, b)]
            outputs[tuple(scalar_product(field, weights, values) for values in (a, b, c))] += 1
        assert len(outputs) == field.size**3 and set(outputs.values()) == {1}
    print("Three affine directions: valid padding makes all three terminal evaluations jointly uniform over GF(4)")


def multiplication_ranks():
    field = Field(8, 0x11B)
    rng = Random(0)
    for log_size, secret_rows in ((3, 1), (4, 1), (5, 8), (5, 16)):
        size = 1 << log_size
        pad = range(secret_rows, size)
        histogram = Counter()
        for _ in range(100):
            equality = [rng.randrange(2, field.size) for _ in range(log_size)]
            challenges = [rng.randrange(2, field.size) for _ in range(log_size)]
            b = [rng.randrange(field.size) for _ in range(size)]
            matrix, terminal_b = multiplication_view_matrix(field, b, equality, challenges)
            a = [rng.randrange(field.size) for _ in range(size)]
            direct, direct_b, direct_c = multiplication_view_direct(field, a, b, equality, challenges)
            assert tuple(scalar_product(field, row, a) for row in matrix) == direct
            assert terminal_b == direct_b
            assert simulated_terminal_c(field, direct, direct_b, equality, challenges) == direct_c
            rank = field.rank([[row[i] for i in pad] for row in matrix])
            histogram[rank] += 1
        print(f"GF(256) multiplication zerocheck: N={size}, secret={secret_rows}, target rank={2 * log_size}, ranks={dict(histogram)}")


def triangular_padding():
    def triangular(a):
        return a * (a - 1) // 2

    for bound in range(1, 65):
        maximum = triangular(bound)
        triangulars = {triangular(a): a for a in range(bound + 1)}
        pairs = {}
        for a in range(bound + 1):
            for b in range(bound + 1):
                value = triangular(a) + triangular(b)
                if value <= maximum:
                    pairs.setdefault(value, (a, b))
        for deficit in range(maximum + 1):
            completion = next(((a, *pairs[deficit - value]) for value, a in triangulars.items() if deficit - value in pairs), None)
            assert completion is not None
            assert sum(triangular(a) for a in completion) == deficit
            assert sum(completion) <= 3 * bound
    print("Abstract lookup completion: every deficit checked for read bounds 1..64 uses at most three fresh addresses and 3R reads")


def terminal_mask_rank():
    field = Field(8, 0x11B)
    size, fold_variables, tail_size = 64, 4, 4
    weights = eq_weights(field, [2, 3, 4, 5])
    matrix = [[weights[i % (1 << fold_variables)] if i // (1 << fold_variables) == tail else 0 for i in range(size)] for tail in range(tail_size)]
    prefix = list(range(8))
    distributed = [16 * tail + j for tail in range(tail_size) for j in range(2)]
    assert field.rank([[row[i] for i in prefix] for row in matrix]) == 1
    assert field.rank([[row[i] for i in distributed] for row in matrix]) == 4
    print("Low-variable folds to four plaintext coefficients: eight prefix masks have rank 1; two masks per surviving slice have rank 4")


if __name__ == "__main__":
    two_row_distance()
    three_direction_terminal()
    multiplication_ranks()
    comb_certificates()
    base_field_ranks()
    terminal_subfield_span()
    triangular_padding()
    terminal_mask_rank()
