"""Joint scalar-zerocheck and linear-opening experiments, not a PCS implementation."""

from collections import Counter
from fractions import Fraction
from itertools import combinations
from random import Random

from zk_padding_experiments import (
    Field,
    comb_positions,
    eq_weights,
    multiplication_view_matrix,
)


def novel_weights(field, log_size, point):
    weights = [1]
    for j in range(log_size):
        numerator = denominator = 1
        for root in range(1 << j):
            numerator = field.mul[numerator][point ^ root]
            denominator = field.mul[denominator][(1 << j) ^ root]
        value = field.mul[numerator][field.inv[denominator]]
        weights += [field.mul[x][value] for x in weights]
    return weights


def linear_opening_rows(field, log_size, query_points, fold_point, tail_log):
    size = 1 << log_size
    rows = [novel_weights(field, log_size, point) for point in query_points]
    weights = eq_weights(field, fold_point)
    folded_size = 1 << (log_size - tail_log)
    for tail in range(1 << tail_log):
        rows.append([weights[i % folded_size] if i // folded_size == tail else 0 for i in range(size)])
    return rows


def joint_matrix(field, b, equality, challenges, linear_rows):
    matrix, _ = multiplication_view_matrix(field, b, equality, challenges)
    return matrix + linear_rows + [[field.mul[x][y] for x, y in zip(row, b)] for row in linear_rows]


def opening_ranks():
    field = Field(8, 0x11B)
    rng = Random(5)
    for pattern in ("comb", "prefix", "sliced-comb"):
        log_size, tail_log = 6, 2
        size = 1 << log_size
        if pattern == "comb":
            padding = comb_positions(log_size)
        elif pattern == "prefix":
            padding = list(range(32))
        else:
            padding = [16 * tail + i for tail in range(4) for i in comb_positions(4)]
        ranks = Counter()
        for _ in range(100):
            equality = [rng.randrange(2, field.size) for _ in range(log_size)]
            challenges = [rng.randrange(2, field.size) for _ in range(log_size)]
            b = [rng.randrange(field.size) for _ in range(size)]
            queries = rng.sample(range(64, 128), 2)
            linear = linear_opening_rows(field, log_size, queries, [rng.randrange(2, field.size) for _ in range(4)], tail_log)
            matrix = joint_matrix(field, b, equality, challenges, linear)
            ranks[(field.rank(matrix), field.rank([[row[i] for i in padding] for row in matrix]))] += 1
        print(f"Joint zerocheck, two RS queries, four final coefficients: {pattern}, masks={len(padding)}, (full,padded) ranks={dict(ranks)}")


def joint_certificates():
    field = Field(8, 0x11B)
    log_size = 6
    padding = [16 * tail + i for tail in range(4) for i in comb_positions(4)]
    rng = Random(6)
    for queries in ([64, 65], [0, 64]):
        equality = [rng.randrange(2, field.size) for _ in range(log_size)]
        challenges = [rng.randrange(2, field.size) for _ in range(log_size)]
        b = [rng.randrange(field.size) if i in padding else 0 for i in range(64)]
        linear = linear_opening_rows(field, log_size, queries, [rng.randrange(2, field.size) for _ in range(4)], 2)
        matrix = joint_matrix(field, b, equality, challenges, linear)
        rank = field.rank([[row[i] for i in padding] for row in matrix])
        target = 2 * log_size + 2 * len(linear)
        if queries[0] == 0:
            assert rank < target
            # Expose the random row at zero, then omit its redundant a/c readouts.
            retained = [i for i in range(len(matrix)) if i not in (2 * log_size, 2 * log_size + len(linear))]
            remaining_padding = [i for i in padding if i != 0]
            assert field.rank([[matrix[j][i] for i in remaining_padding] for j in retained]) == target - 2
            b_rows = [eq_weights(field, challenges)] + linear[1:]
            assert field.rank([[row[i] for i in remaining_padding] for row in b_rows]) == len(b_rows)
            print("Query at zero: full-uniformity criterion fails; conditioning on the valid random padding triple restores residual full rank")
        else:
            assert rank == target
            b_rows = [eq_weights(field, challenges)] + linear
            assert field.rank([[row[i] for i in padding] for row in b_rows]) == len(b_rows)
            print("Joint certificate: zero-real-b minor has rank 24; terminal/opened b map has rank 7")


def weighted_rows(field, weights, rows):
    out = [0] * len(rows[0])
    for weight, row in zip(weights, rows):
        if weight:
            out = [x ^ field.mul[weight][y] for x, y in zip(out, row)]
    return out


def whir_linear_view(field, log_size, rng, query_count=2, forced_query=None):
    """Scalar linear view of a small WHIR instance, including all revealed leaves.

    This models the documented algebraic schedule: two high-coordinate folds,
    then one low-coordinate fold per level, stopping at four plaintext values.
    Hashes are omitted. The returned rows act on the original message vector.
    Separate introduction polynomials are omitted; zk_pcs_audit.py covers them.
    """
    size = 1 << log_size
    order = list(range(log_size - 2, log_size)) + list(range(log_size - 2))
    permutation = [sum(((i >> j) & 1) << bit for j, bit in enumerate(order)) for i in range(size)]
    current = [[int(i == j) for j in range(size)] for i in permutation]
    initial_weights = eq_weights(field, [rng.randrange(2, field.size) for _ in range(log_size)])
    claims = [[initial_weights[i] for i in permutation]]
    observations = [initial_weights]
    remaining = log_size
    level = 0
    while remaining > 2:
        folded = 2 if level == 0 else 1
        lanes = 1 << folded
        code_log = remaining - folded
        before = current
        beta = rng.randrange(2, field.size)
        power = 1
        weights = [0] * len(current)
        for claim in claims:
            weights = [x ^ field.mul[power][y] for x, y in zip(weights, claim)]
            power = field.mul[power][beta]
        for _ in range(folded):
            lo, hi = current[::2], current[1::2]
            wlo, whi = weights[::2], weights[1::2]
            observations.append(weighted_rows(field, wlo, lo))
            differences = [[x ^ y for x, y in zip(a, b)] for a, b in zip(lo, hi)]
            observations.append(weighted_rows(field, [a ^ b for a, b in zip(wlo, whi)], differences))
            r = rng.randrange(2, field.size)
            current = [[x ^ field.mul[r][y] for x, y in zip(a, difference)] for a, difference in zip(lo, differences)]
            weights = [a ^ field.mul[r][a ^ b] for a, b in zip(wlo, whi)]
        remaining -= folded
        if remaining > 2:
            ood = eq_weights(field, [rng.randrange(2, field.size) for _ in range(remaining)])
            observations.append(weighted_rows(field, ood, current))
            claims = [weights, ood]
        queries = [rng.randrange(1 << (code_log + 1)) for _ in range(query_count)]
        if forced_query is not None:
            queries[0] = forced_query
        for point in queries:
            code_weights = novel_weights(field, code_log, point)
            for lane in range(lanes):
                observations.append(weighted_rows(field, code_weights, before[lane::lanes]))
            if remaining > 2:
                claims.append(code_weights)
        if remaining == 2:
            observations += current
        level += 1
    return observations


def whir_ranks():
    field = Field(8, 0x11B)
    for log_size in (6, 7):
        size = 1 << log_size
        # Four final slices inside each of the four initial lanes.
        region = size // 16
        patterns = {
            "half-prefix": list(range(size // 2)),
            "half-per-slice": [region * block + i for block in range(16) for i in range(region // 2)],
            "even-parity": [i for i in range(size) if i.bit_count() % 2 == 0],
        }
        for name, padding in patterns.items():
            rng = Random(8)
            ranks = Counter()
            for _ in range(20):
                matrix = whir_linear_view(field, log_size, rng)
                ranks[(field.rank(matrix), field.rank([[row[i] for i in padding] for row in matrix]))] += 1
            print(f"WHIR scalar linear view N={size}, {name}, masks={len(padding)}, (full,padded) ranks={dict(ranks)}")


def witness_leak(field, matrix, padding):
    """Return coefficients of an observed linear combination annihilating padding."""
    width = len(matrix[0])
    outside = [i for i in range(width) if i not in padding]
    rows = [row[:] + [int(i == j) for j in range(len(matrix))] for i, row in enumerate(matrix)]
    rank = 0
    for col in padding:
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        rows[rank] = [field.mul[field.inv[rows[rank][col]]][x] for x in rows[rank]]
        for i in range(rank + 1, len(rows)):
            coefficient = rows[i][col]
            rows[i] = [x ^ field.mul[coefficient][y] for x, y in zip(rows[i], rows[rank])]
        rank += 1
    for row in rows[rank:]:
        if any(row[i] for i in outside):
            coefficients = row[width:]
            assert weighted_rows(field, coefficients, matrix) == row[:width]
            assert all(row[i] == 0 for i in padding)
            return coefficients, row[:width]
    return None


def whir_leak_certificate():
    field = Field(8, 0x11B)
    matrix = whir_linear_view(field, 6, Random(8))
    padding = [4 * block + i for block in range(16) for i in range(2)]
    result = witness_leak(field, matrix, padding)
    assert result is not None
    coefficients, leak = result
    real_index = next(i for i, coefficient in enumerate(leak) if coefficient)
    for bit in (0, 1):
        message = [0] * 64
        message[real_index] = bit
        for i in padding:
            message[i] = (7 * i) % 256
        view = [sum_in_field(field, row, message) for row in matrix]
        assert sum_in_field(field, coefficients, view) == field.mul[bit][leak[real_index]]
    print("WHIR obstruction certified: an explicit linear combination of observations cancels every per-slice prefix mask and retains real data")


def sum_in_field(field, row, message):
    result = 0
    for a, b in zip(row, message):
        result ^= field.mul[a][b]
    return result


def adaptive_linear_simulation():
    field = Field(2, 0b111)
    # A four-cell vector: two real entries followed by two uniform masks.
    # Second query is chosen from the first answer, with invertible mask columns.
    for secret in ((0, 0), (1, 0), (2, 3)):
        views = Counter()
        for u in range(4):
            for v in range(4):
                first = secret[0] ^ u
                second = secret[1] ^ field.mul[first][u] ^ v
                views[(first, second)] += 1
        assert len(views) == 16 and set(views.values()) == {1}
    print("Adaptive linear-query simulator: exhaustive GF(4) example matches uniform answers for every tested real vector")


def discrete_query_certificates():
    field = Field(4, 0x13)
    size, domain_size = 4, 8
    views = []
    for secret in (0, 1):
        view = Counter()
        for position in range(size):
            for mask in range(field.size):
                message = [secret] * size
                message[position] = mask
                for query in range(domain_size):
                    answer = sum_in_field(field, novel_weights(field, 2, query), message)
                    view[(query, answer)] += 1
        views.append(view)
    total = sum(views[0].values())
    zero_query_distance = Fraction(sum(abs(views[0][0, answer] - views[1][0, answer]) for answer in range(field.size)), 2 * total)
    assert zero_query_distance == Fraction(size - 1, size * domain_size)
    print(f"Random sprinkling: the query-zero event alone contributes exact statistical distance {zero_query_distance}")
    weights = [novel_weights(field, 3, point) for point in range(field.size)]
    for query_count in range(1, 5):
        for points in combinations(range(field.size), query_count):
            assert field.rank([weights[point][:4] for point in points]) == query_count
    print("Low-degree prefix: four masks hide every set of at most four distinct GF(16) evaluation queries, exhaustively checked")


if __name__ == "__main__":
    opening_ranks()
    joint_certificates()
    whir_ranks()
    whir_leak_certificate()
    adaptive_linear_simulation()
    discrete_query_certificates()
