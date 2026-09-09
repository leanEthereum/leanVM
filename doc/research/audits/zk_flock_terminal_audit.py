"""Linear terminal disclosures of Flock, excluding its batch zerocheck rounds."""

from fractions import Fraction
from random import Random
from types import FunctionType, SimpleNamespace

from zk_count_mixed_audit import echelon
from zk_flock_skip_audit import witness
from zk_pcs_audit import verifier_module
from zk_two_point_audit import error_bounds


def transpose_rows(verifier, row_weights):
    size, parents = 1 << 14, [None] * ((1 << 14) + 1)

    class Node:
        def __init__(self, index):
            self.index = index

        def __add__(self, other):
            if self.index == other.index:
                return zero
            if self.index == 0:
                return other
            if other.index == 0:
                return self
            parents.append((self.index, other.index))
            return Node(len(parents) - 1)

    zero = Node(0)
    walk = FunctionType(verifier.blake2s_row_values.__code__, {**verifier.__dict__, "ZERO": zero})
    outputs = walk([Node(index + 1) for index in range(size)])
    result = []
    for rows in outputs:
        adjoints = [verifier.ZERO] * len(parents)
        for node, value in zip(rows, row_weights):
            adjoints[node.index] += value
        for index in range(len(parents) - 1, size, -1):
            if adjoints[index] != verifier.ZERO:
                for parent in parents[index]:
                    adjoints[parent] += adjoints[index]
        result.append(adjoints[1 : size + 1])
    return result


def terminal_columns(verifier, point, challenge, alpha, lc_challenge):
    size = 1 << 14
    row_weights = [weight * value for weight in verifier.eq_kernel(challenge) for value in verifier.lagrange_weights(64, point)]
    left, right = transpose_rows(verifier, row_weights)
    columns = [int(a) | (int(b) << 192) | (int(c) << 384) for a, b, c in zip(left, right, row_weights)]
    public = [a + alpha * b + alpha**2 * c for a, b, c in zip(left, right, row_weights)]
    public[512] += alpha**3
    for round_index, coin in enumerate(lc_challenge):
        half = len(public) // 2
        weights = verifier.eq_kernel(list(reversed(lc_challenge[:round_index])))
        sums = [a + b for a, b in zip(public[:half], public[half:])]
        for index in range(size):
            prefix, low = divmod(index, 2 * half)
            branch, row = divmod(low, half)
            c0 = verifier.ZERO if branch else weights[prefix] * public[row]
            c2 = weights[prefix] * sums[row]
            columns[index] |= int(c0) << (192 * (3 + 2 * round_index))
            columns[index] |= int(c2) << (192 * (4 + 2 * round_index))
        public = [value + coin * delta for value, delta in zip(public[:half], sums)]
    weights = verifier.eq_kernel(list(reversed(lc_challenge)))
    for index in range(size):
        columns[index] |= int(weights[index >> 6]) << (192 * (19 + (index & 63)))
    return columns, public, row_weights


def apply_columns(verifier, columns, bits):
    result = 0
    while bits:
        lowest = bits & -bits
        result ^= columns[lowest.bit_length() - 1]
        bits ^= lowest
    mask = (1 << 64) - 1
    return [verifier.E(*(result >> (192 * output + 64 * limb) & mask for limb in range(3))) for output in range(83)]


def replay(verifier, values, public, point, challenge, alpha, lc_challenge, native=False):
    va, vb, vc = values[:3]
    claim = va + alpha * vb + alpha**2 * vc + alpha**3
    for coordinate, coin in enumerate(lc_challenge):
        c0, c2 = values[3 + 2 * coordinate : 5 + 2 * coordinate]
        claim = verifier.poly_eval([c0, claim + c2, c2], coin)
    assert claim == verifier.dot(public, values[19:])
    if native:
        scalars, coins = iter(values[3:]), iter([alpha, *lc_challenge])
        transcript = SimpleNamespace(
            next_scalar=lambda: next(scalars), next_scalars=lambda count: tuple(next(scalars) for _ in range(count)), sample=lambda: next(coins)
        )
        transcript.sumcheck_round_poly = lambda count, claim, eq: verifier.Transcript.sumcheck_round_poly(transcript, count, claim, eq)
        terminal = verifier.ZerocheckResult(point, tuple(challenge), va, vb, vc)
        recovered_point, slices = verifier.verify_flock_lincheck(terminal, transcript)
        assert recovered_point == tuple(reversed(lc_challenge)) and slices == tuple(values[19:])


def bound_certificate():
    terminal_degree = 3 * 71 + sum(2 * (73 + 2 * index) for index in range(8)) + 64 * 8 - (73 + 2 * 7)
    assert terminal_degree == 1918
    _, span, _ = error_bounds()
    assert span + Fraction(2205 + terminal_degree + 28 + 1, 1 << 192) < Fraction(1, 1 << 148)
    print("Joint endpoint bound: two-point span error plus 4152/2^192, below 2^-148", flush=True)


def simulator_certificate(verifier, public, point, challenge, alpha, lc_challenge, rng):
    for _ in range(2):
        values = [verifier.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(83)]
        claim = values[0] + alpha * values[1] + alpha**2 * values[2] + alpha**3
        for coordinate, coin in enumerate(lc_challenge[:7]):
            c0, c2 = values[3 + 2 * coordinate : 5 + 2 * coordinate]
            claim = verifier.poly_eval([c0, claim + c2, c2], coin)
        coin = lc_challenge[7]
        values[17] = verifier.dot(public, values[19:]) + coin * claim + (coin + coin**2) * values[18]
        replay(verifier, values, public, point, challenge, alpha, lc_challenge, native=True)
    print("Uniform free terminal coordinates and the reconstructed last constant pass the reference lincheck verifier", flush=True)


def audit(verifier):
    library_rng, terminal_rng = Random(152), Random(153)
    sample = lambda rng: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    point, challenge = sample(library_rng), [sample(library_rng) for _ in range(8)]
    messages = [[library_rng.getrandbits(32) for _ in range(16)] for _ in range(128)]
    alpha, lc_challenge = sample(terminal_rng), [sample(terminal_rng) for _ in range(8)]
    columns, public, row_weights = terminal_columns(verifier, point, challenge, alpha, lc_challenge)
    base = apply_columns(verifier, columns, witness(verifier, [0] * 16)[0])
    replay(verifier, base, public, point, challenge, alpha, lc_challenge, native=True)
    differences = []
    for index, message in enumerate(messages):
        z, a, b = witness(verifier, message)
        values = apply_columns(verifier, columns, z)
        assert values[0] == verifier.E.sum(weight for bit, weight in enumerate(row_weights) if a >> bit & 1)
        assert values[1] == verifier.E.sum(weight for bit, weight in enumerate(row_weights) if b >> bit & 1)
        assert values[2] == verifier.E.sum(weight for bit, weight in enumerate(row_weights) if z >> bit & 1)
        replay(verifier, values, public, point, challenge, alpha, lc_challenge, native=index in (0, 127))
        difference = [x + y for x, y in zip(values, base)]
        differences.append(difference[:17] + difference[18:])
        if index % 16 == 15:
            print(f"Verified {index + 1} terminal feature directions", flush=True)
    rank = len(echelon(verifier, differences))
    print(f"Terminal observations with final lincheck constant removed: extension rank {rank}/82", flush=True)
    assert rank == 82
    simulator_certificate(verifier, public, point, challenge, alpha, lc_challenge, terminal_rng)
    bound_certificate()


if __name__ == "__main__":
    audit(verifier_module())
