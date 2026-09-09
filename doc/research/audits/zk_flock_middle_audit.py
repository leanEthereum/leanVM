"""Sparse Flock batch rounds: two endpoint identities and the remaining rank."""

from fractions import Fraction
from random import Random

from zk_count_full_head_audit import weight
from zk_count_mixed_audit import echelon
from zk_flock_prefix_audit import prefix
from zk_flock_skip_audit import skip_halves, tables, witness
from zk_pcs_audit import verifier_module
from zk_two_point_audit import SPARSE_TWO, error_bounds


def pack_values(values):
    return sum(int(value) << (192 * index) for index, value in enumerate(values))


def unpack_values(verifier, packed, count):
    mask = (1 << 64) - 1
    return [verifier.E(*(packed >> (192 * index + 64 * limb) & mask for limb in range(3))) for index in range(count)]


def local_columns(verifier, equality, challenge, support):
    result = []
    for index in support:
        values = []
        for coordinate in range(len(challenge)):
            low = weight(verifier, challenge[:coordinate], index)
            high = weight(verifier, equality[coordinate + 1 :], index >> (coordinate + 1))
            values.extend((high * low, high * low**2))
        first, second = weight(verifier, equality, index), weight(verifier, challenge, index)
        assert verifier.dot([a + b for a, b in zip(equality, challenge)], values[::2]) == first + second
        assert verifier.dot([a + b**2 for a, b in zip(equality, challenge)], values[1::2]) == first + second**2
        result.append((int(first) | (int(second) << 192), pack_values(values)))
    return result


def endpoint_kernel(columns):
    pivots, residuals = {}, []
    for endpoint, message in columns:
        while endpoint:
            bit = endpoint.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = endpoint, message
                break
            previous_endpoint, previous_message = pivots[bit]
            endpoint ^= previous_endpoint
            message ^= previous_message
        if endpoint == 0:
            residuals.append(message)
    return len(pivots), residuals


def field_triple(verifier, packed, row_weights):
    result = []
    for value in packed:
        folded = 0
        while value:
            bit = value & -value
            folded ^= row_weights[bit.bit_length() - 1]
            value ^= bit
        result.append(unpack_values(verifier, folded, 1)[0])
    return result


def local_replay(verifier):
    rng = Random(155)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    point, within = sample(), [sample() for _ in range(8)]
    weights = [int(high * low) for high in verifier.eq_kernel(within) for low in verifier.lagrange_weights(64, point)]
    baseline = field_triple(verifier, witness(verifier, [0] * 16), weights)
    choices = [field_triple(verifier, witness(verifier, [rng.getrandbits(32) for _ in range(16)]), weights) for _ in range(4)]
    equality, challenge = ([sample() for _ in range(5)] for _ in range(2))
    tags = verifier.eq_kernel(equality[3:])
    local = [unpack_values(verifier, message, 6) for _, message in local_columns(verifier, equality[:3], challenge[:3], range(8))]
    bit_columns = []
    cc, aa, bb = baseline
    for tag, (c, a, b) in zip(tags, choices):
        da, db, dc = a + aa, b + bb, c + cc
        beta, gamma = aa * db + bb * da + dc, da * db
        bit_columns.extend(pack_values([tag * (beta if index % 2 == 0 else gamma) * value for index, value in enumerate(values)]) for values in local)

    def view(bits):
        rows = [choices[index // 8] if bits >> index & 1 else baseline for index in range(32)]
        wire = []
        for coordinate, coin in enumerate(challenge[:3]):
            q1, q2 = verifier.ZERO, verifier.ZERO
            for pair, scale in enumerate(verifier.eq_kernel(equality[coordinate + 1 :])):
                c0, a0, b0 = rows[2 * pair]
                c1, a1, b1 = rows[2 * pair + 1]
                da, db, dc = a0 + a1, b0 + b1, c0 + c1
                q1 += scale * (a0 * db + b0 * da + dc)
                q2 += scale * da * db
            wire.extend((q1, q2))
            rows = [tuple(a + coin * (a + b) for a, b in zip(rows[2 * pair], rows[2 * pair + 1])) for pair in range(len(rows) // 2)]
        return pack_values(wire)

    bits = rng.getrandbits(32)
    before = view(bits)
    for selected in ((0,), (9,), (18,), (27,), (0, 1, 9, 18, 23, 31)):
        changed, expected = bits, 0
        for bit in selected:
            changed ^= 1 << bit
            expected ^= bit_columns[bit]
        assert view(changed) ^ before == expected
    print("Single and joint flips of actual compression choices match the local sparse-round columns", flush=True)


def library_certificate(verifier):
    rng = Random(152)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    point, challenge = sample(), [sample() for _ in range(8)]
    messages = [[rng.getrandbits(32) for _ in range(16)] for _ in range(128)]
    lookup = tables(verifier)
    row_weights = [int(high * low) for high in verifier.eq_kernel(challenge) for low in verifier.lagrange_weights(64, point)]
    baseline = witness(verifier, [0] * 16)
    cc, aa, bb = field_triple(verifier, baseline, row_weights)
    equality = [*verifier.FIXED_CHALLENGES, verifier.ZERO]
    base = prefix(verifier, baseline, skip_halves(verifier, baseline, lookup), equality, point, challenge)
    extended, directions = [], []
    for index, message in enumerate(messages):
        triple = witness(verifier, message)
        c, a, b = field_triple(verifier, triple, row_weights)
        da, db, dc = a + aa, b + bb, c + cc
        beta, gamma = aa * db + bb * da + dc, da * db
        values = prefix(verifier, triple, skip_halves(verifier, triple, lookup), equality, point, challenge)
        difference = [x + y for x, y in zip(values, base)]
        running = verifier.lagrange_interpolate(128, [verifier.ZERO] * 64 + difference[:64], point)
        for coordinate, coin in enumerate(challenge):
            q1, q2 = difference[64 + 2 * coordinate : 66 + 2 * coordinate]
            running += (equality[coordinate] + coin) * q1 + (equality[coordinate] + coin**2) * q2
        assert running == beta + gamma
        extended.append([*difference[:63], *difference[64:], beta])
        directions.append((beta, gamma))
        if index % 16 == 15:
            print(f"Constructed {index + 1} actual compression cofactor pairs", flush=True)
    rank = len(echelon(verifier, extended))
    print(f"Prefix plus the separate linear cofactor: extension rank {rank}/80", flush=True)
    assert rank == 80
    _, span, _ = error_bounds()
    assert span + Fraction(2205 + 142 + 1918 + 28 + 1, 1 << 192) < Fraction(1, 1 << 148)
    print("Adding the auxiliary cofactor to the joint endpoint theorem costs a degree-142 row; total bound remains below 2^-148", flush=True)
    return directions


def conditional_rank(verifier, directions):
    rng = Random(154)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    equality, challenge = ([sample() for _ in range(14)] for _ in range(2))
    tags = verifier.eq_kernel([sample() for _ in range(7)])
    assert all(tags)
    rank, packed = endpoint_kernel(local_columns(verifier, equality, challenge, SPARSE_TWO))
    assert (rank, len(packed)) == (384, 192)
    residuals = [unpack_values(verifier, value, 28) for value in packed]
    first_relation = [a + b for a, b in zip(equality, challenge)]
    second_relation = [a + b**2 for a, b in zip(equality, challenge)]
    assert any(first_relation) and any(second_relation)
    for values in residuals:
        assert verifier.dot(first_relation, values[::2]) == verifier.ZERO
        assert verifier.dot(second_relation, values[1::2]) == verifier.ZERO
    pivots = {}
    for bank, ((beta, gamma), tag) in enumerate(zip(directions, tags)):
        scales = tag * beta, tag * gamma
        for values in residuals:
            packed = pack_values([scales[index % 2] * value for index, value in enumerate(values)])
            while packed:
                bit = packed.bit_length() - 1
                if bit not in pivots:
                    pivots[bit] = packed
                    break
                packed ^= pivots[bit]
        if bank % 8 == 7 or len(pivots) == 26 * 192:
            print(f"After {bank + 1} banks: conditional sparse-round binary rank {len(pivots)}/4992", flush=True)
        if len(pivots) == 26 * 192:
            break
    assert len(pivots) == 26 * 192
    print("The stronger 27-field target given all two-point evaluations is impossible here: two exact relations remain, not one", flush=True)
    print("This is a finite rank certificate for the canonical completion, not a uniform probability bound or a transcript distinguisher", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    local_replay(verifier)
    conditional_rank(verifier, library_certificate(verifier))
