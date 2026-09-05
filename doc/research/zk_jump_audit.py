"""Conditional JUMP sumcheck certificates, excluding a full VM simulator."""

import argparse
from fractions import Fraction
from random import Random

from zk_pcs_audit import Tower, edot, verifier_module
from zk_stacked_audit import binary_basis


def inverse_message_map(field, condition, padding, equality, challenges):
    """Cofactor coordinates: first quadratic term, then value at one and quadratic."""
    assert all(condition[i] == 0 for i in padding)
    condition = list(condition)
    factors = [1] * len(padding)
    rows = []
    for coordinate in reversed(range(len(challenges))):
        half = len(condition) // 2
        weights = field.eq(equality[:coordinate])
        at_one, quadratic = [], []
        for index, factor in zip(padding, factors):
            low = index % half
            weight = field.mul(factor, weights[low])
            at_one.append(field.mul(weight, condition[low + half]) if index & half else 0)
            quadratic.append(field.mul(weight, condition[low] ^ condition[low + half]))
        if rows:
            rows.append(at_one)
        else:
            assert not any(at_one)
        rows.append(quadratic)
        coin = challenges[coordinate]
        condition = [lo ^ field.mul(coin, lo ^ hi) for lo, hi in zip(condition[:half], condition[half:])]
        factors = [field.mul(factor, coin if index & half else 1 ^ coin) for index, factor in zip(padding, factors)]
    return rows, factors, condition[0]


def jump_view(field, condition, flag, inverse, equality, challenges, batch):
    columns = [list(column) for column in (condition, flag, inverse)]
    messages = []
    for coordinate in reversed(range(len(challenges))):
        c, b, w = columns
        half, weights = len(c) // 2, field.eq(equality[:coordinate])
        at_one = quadratic = 0
        for i, weight in enumerate(weights):
            upper = i + half
            value = b[upper] ^ field.mul(c[upper], w[upper]) ^ field.mul(batch, field.mul(c[upper], b[upper] ^ 1))
            slope_c, slope_b, slope_w = c[i] ^ c[upper], b[i] ^ b[upper], w[i] ^ w[upper]
            square = field.mul(slope_c, slope_w) ^ field.mul(batch, field.mul(slope_c, slope_b))
            at_one ^= field.mul(weight, value)
            quadratic ^= field.mul(weight, square)
        if messages:
            messages.append(at_one)
        else:
            assert at_one == 0
        messages.append(quadratic)
        coin = challenges[coordinate]
        columns = [[lo ^ field.mul(coin, lo ^ hi) for lo, hi in zip(column[:half], column[half:])] for column in columns]
    return messages, tuple(column[0] for column in columns)


def parity_bank(field, log_size, rng):
    size = 1 << log_size
    padding = [i for i in range(3 * size // 4) if i.bit_count() % 2 == 0]
    condition = [0 if i in padding else rng.randrange(1, 1 << field.bits) for i in range(size)]
    return condition, padding


def einv(field, value):
    assert value
    result, power = 1, (1 << (3 * field.bits)) - 2
    while power:
        if power & 1:
            result = field.mul(result, value)
        value = field.mul(value, value)
        power >>= 1
    return result


def penultimate(field, column, challenges):
    column = list(column)
    for coin in reversed(challenges[1:]):
        half = len(column) // 2
        column = [lo ^ field.mul(coin, lo ^ hi) for lo, hi in zip(column[:half], column[half:])]
    return tuple(column)


def reconstruct(field, free_messages, c_pair, b_pair, equality, challenges, batch):
    c0, c1 = c_pair
    root = field.mul(c0, einv(field, c0 ^ c1))
    at_root = b_pair[0] ^ field.mul(root, b_pair[0] ^ b_pair[1])
    messages, wire, cursor, claim, factor = [], [], 0, 0, 1
    for round_index, coordinate in enumerate(reversed(range(len(challenges)))):
        at_one = 0 if round_index == 0 else free_messages[cursor]
        cursor += int(round_index != 0)
        r, coin = equality[coordinate], challenges[coordinate]
        at_zero = field.mul(claim ^ field.mul(r, at_one), einv(field, 1 ^ r))
        if coordinate:
            quadratic = free_messages[cursor]
            cursor += 1
        else:
            quadratic = field.mul(at_root ^ at_zero ^ field.mul(at_zero ^ at_one, root), einv(field, field.mul(root, 1 ^ root)))
        if round_index:
            messages.append(at_one)
        messages.append(quadratic)
        linear = at_zero ^ at_one ^ quadratic
        wire.append(
            (field.mul(factor, field.mul(1 ^ r, at_zero)), field.mul(factor, linear ^ field.mul(1 ^ r, quadratic)), field.mul(factor, quadratic))
        )
        claim = at_zero ^ field.mul(coin, linear ^ field.mul(coin, quadratic))
        factor = field.mul(factor, 1 ^ r ^ coin)
    assert cursor == len(free_messages)
    condition = c0 ^ field.mul(challenges[0], c0 ^ c1)
    flag = b_pair[0] ^ field.mul(challenges[0], b_pair[0] ^ b_pair[1])
    inverse = field.mul(claim ^ flag, einv(field, condition)) ^ field.mul(batch, flag ^ 1)
    return messages, (condition, flag, inverse), wire


def replay_sumcheck(verifier, wire, equality, challenges, terminal, batch):
    ext = lambda value: verifier.E(*(value >> (64 * i) & ((1 << 64) - 1) for i in range(3)))

    class Replay:
        def __init__(self):
            self.stream = iter(value for row in wire for value in row)
            self.coins = iter(reversed(challenges))

        def next_scalar(self):
            return ext(next(self.stream))

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            return ext(next(self.coins))

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    point, claim = verifier.sumcheck(Replay(), verifier.ZERO, 4, [None] * len(challenges))
    c, b, w = map(ext, terminal)
    eq = verifier.eq_eval(list(map(ext, equality)), list(reversed(point)))
    assert claim == eq * (b + c * w + ext(batch) * c * (b + verifier.ONE))
    print("Reference replay: reconstructed synthetic cubic messages pass the actual Python sumcheck and JUMP terminal identity", flush=True)


def endpoint_certificate(verifier):
    field, rng = Tower(64, verifier), Random(52)
    point = [field.random(rng) for _ in range(14)]
    low, high = field.eq(point[:12]), field.eq(point[12:])
    positions = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    directions = []
    for parity in (0, 1):
        for group, condition in enumerate((1, int(verifier.GEN))):
            for index in positions:
                weight = field.mul(high[group], low[index])
                directions.append((field.mul(condition, weight) << (192 * parity)) | (weight << (192 * (parity + 2))))
    assert len(binary_basis(directions)) == 4 * 192
    print("Four-endpoint cycle bank: actual-field binary rank 768 for (C0, C1, B0, B1)", flush=True)


def combined_layout(field, generator, mode, seed):
    rng, size = Random(seed), 1 << 15
    sparse = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
    families = {parity + 2 * index + 8192 * group: group for parity in (0, 1) for index in sparse for group in (0, 1)}
    eligible = [i for i in range(3 * size // 4) if i not in families and i.bit_count() % 2 == 0]
    bank = list(range(8576, 8581))
    padding = sorted(Random(70).sample([i for i in eligible if i not in bank], 251) + bank)
    zeros = set(padding)
    condition = [0 if i in zeros else 1 for i in range(size)]
    for index, group in families.items():
        condition[index] = (generator if group else 1) * rng.randrange(2)
    for index in range(3 * size // 4, size):
        condition[index] = {"zero": 0, "one": 1, "generator": generator}.get(mode, rng.randrange(1 << field.bits))
    for index in range(24960, 24966):
        condition[index] = 1
    return condition, padding, families


def combined_certificates(verifier, actual):
    field = Tower(64 if actual else 8, verifier)
    generator = int(verifier.GEN) if actual else 2
    for mode in ("zero", "one", "generator", "random"):
        condition, padding, families = combined_layout(field, generator, mode, 71)
        rng = Random(72)
        equality = [field.random(rng) for _ in range(15)]
        challenges = [field.random(rng) for _ in range(15)]
        matrix, _, _ = inverse_message_map(field, condition, padding, equality, challenges)
        rank = len(field.pivots(field.expand(matrix[:-1])))
        assert rank == 84
        assert len(families) == 1792 and not set(padding).intersection(families)
        return_rows = [i for i in range(3 * len(condition) // 4) if i not in families and i not in padding and condition[i] == 1]
        assert len(return_rows) >= len(families) + len(padding)
        print(f"Combined layout: K=2^{field.bits}, real={mode}, 1792 flag rows and 256 fixed inverse positions, rank={rank}/84", flush=True)


def complete_bank_layout(field, high_rounds, tag_bits):
    assert high_rounds >= 4
    tail = [0, 1] + [index for bit in range(1, tag_bits) for index in (1 << bit, (1 << bit) + 1)]
    groups = [group for group in range(1 << (tag_bits - 3)) if not set(range(8 * group, 8 * group + 5)).intersection(tail)]
    assert len(groups) >= high_rounds - 1
    banks, scales, padding = {}, {}, []
    for active, group in zip(range(tag_bits + 1, tag_bits + high_rounds), groups):
        for tag in range(8 * group, 8 * group + 5):
            banks[tag], scales[tag] = active, 1
            padding += [tag, tag + (1 << (active - 1))]
    for tag in tail:
        banks[tag] = tag_bits
        scales[tag] = 1 if tag in (0, 1) or tag % 2 == 0 else 2
        padding += [tag + (replica << (tag_bits + 1)) for replica in range(5)]
    assert len(padding) == len(set(padding)) == 10 * (high_rounds - 1) + 10 * tag_bits
    return banks, scales, padding


def structured_bank_map(field, high_rounds, tag_bits, equality, challenges, outside):
    size = high_rounds + tag_bits
    banks, scales, padding = complete_bank_layout(field, high_rounds, tag_bits)
    low_weights = []
    for index in padding:
        weights = [1]
        for coordinate, value in enumerate(equality):
            weights.append(field.mul(weights[-1], value if index >> coordinate & 1 else 1 ^ value))
        low_weights.append(weights)
    boundary = [field.mul(scales[tag], challenges[banks[tag]]) if tag in banks else outside[tag] for tag in range(1 << tag_bits)]
    condition, factors, rows = list(boundary), [1] * len(padding), []
    for coordinate in reversed(range(size)):
        half = 1 << coordinate
        at_one, quadratic = [], []
        for cursor, index in enumerate(padding):
            weight = field.mul(factors[cursor], low_weights[cursor][coordinate])
            if coordinate >= tag_bits:
                active = banks[index % (1 << tag_bits)]
                scale = scales[index % (1 << tag_bits)]
                upper = field.mul(scale, challenges[active]) if active > coordinate else scale if active == coordinate else 0
                slope = scale if active == coordinate else 0
            else:
                low = index % half
                upper = condition[low + half]
                slope = condition[low] ^ upper
            at_one.append(field.mul(weight, upper) if index & half else 0)
            quadratic.append(field.mul(weight, slope))
        if rows:
            rows.append(at_one)
        else:
            assert not any(at_one)
        rows.append(quadratic)
        coin = challenges[coordinate]
        factors = [field.mul(factor, coin if index & half else 1 ^ coin) for index, factor in zip(padding, factors)]
        if coordinate < tag_bits:
            condition = [lo ^ field.mul(coin, lo ^ hi) for lo, hi in zip(condition[:half], condition[half:])]
    return rows, padding, banks, boundary


def structured_certificates(verifier, actual):
    field, rng = Tower(64 if actual else 8, verifier), Random(81)
    high_rounds, tag_bits = 12, 8
    size = high_rounds + tag_bits
    equality = [field.random(rng) for _ in range(size)]
    challenges = [field.random(rng) for _ in range(size)]
    for mode in ("zero", "one", "random"):
        outside = [0 if mode == "zero" else 1 if mode == "one" else field.random(rng) for _ in range(1 << tag_bits)]
        matrix, padding, _, _ = structured_bank_map(field, high_rounds, tag_bits, equality, challenges, outside)
        prefix = matrix[: 2 * high_rounds - 2]
        prefix_rank = len(field.pivots(field.expand(prefix)))
        full_rank = len(field.pivots(field.expand(matrix[:-1])))
        assert prefix_rank == 3 * (2 * high_rounds - 2)
        assert full_rank == 3 * (2 * size - 2)
        print(f"Structured banks: K=2^{field.bits}, outside={mode}, masks={len(padding)}, prefix={prefix_rank}/66, full={full_rank}/114", flush=True)
    if actual:
        high_weights = field.eq(challenges[tag_bits:])
        selectors = field.eq(challenges[1:tag_bits])
        sparse = list(range(64)) + [i | (1 << j) for j in range(6, 12) for i in range(64)]
        directions = []
        banks, _, padding = complete_bank_layout(field, high_rounds, tag_bits)
        for tag, scale in ((6, 1), (7, 1), (10, 2), (11, 2)):
            assert tag not in banks
            for index in sparse:
                weight = field.mul(selectors[tag >> 1], high_weights[index])
                parity = tag % 2
                directions.append((field.mul(scale, weight) << (192 * parity)) | (weight << (192 * (parity + 2))))
        assert len(binary_basis(directions)) == 768
        assert 12 not in banks and len(banks) * (1 << high_rounds) + 2 * len(directions) == 294400
        print("Complete endpoint layout: binary rank 768, disjoint plane/endpoint/return rows, total reserved rows 294400", flush=True)
        endpoints = [field.random(rng) for _ in range(4)]
        batch = field.random(rng)
        fake = [field.random(rng) for _ in range(2 * size - 2)]
        _, terminal, wire = reconstruct(field, fake, endpoints[:2], endpoints[2:], equality, challenges, batch)
        replay_sumcheck(verifier, wire, equality, challenges, terminal, batch)
    high_rounds, tag_bits = 4, 6
    size = high_rounds + tag_bits
    equality, challenges = equality[:size], challenges[:size]
    outside = [0] * (1 << tag_bits)
    matrix, padding, banks, _ = structured_bank_map(field, high_rounds, tag_bits, equality, challenges, outside)
    _, scales, _ = complete_bank_layout(field, high_rounds, tag_bits)
    condition = [
        scales[index % (1 << tag_bits)] * ((index >> banks[index % (1 << tag_bits)]) & 1) if index % (1 << tag_bits) in banks else 0
        for index in range(1 << size)
    ]
    dense, _, _ = inverse_message_map(field, condition, padding, equality, challenges)
    assert matrix == dense
    print("Structured map agrees exactly with dense high-to-low folding on an independently constructed condition table", flush=True)


def tail_matrix(field, condition, padding, equality, challenges):
    weights = field.eq(equality)
    rows = [[field.mul(weights[index], condition[index]) for index in padding]]
    condition, factors = list(condition), [1] * len(padding)
    for coordinate in reversed(range(len(challenges))):
        half, weights = len(condition) // 2, field.eq(equality[:coordinate])
        at_one, quadratic = [], []
        for index, factor in zip(padding, factors):
            low = index % half
            weight = field.mul(weights[low], factor)
            at_one.append(field.mul(weight, condition[low + half]) if index & half else 0)
            quadratic.append(field.mul(weight, condition[low] ^ condition[low + half]))
        rows.append(at_one)
        if coordinate:
            rows.append(quadratic)
        coin = challenges[coordinate]
        factors = [field.mul(factor, coin if index & half else 1 ^ coin) for index, factor in zip(padding, factors)]
        condition = [lo ^ field.mul(coin, lo ^ hi) for lo, hi in zip(condition[:half], condition[half:])]
    assert len(rows) == 2 * len(challenges)
    return rows


def edeterminant(field, matrix):
    rows, determinant = [row[:] for row in matrix], 1
    for column in range(len(rows)):
        pivot = next((row for row in range(column, len(rows)) if rows[row][column]), None)
        if pivot is None:
            return 0
        rows[column], rows[pivot] = rows[pivot], rows[column]
        value = rows[column][column]
        determinant = field.mul(determinant, value)
        inverse = einv(field, value)
        for row in range(column + 1, len(rows)):
            scale = field.mul(rows[row][column], inverse)
            rows[row] = [a ^ field.mul(scale, b) for a, b in zip(rows[row], rows[column])]
    return determinant


def tail_certificates(verifier, actual):
    field, rng = Tower(64 if actual else 8, verifier), Random(91)
    for tag_bits in (3, 5, 8):
        padding = [0, 1] + [index for bit in range(1, tag_bits) for index in (1 << bit, (1 << bit) + 1)]
        equality, challenges = [2] * tag_bits, [0] * tag_bits
        common = field.random(rng)
        for mode in ("zero", "one", "random"):
            condition = [0 if mode == "zero" else 1 if mode == "one" else field.random(rng) for _ in range(1 << tag_bits)]
            for index in padding:
                condition[index] = field.mul(common, 1 if index in (0, 1) or index % 2 == 0 else 2)
            matrix = tail_matrix(field, condition, padding, equality, challenges)
            actual_det = edeterminant(field, matrix)
            predicted = field.mul(field.mul(condition[0], condition[1]), field.eq(equality)[0])
            for bit in range(1, tag_bits):
                weights = field.eq(equality[:bit])
                cross = field.mul(condition[1 << bit], condition[1]) ^ field.mul(condition[(1 << bit) + 1], condition[0])
                predicted = field.mul(predicted, field.mul(field.mul(weights[0], weights[1]), cross))
            assert actual_det == predicted != 0
        print(f"Tail determinant: K=2^{field.bits}, d={tag_bits}, exact triangular formula holds with arbitrary outside values", flush=True)
    size = 1 << 192
    span = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert span + Fraction(273, size) < Fraction(1, 1 << 157)
    print("Isolated JUMP bound: sparse-span error plus 273/|E| is below 2^-157", flush=True)


def conditional_certificates(verifier):
    for bits, logs in ((8, range(6, 10)), (64, (7, 8))):
        field, rng = Tower(bits, verifier), Random(51)
        for log_size in logs:
            condition, padding = parity_bank(field, log_size, rng)
            equality = [field.random(rng) for _ in range(log_size)]
            challenges = [field.random(rng) for _ in range(log_size)]
            matrix, terminal, terminal_c = inverse_message_map(field, condition, padding, equality, challenges)
            rank = len(field.pivots(field.expand(matrix)))
            target = 3 * (2 * log_size - 2)
            assert terminal_c
            if log_size >= 7:
                assert len(field.pivots(field.expand(matrix[:-1]))) == rank == target
            extended_rank = len(field.pivots(field.expand(matrix + [terminal])))
            assert rank == extended_rank
            print(
                f"Conditional inverse map: K=2^{bits}, logN={log_size}, masks={len(padding)}, rank={rank}/{target}; terminal adds no rank", flush=True
            )
            if log_size == 7:
                flag = [int(bool(c)) for c in condition]
                inverse = [field.kinv(c) if c else rng.randrange(1 << bits) for c in condition]
                batch = field.random(rng)
                before, old_terminal = jump_view(field, condition, flag, inverse, equality, challenges, batch)
                shifts = [rng.randrange(1 << bits) for _ in padding]
                for index, shift in zip(padding, shifts):
                    inverse[index] ^= shift
                after, new_terminal = jump_view(field, condition, flag, inverse, equality, challenges, batch)
                assert [a ^ b for a, b in zip(before, after)] == [edot(field, row, shifts) for row in matrix]
                assert old_terminal[2] ^ new_terminal[2] == edot(field, terminal, shifts)
                c_pair, b_pair = (penultimate(field, column, challenges) for column in (condition, flag))
                rebuilt, rebuilt_terminal, _ = reconstruct(field, before[:-1], c_pair, b_pair, equality, challenges, batch)
                assert rebuilt == before and rebuilt_terminal == old_terminal
                if bits == 64:
                    fake = [field.random(rng) for _ in before[:-1]]
                    _, terminal, wire = reconstruct(field, fake, c_pair, b_pair, equality, challenges, batch)
                    replay_sumcheck(verifier, wire, equality, challenges, terminal, batch)
                print("Direct and reconstruction checks: conditional map, final-round invariant, and terminal inverse agree", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--combined", action="store_true")
    parser.add_argument("--actual-field", action="store_true")
    parser.add_argument("--structured", action="store_true")
    parser.add_argument("--tail", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    if args.tail:
        tail_certificates(verifier, args.actual_field)
    elif args.structured:
        structured_certificates(verifier, args.actual_field)
    elif args.combined:
        combined_certificates(verifier, args.actual_field)
    else:
        conditional_certificates(verifier)
        endpoint_certificate(verifier)
