"""Initial-query obstructions for finite-profile Flock padding, not a ZK proof."""

import argparse
import subprocess
from fractions import Fraction
from math import comb
from pathlib import Path
from random import Random

from zk_flock_skip_audit import check_rows, cycle_certificate, witness
from zk_pcs_audit import Tower, kdot, verifier_module
from zk_stacked_audit import binary_basis


def library_messages():
    rng = Random(152)
    for _ in range(27):
        rng.getrandbits(64)
    messages = [[rng.getrandbits(32) for _ in range(16)] for _ in range(128)]
    assert len({tuple(message) for message in messages}) == 128
    return messages


def packed_difference(verifier, message, baseline):
    triple = witness(verifier, message)
    check_rows(verifier, triple)
    difference = triple[0] ^ baseline
    return [(difference >> (64 * slot)) & ((1 << 64) - 1) for slot in range(256)]


def probability_all_hit(domain, queries, count):
    numerator = sum((-1) ** omitted * comb(count, omitted) * (domain - omitted) ** queries for omitted in range(count + 1))
    return Fraction(numerator, domain**queries)


def probability_certificate(verifier):
    for rate in range(1, 5):
        queries = verifier.derive_config(28, rate).queries[0]
        domain = 1 << (22 + rate)
        cosets = domain >> 8
        good = 32 * (cosets - ((1 << 14) - 1)) - 7 * 255
        assert good > 0
        first = probability_all_hit(domain, queries, 7)
        second = probability_all_hit(domain, queries, 14)
        floor = (good * first - comb(good, 2) * second) / 2
        exponent = next(bits for bits in range(80, 140) if floor > Fraction(1, 1 << bits))
        assert exponent <= (89, 101, 111, 120)[rate - 1]
        assert Fraction((1 << 22) - 1, domain) ** queries < Fraction(1, 1 << 226)
        print(f"Rate log {rate}, {queries} queries: seven-point coset attack gives simulator error greater than 2^-{exponent}.", flush=True)


def reordered_index(logical):
    sparse, bank = logical & 2047, logical >> 11
    return (sparse & 7) | ((sparse >> 7) << 3) | (bank << 7) | (((sparse >> 3) & 15) << 14)


def layout_certificate(verifier):
    physical = [reordered_index(row) for row in range(1 << 18)]
    assert len(set(physical)) == 1 << 18
    profiles, random_counts, real_counts = [set() for _ in range(16)], [0] * 16, [0] * 16
    for logical, row in enumerate(physical):
        sparse, bank, lane = logical & 2047, logical >> 11, row >> 14
        if bank < 96 and (sparse >> 7).bit_count() <= 1:
            profiles[lane].add(bank)
            random_counts[lane] += 1
        if bank >= 96:
            real_counts[lane] += 1
    assert all(profile == set(range(96)) for profile in profiles)
    assert random_counts == [3840] * 16 and real_counts == [4096] * 16
    assert 96 * (2048 - 640) == 135168
    assert 96 * 640 + 7 * 135168 == 1007616
    layout = verifier.build_layout(range(16 << 17), 25, (19, 19, 19, 19, 20, 18))
    assert layout.stack_log == 28
    assert 248776704 - (1 << 11) + (1 << 17) == 248905728
    print("Mixed-coordinate candidate: all sixteen initial lanes contain all 96 profiles, 3840 random choices and 4096 real slots each.", flush=True)


def novel_factors(field, log_size, query):
    basis, value, factors = [1 << bit for bit in range(log_size)], query, []
    for bit in range(log_size):
        root = basis[bit]
        factors.append(field.kmul(value, field.kinv(root)))
        value = field.kmul(value, value ^ root)
        for high in range(bit + 1, log_size):
            basis[high] = field.kmul(basis[high], basis[high] ^ root)
    return factors


def real_factor(field, query):
    factors = novel_factors(field, 22, query)
    result = field.kmul(factors[19], factors[20])
    for factor in (*factors[8:19], factors[21]):
        result = field.kmul(result, 1 ^ factor)
    return result


def mixed_rank_diagnostic(verifier, messages, baseline):
    field, rng = Tower(64, verifier), Random(401)
    differences = [packed_difference(verifier, message, baseline) for message in messages[:97]]
    queries = [rng.randrange(1 << 23) for _ in range(61)]
    support = [low + 8 * high for high in (0, 1, 2, 4, 8) for low in range(8)]
    columns, private = [0] * (96 * len(support)), 0
    for round_index, query in enumerate(queries):
        factors = novel_factors(field, 22, query)
        low = field.novel(8, query)
        positions, banks = [1], [1]
        for position in range(7):
            positions += [field.kmul(value, factors[8 + position]) for value in positions]
            banks += [field.kmul(value, factors[15 + position]) for value in banks]
        values = [kdot(field, low, difference) for difference in differences]
        for bank in range(96):
            scale = field.kmul(banks[bank], values[bank])
            for offset, position in enumerate(support):
                columns[bank * len(support) + offset] |= field.kmul(scale, positions[position]) << (64 * round_index)
        private |= field.kmul(banks[96], values[96]) << (64 * round_index)
    for count, expected in zip((57, 60, 61), ((3616, 3616), (3808, 3808), (3840, 3841))):
        mask = (1 << (64 * count)) - 1
        projected = [column & mask for column in columns]
        padding_rank = len(binary_basis(projected))
        joint_rank = len(binary_basis([*projected, private & mask]))
        assert (padding_rank, joint_rank) == expected
        print(
            f"One mixed-order query sample, {count} points: binary padding rank {padding_rank}, with one private compression {joint_rank}.",
            flush=True,
        )
    print("These are fixed-query certificates, not a bound on their probability under honest queries.", flush=True)


def audit(verifier, native=False, mixed_rank=False):
    field, messages = Tower(64, verifier), library_messages()
    selected = (0, 1, 32, 33, 64, 65, 96)
    baseline = witness(verifier, [0] * 16)[0]
    differences = [packed_difference(verifier, messages[index], baseline) for index in selected]
    assert len(field.pivots(differences)) == 7
    evaluations = [[kdot(field, field.novel(8, offset), difference) for difference in differences] for offset in range(256)]
    offsets = field.pivots(list(zip(*evaluations)))
    assert len(offsets) == 7
    assert offsets == list(range(4, 11))
    assert len(field.pivots([evaluations[offset] for offset in offsets])) == 7
    patterns = [{offset ^ shift for offset in offsets} for shift in range(0, 256, 8)]
    assert len(set.union(*patterns)) == 32 * 7
    print(f"Seven valid compression profiles have coefficient rank seven; nonzero coset minor at offsets {offsets}.", flush=True)

    for base in (0, 1 << 12, 1 << 20, (1 << 22) + 256):
        rows = [[kdot(field, field.novel(8, base ^ offset), difference) for difference in differences] for offset in offsets]
        assert len(field.pivots(rows)) == 7
        for offset in offsets:
            low, full = field.novel(8, base ^ offset), field.novel(12, base ^ offset)
            assert full == tuple(field.kmul(low[slot], full[block << 8]) for block in range(16) for slot in range(256))
            assert [full[block << 8] for block in range(16)] == list(field.novel(12, base)[::256])
        columns = [list(column) for column in zip(*rows)]
        observed = [kdot(field, row[:6], list(range(17, 23))) for row in rows]
        assert len(field.pivots(columns[:6] + [observed])) == 6
        scale = real_factor(field, base)
        assert all(real_factor(field, base ^ offset) == scale for offset in offsets)
        if scale:
            shifted = [value ^ field.kmul(scale, row[-1]) for value, row in zip(observed, rows)]
            assert len(field.pivots(columns[:6] + [shifted])) == 7

    point = [field.random(Random(100 + bit)) for bit in range(18)]
    logical_point = [point[reordered_index(1 << bit).bit_length() - 1] for bit in range(18)]
    for index in (0, 1, 2047, 96 << 11, (1 << 18) - 1):
        left = right = 1
        for bit in range(18):
            left = field.mul(left, point[bit] if reordered_index(index) >> bit & 1 else 1 ^ point[bit])
            right = field.mul(right, logical_point[bit] if index >> bit & 1 else 1 ^ logical_point[bit])
        assert left == right

    cycle_certificate(verifier, [messages[index] for index in selected])
    probability_certificate(verifier)
    layout_certificate(verifier)
    if mixed_rank:
        mixed_rank_diagnostic(verifier, messages, baseline)
    if native:
        source = [word for index in selected for word in messages[index]]
        source += [(baseline >> (64 * slot)) & ((1 << 64) - 1) for slot in range(256)]
        source += [word for difference in differences for word in difference]
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_coset_audit"],
            input=" ".join(map(str, source)),
            text=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="also check native packed witnesses, NTT and authenticated leaf images")
    parser.add_argument("--mixed-rank", action="store_true", help="diagnose the revised order at one fixed query sample, without a probability claim")
    args = parser.parse_args()
    audit(verifier_module(), args.native, args.mixed_rank)
