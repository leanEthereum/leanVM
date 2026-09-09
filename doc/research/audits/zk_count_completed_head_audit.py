"""Exact sparse-head columns with the uniform tail's complete offset chains."""

import argparse
from random import Random

from zk_column_count_audit import Library
from zk_count_children_audit import EDGES, SPARSE, gkr_replay
from zk_count_full_head_audit import BLOCK, late_columns, weight
from zk_count_suffix_audit import pre_suffix
from zk_count_uniform_tail_audit import anchor_labels, permuted_index
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

CANONICAL = (0, 3, 2, 1)


def completion(bank, count, support, anchor):
    labels = anchor_labels(bank)
    if len(set(labels)) == 1:
        prefix = list(range(labels[0])) * 4
    else:
        prefix = list(range(min(labels)))
    replacements = {anchor: labels}
    reserved = set(support) | {anchor}
    for index in range(1 << count):
        if not prefix:
            break
        if index in reserved:
            continue
        taken, prefix = prefix[:4], prefix[4:]
        replacements[index] = tuple(taken + [0] * (4 - len(taken)))
    assert not prefix
    return replacements


def dense_library(verifier, count, banks, support, anchor):
    library, positions, switches = Library(verifier), {}, {}
    column = verifier.JUMP_COLUMNS.index("cnt_c")

    def repeats(number):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        return [library.append(template)[0] for _ in range(number)]

    for bank, (kind, edge) in enumerate(banks):
        labels, replacements = anchor_labels(bank), completion(bank, count, support, anchor)
        if len(set(labels)) == 1:
            chains = [repeats(labels[0] + 1) for _ in range(4)]
            selected, prefix = [chain[-1] for chain in chains], [row for chain in chains for row in chain[:-1]]
        else:
            chain = repeats(max(labels) + 1)
            selected, prefix = [chain[label] for label in labels], chain[: min(labels)]
        for index in range(1 << count):
            if index == anchor:
                rows = selected
            elif index in replacements:
                rows, prefix = prefix[:4], prefix[4:]
                rows += [repeats(1)[0] for _ in range(4 - len(rows))]
            else:
                chain = repeats(4)
                rows = [chain[label] for label in CANONICAL]
            for location, row in enumerate(rows):
                branch, child = divmod(location, 2)
                positions[(bank << (count + 3)) + 4 * (index + (branch << count)) + edge[child]] = row
            if index in support:
                switches[bank, index] = tuple((row, column) for row in rows)
        assert not prefix
        for number, child in enumerate(child for child in range(4) if child not in edge):
            rows = repeats(1 << (count + 1)) if number < kind else [repeats(1)[0] for _ in range(1 << (count + 1))]
            for index in range(1 << (count + 1)):
                row = rows[permuted_index(index, bank, count + 1)] if number < kind else rows[index]
                positions[(bank << (count + 3)) + 4 * index + child] = row
    assert len(positions) == len(library.rows) == len(banks) << (count + 3)
    return library, positions, switches


def bank_model(verifier, bank, count, support, anchor, challenge):
    g = verifier.GEN
    replacements = completion(bank, count, support, anchor)
    corrections = {index: [g**label + g**base for label, base in zip(labels, CANONICAL)] for index, labels in replacements.items()}
    folded = [g**label for label in CANONICAL]
    for index, values in corrections.items():
        scale = weight(verifier, challenge, index)
        folded = [value + scale * delta for value, delta in zip(folded, values)]
    lines = []
    for coordinate in range(count):
        stage = {}
        for index, values in corrections.items():
            high = index >> (coordinate + 1)
            if high not in stage:
                stage[high] = [[g**label, verifier.ZERO] for label in CANONICAL]
            scale = weight(verifier, challenge[:coordinate], index)
            for line, delta in zip(stage[high], values):
                line[1] += scale * delta
                if not (index >> coordinate & 1):
                    line[0] += scale * delta
        lines.append(stage)
    return folded, lines


def early_columns(verifier, bank, count, support, anchor, equality, challenge):
    kind, _ = BLOCK[bank % 8]
    g, step = verifier.GEN, verifier.ONE + verifier.GEN
    _, corrections = bank_model(verifier, bank, count, support, anchor, challenge)
    permutation = [(bit + bank) % (count + 1) for bit in range(count + 1)]
    prefixes = [verifier.ONE]
    for bit, coin in enumerate(challenge):
        prefixes.append(prefixes[-1] * (verifier.ONE + (verifier.ONE + g ** (1 << permutation[bit])) * coin))
    columns = []
    for index in support:
        result = []
        for coordinate in range(count):
            prefix = weight(verifier, challenge[:coordinate], index)
            delta = (verifier.ZERO if index >> coordinate & 1 else prefix, prefix)
            high = index >> (coordinate + 1)
            selected = corrections[coordinate].get(high, [[g**label, verifier.ZERO] for label in CANONICAL])
            message = [verifier.ZERO] * 5
            for branch, left, right in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
                first, second = selected[2 * branch : 2 * branch + 2]
                beta = [step * (right * first[power] + left * second[power]) for power in (0, 1)]
                gamma = step**2 * left * right
                inside = [
                    beta[0] * delta[0] + gamma * delta[0] ** 2,
                    beta[0] * delta[1] + beta[1] * delta[0],
                    beta[1] * delta[1] + gamma * delta[1] ** 2,
                ]
                exponent = sum(((index >> bit) & 1) << permutation[bit] for bit in range(coordinate + 1, count))
                exponent += branch << permutation[count]
                geometric = prefixes[coordinate] * g**exponent
                line = geometric, geometric * (verifier.ONE + g ** (1 << permutation[coordinate]))
                scale = equality[count] + (verifier.ONE if branch == 0 else verifier.ZERO)
                for power, coefficient in enumerate(inside):
                    message[power] += scale * coefficient * line[0] ** kind
                    if kind:
                        message[power + kind] += scale * coefficient * line[1] ** kind
            scale = weight(verifier, equality[coordinate + 1 : count], high)
            result.extend(scale * value for value in message[1:])
        assert verifier.E.sum(result[:4]) == verifier.ZERO
        columns.append(result)
    return columns


def folded_children(verifier, banks, count, support, anchor, challenge, masks):
    children, g = [[] for _ in range(4)], verifier.GEN
    for bank, ((kind, edge), mask) in enumerate(zip(banks, masks)):
        selected, _ = bank_model(verifier, bank, count, support, anchor, challenge)
        geometric = verifier.ONE
        for bit, coin in enumerate(challenge):
            geometric *= verifier.ONE + (verifier.ONE + g ** (1 << ((bit + bank) % (count + 1)))) * coin
        for branch, left, right in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
            values = [verifier.ONE] * 4
            values[edge[0]] = selected[2 * branch] + (verifier.ONE + g) * left * mask
            values[edge[1]] = selected[2 * branch + 1] + (verifier.ONE + g) * right * mask
            for number, child in enumerate(child for child in range(4) if child not in edge):
                if number < kind:
                    values[child] = geometric * g ** (branch << ((count + bank) % (count + 1)))
            for destination, value in zip(children, values):
                destination.append(value)
    return children


def packed(values):
    return sum(int(value) << (192 * coordinate) for coordinate, value in enumerate(values))


def columns(verifier, banks, count, support, anchor, equality, challenge, masks):
    children = folded_children(verifier, banks, count, support, anchor, challenge[:count], masks)
    pivots = [bank for bank, (_, edge) in enumerate(banks) if edge == EDGES[0]]
    late = late_columns(verifier, children, equality[count:], challenge[count:], pivots)
    weights = [weight(verifier, challenge[:count], index) for index in support]
    tags = verifier.eq_kernel(equality[count + 1 :])
    for pivot, (bank, (linear, square)) in enumerate(zip(pivots, late)):
        early = early_columns(verifier, bank, count, support, anchor, equality, challenge[:count])
        for vector, value in zip(early, weights):
            head = [tags[bank] * coefficient for coefficient in vector]
            tail = [a * value + b * value**2 for a, b in zip(linear, square)]
            yield packed(head + tail), packed(head) | (int(value) << (192 * (4 * count + pivot)))
        print(f"Completed bank {bank}: {(pivot + 1) * len(support)} exact bit columns", flush=True)


def small_replay(verifier):
    count, anchor, support, banks, rng = 4, 12, (0, 1), BLOCK * 2, Random(149)
    library, positions, switches = dense_library(verifier, count, banks, support, anchor)
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    active = []
    for (bank, index), switch in switches.items():
        if banks[bank][1] != EDGES[0] and rng.getrandbits(1):
            library.set_labels(switch, (1, 2, 3, 0))
            active.append((bank, index))
    library.verify()

    def leaves():
        return [library.rows[positions[index]][1][column] for index in range(len(positions))]

    values = leaves()
    details = gkr_replay(verifier, values, details=True)
    equality, challenge = details["equality"], details["challenge"]
    masks = [verifier.E.sum(weight(verifier, challenge[:count], index) for source, index in active if source == bank) for bank in range(len(banks))]
    assert folded_children(verifier, banks, count, support, anchor, challenge[:count], masks) == pre_suffix(verifier, values, challenge[:count])
    actual_columns = list(columns(verifier, banks, count, support, anchor, equality, challenge, masks))
    pivots = [switch for (bank, _), switch in switches.items() if banks[bank][1] == EDGES[0]]
    base = [value / details["combiner"] ** 2 for value in details["view"][3][: 4 * (count + 4)]]
    base += pre_suffix(verifier, values, challenge[: count + 4])[0]
    for selected in ((0,), (2,), (4,), (6,), (8,), (10,), (12,), (14,), (0, 3, 5, 8, 13, 15)):
        expected = 0
        for index in selected:
            library.set_labels(pivots[index], (1, 2, 3, 0))
            expected ^= actual_columns[index][0]
        library.verify()
        changed_values = leaves()
        other = gkr_replay(verifier, changed_values)
        assert other[0] == details["view"][0]
        actual = [value / details["combiner"] ** 2 for value in other[3][: 4 * (count + 4)]]
        actual += pre_suffix(verifier, changed_values, challenge[: count + 4])[0]
        assert packed([a + b for a, b in zip(actual, base)]) == expected
        for index in selected:
            library.set_labels(pivots[index], CANONICAL)
    print("Complete offset-chain library: valid counters and joint sparse/head differences match full GKR replays", flush=True)


def full_rank(verifier):
    count, anchor, banks, rng = 13, 384, BLOCK * 16, Random(150)
    support = tuple(2 * index + bit for index in SPARSE for bit in (0, 1))
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    equality, challenge = ([sample() for _ in range(count + 8)] for _ in range(2))
    weights = [weight(verifier, challenge[:count], index) for index in support]
    masks = [verifier.ZERO if edge == EDGES[0] else verifier.E.sum(value for value in weights if rng.getrandbits(1)) for _, edge in banks]
    joint, strong = zip(*columns(verifier, banks, count, support, anchor, equality, challenge, masks))
    rank, suffix_rank = len(binary_basis(joint)), len(binary_basis(value >> (192 * 4 * (count + 4)) for value in joint))
    strong_rank = len(binary_basis(strong))
    evaluation_rank = len(binary_basis(value >> (192 * 4 * count) for value in strong))
    print(f"Joint rank {rank}, suffix rank {suffix_rank}, conditional head {rank - suffix_rank}/{192 * (4 * (count + 4) - 2)}", flush=True)
    print(f"Early rank conditioned on all pivot evaluations: {strong_rank - evaluation_rank}/{192 * (4 * count - 2)}", flush=True)
    assert (rank, suffix_rank) == (15744, 3072)
    assert (strong_rank, evaluation_rank) == (21888, 12288)
    print("One actual-bit instance with all required prefix reads; neither calculation is a uniform statistical bound", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    small_replay(verifier)
    if args.full:
        full_rank(verifier)
