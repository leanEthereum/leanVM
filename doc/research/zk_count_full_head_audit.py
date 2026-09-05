"""Actual sparse-bit columns for the parity count head, not a ZK theorem."""

import argparse
from random import Random

from zk_count_children_audit import EDGES, SPARSE, gkr_replay
from zk_count_first_round_audit import library_rows
from zk_count_head_audit import late_view
from zk_count_suffix_audit import pre_suffix
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

BLOCK = ((0, EDGES[0]), (1, EDGES[1]), (2, EDGES[2]), (1, EDGES[0]), (0, EDGES[3]), (2, EDGES[0]), (0, EDGES[0]), (0, EDGES[1]))


def weight(verifier, point, index):
    result = verifier.ONE
    for bit, coin in enumerate(point):
        result *= coin + (verifier.ZERO if index >> bit & 1 else verifier.ONE)
    return result


def folded_bank(verifier, kind, edge, point, anchor, mask):
    g, step = verifier.GEN, verifier.ONE + verifier.GEN
    geometric = verifier.ONE
    for bit, coin in enumerate(point):
        geometric *= verifier.ONE + (verifier.ONE + g ** (1 << bit)) * coin
    anchor_weight = weight(verifier, point, anchor)
    result = [[verifier.ONE] * 2 for _ in range(4)]
    for branch, left, right in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
        first, second = left + step * left * mask, g * right + step * right * mask
        if edge == EDGES[0]:
            first += anchor_weight * (verifier.ONE + left)
            second += anchor_weight * (verifier.ONE + g * right)
        elif edge == EDGES[3] and branch:
            first += anchor_weight * (g + g**2)
            second += anchor_weight * (g + g**2)
        result[edge[0]][branch], result[edge[1]][branch] = first, second
        background = geometric * g ** (branch << len(point))
        for number, child in enumerate(child for child in range(4) if child not in edge):
            if number < kind:
                result[child][branch] = background
    return result


def early_column(verifier, kind, index, anchor, equality, challenge):
    count, g = len(challenge), verifier.GEN
    step = verifier.ONE + g
    gamma = step**2 * g**2
    anchor_step = step * (verifier.ONE + g**2) + gamma
    result = []
    for coordinate in range(count):
        prefix = weight(verifier, challenge[:coordinate], index)
        delta = (verifier.ZERO if index >> coordinate & 1 else prefix, prefix)
        anchor_line = [verifier.ZERO, verifier.ZERO]
        if index >> (coordinate + 1) == anchor >> (coordinate + 1):
            anchor_prefix = weight(verifier, challenge[:coordinate], anchor)
            anchor_line = [verifier.ZERO if anchor >> coordinate & 1 else anchor_prefix, anchor_prefix]
        beta = gamma + anchor_step * anchor_line[0], anchor_step * anchor_line[1]
        inside = [
            beta[0] * delta[0] + gamma * delta[0] ** 2,
            beta[0] * delta[1] + beta[1] * delta[0],
            beta[1] * delta[1] + gamma * delta[1] ** 2,
        ]
        geometric = g ** ((index >> (coordinate + 1)) << (coordinate + 1))
        for bit, coin in enumerate(challenge[:coordinate]):
            geometric *= verifier.ONE + (verifier.ONE + g ** (1 << bit)) * coin
        line = geometric, geometric * (verifier.ONE + g ** (1 << coordinate))
        product = [verifier.ZERO] * 5
        if kind == 0:
            product[:3] = inside
        else:
            for power, coefficient in enumerate(inside):
                product[power] += coefficient * line[0] ** kind
                product[power + kind] += coefficient * line[1] ** kind
        separator_weight = verifier.ONE + equality[count] * (verifier.ONE + g ** (kind << count))
        scale = weight(verifier, equality[coordinate + 1 : count], index >> (coordinate + 1)) * separator_weight
        result.extend(scale * coefficient for coefficient in product[1:])
    return result


def late_columns(verifier, children, equality, challenge, pivots):
    base = late_view(verifier, children, equality, challenge, 4)
    g, result = verifier.GEN, []
    for bank in pivots:
        changes = []
        for value in (verifier.ONE, g):
            work = [child[:] for child in children]
            for branch, left, right in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
                work[0][2 * bank + branch] += (verifier.ONE + g) * left * value
                work[1][2 * bank + branch] += (verifier.ONE + g) * right * value
            changes.append([a + b for a, b in zip(late_view(verifier, work, equality, challenge, 4), base)])
        square = [(b + g * a) / (g**2 + g) for a, b in zip(*changes)]
        result.append(([a + b for a, b in zip(changes[0], square)], square))
    return result


def matrix_columns(verifier, banks, support, anchor, equality, challenge, mask_values):
    count = len(challenge) - 4 - verifier.log2_strict(len(banks) // 8)
    children = [[] for _ in range(4)]
    for (kind, edge), mask in zip(banks, mask_values):
        for destination, source in zip(children, folded_bank(verifier, kind, edge, challenge[:count], anchor, mask)):
            destination.extend(source)
    pivots = [bank for bank, (_, edge) in enumerate(banks) if edge == EDGES[0]]
    late = late_columns(verifier, children, equality[count:], challenge[count:], pivots)
    early = {kind: [early_column(verifier, kind, index, anchor, equality, challenge[:count]) for index in support] for kind in (0, 1, 2)}
    tags = verifier.eq_kernel(equality[count + 1 :])
    weights = [weight(verifier, challenge[:count], index) for index in support]
    columns = []
    for bank, (linear, square) in zip(pivots, late):
        for prefix, value in zip(early[banks[bank][0]], weights):
            vector = [tags[bank] * coefficient for coefficient in prefix]
            assert verifier.E.sum(vector[:4]) == verifier.ZERO
            vector.extend(a * value + b * value**2 for a, b in zip(linear, square))
            columns.append(sum(int(coefficient) << (192 * output) for output, coefficient in enumerate(vector)))
        print(f"Built {len(columns)} actual sparse-bit columns", flush=True)
    return columns, children


def small_replay(verifier):
    count, groups, anchor, rng = 3, 1, 7, Random(145)
    banks = BLOCK * (1 << groups)
    library, positions, switches = library_rows(
        verifier,
        tuple(range(1 << (count - 1))),
        count - 1,
        geometric=True,
        twist=True,
        anchors={(bank, anchor): "ones" if edge == EDGES[0] else "plain" for bank, (_, edge) in enumerate(banks) if edge in (EDGES[0], EDGES[3])},
        banks=banks,
    )
    reverse = {row: position for position, row in positions.items()}
    pivots, mask_positions = [], {bank: [] for bank in range(len(banks))}
    for switch in switches:
        position = reverse[switch[0][0]]
        bank, index = position >> (count + 3), (position >> 2) & ((1 << count) - 1)
        if banks[bank][1] == EDGES[0]:
            pivots.append(switch)
        elif rng.getrandbits(1):
            library.set_labels(switch, (1, 2, 3, 0))
            mask_positions[bank].append(index)
    library.verify()
    column = verifier.JUMP_COLUMNS.index("cnt_c")

    def leaves():
        return [library.rows[positions[index]][1][column] for index in range(len(positions))]

    values = leaves()
    details = gkr_replay(verifier, values, details=True)
    equality, challenge = details["equality"], details["challenge"]
    masks = [verifier.E.sum(weight(verifier, challenge[:count], index) for index in mask_positions[bank]) for bank in range(len(banks))]
    columns, folded = matrix_columns(verifier, banks, tuple(range(anchor)), anchor, equality, challenge, masks)
    assert folded == pre_suffix(verifier, values, challenge[:count])
    base = [value / details["combiner"] ** 2 for value in details["view"][3][: 4 * (count + 4)]]
    base += pre_suffix(verifier, values, challenge[: count + 4])[0]
    for selected in ((0,), (6,), (7,), (14,), (20,), (len(pivots) - 1,), (0, 4, 12, 18, 25, 37)):
        expected = 0
        for index in selected:
            library.set_labels(pivots[index], (1, 2, 3, 0))
            expected ^= columns[index]
        library.verify()
        other_values = leaves()
        other = gkr_replay(verifier, other_values)
        assert other[0] == details["view"][0]
        actual = [value / details["combiner"] ** 2 for value in other[3][: 4 * (count + 4)]]
        actual += pre_suffix(verifier, other_values, challenge[: count + 4])[0]
        packed = sum(int(a + b) << (192 * output) for output, (a, b) in enumerate(zip(actual, base)))
        assert packed == expected
        for index in selected:
            library.set_labels(pivots[index], (0, 3, 2, 1))
    print(
        "Small valid-cycle certificate: local early formulas, folded bank formula, late composition, and joint bit flips match complete GKR replays",
        flush=True,
    )


def full_rank(verifier):
    count, group_bits, anchor, rng = 13, 3, 384, Random(146)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    banks, support = BLOCK * (1 << group_bits), tuple(2 * index + bit for index in SPARSE for bit in (0, 1))
    assert anchor not in support
    equality, challenge = ([sample() for _ in range(count + 4 + group_bits)] for _ in range(2))
    weights = [weight(verifier, challenge[:count], index) for index in support]
    masks = [verifier.ZERO if edge == EDGES[0] else verifier.E.sum(value for value in weights if rng.getrandbits(1)) for _, edge in banks]
    columns, _ = matrix_columns(verifier, banks, support, anchor, equality, challenge, masks)
    shift = 192 * 4 * (count + 4)
    rank, suffix_rank = len(binary_basis(columns)), len(binary_basis(value >> shift for value in columns))
    assert (rank, suffix_rank) == (14208, 192 * (1 << group_bits))
    print(
        f"Full support: {len(columns)} bits, joint rank {rank}, suffix rank {suffix_rank}, conditional rank {rank - suffix_rank}, target {192 * (4 * (count + 4) - 2)}",
        flush=True,
    )
    print("One concrete completion and independent coin choice; no uniform rank bound or full-layer statistical theorem", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--full", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    small_replay(verifier)
    if args.full:
        full_rank(verifier)
