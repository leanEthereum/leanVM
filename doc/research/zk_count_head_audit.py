"""Conditional binary rank of the post-sparse count head, not a ZK proof."""

import argparse
from random import Random

from zk_count_children_audit import EDGES, gkr_replay, polynomial_product
from zk_count_first_round_audit import library_rows
from zk_count_mixed_audit import echelon, root_form
from zk_count_suffix_audit import BLOCK, pre_suffix, span_certificate
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis


def late_view(verifier, children, equality, challenge, rounds):
    outputs, work = [], children
    for coordinate, coin in enumerate(challenge[:rounds]):
        message = [verifier.ZERO] * 5
        for row, weight in enumerate(verifier.eq_kernel(equality[coordinate + 1 :])):
            product = polynomial_product(verifier, [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in work])
            for degree, value in enumerate(product):
                message[degree] += weight * value
        outputs.extend(message[1:])
        work = [[child[2 * row] + coin * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in work]
    return outputs + work[0]


def audit(verifier, replica_bits=2, group_bits=3, parity=False):
    sparse_bits, rng = 1, Random(144)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    direction_bits = 3 if parity else 2
    parity_block = ((0, EDGES[0]), (1, EDGES[1]), (2, EDGES[2]), (1, EDGES[0]), (0, EDGES[3]), (2, EDGES[0]), (0, EDGES[0]), (0, EDGES[1]))
    banks = tuple(
        parity_block[bank % 8] if parity else ((bank // 4) % (1 << replica_bits) % 3 if bank % 4 == 0 else BLOCK[bank % 4][0], EDGES[bank % 4])
        for bank in range(1 << (replica_bits + group_bits + direction_bits))
    )
    anchors = {(bank, 3): "ones" if edge == EDGES[0] else "plain" for bank, (_, edge) in enumerate(banks) if edge in (EDGES[0], EDGES[3])}
    library, positions, masks = library_rows(verifier, (0, 1), sparse_bits, geometric=True, twist=True, anchors=anchors, banks=banks)
    for switch in masks:
        if rng.getrandbits(1):
            library.set_labels(switch, (1, 2, 3, 0))
    library.verify()
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    leaves = [library.rows[positions[index]][1][column] for index in range(len(positions))]
    details = gkr_replay(verifier, leaves, details=True)
    children = pre_suffix(verifier, leaves, details["challenge"][: sparse_bits + 1])
    equality, challenge = details["equality"][sparse_bits + 1 :], details["challenge"][sparse_bits + 1 :]
    rounds, groups, g = replica_bits + direction_bits + 1, 1 << group_bits, verifier.GEN
    base = late_view(verifier, children, equality, challenge, rounds)
    start, end = 4 * (sparse_bits + 1), 4 * (sparse_bits + 1 + rounds)
    assert base[: 4 * rounds] == [value / details["combiner"] ** 2 for value in details["view"][3][start:end]]
    pivot_banks = tuple(bank for bank, (_, edge) in enumerate(banks) if edge == EDGES[0])
    reverse = {row: position for position, row in positions.items()}
    for switch in masks:
        bank = reverse[switch[0][0]] >> (sparse_bits + 4)
        if bank in pivot_banks:
            original = tuple(library.labels[location][1] for location in switch)
            library.set_labels(switch, (1, 2, 3, 0) if original == (0, 3, 2, 1) else (0, 3, 2, 1))
    library.verify()
    changed = gkr_replay(verifier, [library.rows[positions[index]][1][column] for index in range(len(positions))])
    assert changed[0] == details["view"][0]
    difference = [a + b for a, b in zip((*changed[3][:-12], *changed[2]), (*details["view"][3][:-12], *details["view"][2]))]
    endpoint_changes = [
        verifier.dot(root_form(verifier, details["equality"], details["challenge"], sparse_bits + 2 + offset, verifier.ONE), difference)
        for offset in range(direction_bits)
    ]
    assert [value == verifier.ZERO for value in endpoint_changes] == ([False] * direction_bits if parity else [True] * direction_bits)
    print(f"Direction-round upper endpoints unchanged under pivot flips: {[value == verifier.ZERO for value in endpoint_changes]}", flush=True)

    def view(values):
        work = [child[:] for child in children]
        for bank, value in zip(pivot_banks, values):
            for branch, left, right in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
                work[0][2 * bank + branch] += (verifier.ONE + g) * left * value
                work[1][2 * bank + branch] += (verifier.ONE + g) * right * value
        return late_view(verifier, work, equality, challenge, rounds)

    linear, square = [], []
    for index in range(len(pivot_banks)):
        values = [verifier.ZERO] * len(pivot_banks)
        values[index] = verifier.ONE
        first = [value + constant for value, constant in zip(view(values), base)]
        values[index] = g
        second = [value + constant for value, constant in zip(view(values), base)]
        quadratic = [(b + g * a) / (g**2 + g) for a, b in zip(first, second)]
        square.append(quadratic)
        linear.append([a + b for a, b in zip(first, quadratic)])
        assert all(value == verifier.ZERO for value in quadratic[-groups:])
    for _ in range(2):
        values = [sample() for _ in pivot_banks]
        expected = [
            constant + verifier.E.sum(a[output] * value + b[output] * value**2 for a, b, value in zip(linear, square, values))
            for output, constant in enumerate(base)
        ]
        assert view(values) == expected
    print(
        f"Valid {len(positions)}-row baseline: exact reference head replay; {len(pivot_banks)} abstract E-valued pivots have an exact linearized map",
        flush=True,
    )
    columns, suffix_columns = [], []
    for a, b in zip(linear, square):
        for bit in range(192):
            limbs = [0, 0, 0]
            limbs[bit // 64] = 1 << (bit % 64)
            value = verifier.E(*limbs)
            vector = sum(int(first * value + second * value**2) << (192 * output) for output, (first, second) in enumerate(zip(a, b)))
            columns.append(vector)
            suffix_columns.append(vector >> (192 * 4 * rounds))
    rank, suffix_rank = len(binary_basis(columns)), len(binary_basis(suffix_columns))
    assert suffix_rank == 192 * groups
    conditional = rank - suffix_rank
    necessary = 192 * (4 * rounds - 2)
    extension_rank = len(echelon(verifier, linear + square))
    if group_bits == 3 and (replica_bits, parity) in ((2, False), (0, True)):
        assert (rank, suffix_rank) == ((4608, 1536) if parity else (4992, 1536))
    print(
        f"Post-sparse head: joint binary rank {rank}, suffix rank {suffix_rank}, conditional rank {conditional}; necessary full-head projection rank {necessary}",
        flush=True,
    )
    print(f"E-affine hull rank {extension_rank}/{len(base)}; binary conditional codimension {192 * 4 * rounds - conditional}", flush=True)
    print(
        "This relaxes sparse bits to independent extension scalars and tests one fixed complement and coin choice; it is not a uniform rank bound",
        flush=True,
    )
    return linear, square, rank, suffix_rank


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--replica-bits", type=int, default=2, choices=range(4))
    parser.add_argument("--group-bits", type=int, default=3, choices=range(1, 4))
    parser.add_argument("--parity", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    span_certificate(verifier, parity=args.parity)
    audit(verifier, args.replica_bits, args.group_bits, args.parity)
