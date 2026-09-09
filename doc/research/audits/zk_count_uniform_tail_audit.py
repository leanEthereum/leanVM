"""A rank-safe uniform certificate for the post-sparse count tail."""

from fractions import Fraction
from random import Random

from zk_column_count_audit import Library
from zk_count_children_audit import EDGES
from zk_count_full_head_audit import BLOCK, folded_bank, late_columns
from zk_count_head_audit import late_view
from zk_count_mixed_audit import echelon
from zk_pcs_audit import verifier_module


def anchor_labels(bank):
    edge = BLOCK[bank % 8][1]
    if edge != EDGES[0]:
        return (0, 3, 1, 2) if edge == EDGES[3] else (0, 3, 2, 1)
    offset = bank + 1
    if bank % 8 == 0 and (bank // 8) % 2 == 0:
        return (offset,) * 4
    pattern = (0, 3, 2, 1) if bank % 8 == 0 else (0, 3, 1, 2)
    return tuple(offset + value for value in pattern)


def permuted_index(index, bank, width):
    return sum(((index >> bit) & 1) << ((bit + bank) % width) for bit in range(width))


def cycle_certificate(verifier):
    library = Library(verifier)
    column = verifier.JUMP_COLUMNS.index("cnt_c")

    def repeats(count):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        return [library.append(template)[0] for _ in range(count)]

    for bank in (*range(16), 120, 123, 125, 126):
        labels = anchor_labels(bank)
        if len(set(labels)) == 1:
            selected = [repeats(labels[0] + 1)[-1] for _ in range(4)]
        else:
            rows = repeats(max(labels) + 1)
            selected = [rows[label] for label in labels]
        assert [library.rows[row][1][column] for row in selected] == [verifier.GEN**label for label in labels]
        for _ in range(BLOCK[bank % 8][0]):
            rows = repeats(16)
            labels = [permuted_index(index, bank, 4) for index in range(16)]
            library.set_labels([(row, column) for row in rows], labels)
            assert [library.rows[row][1][column] for row in rows] == [verifier.GEN**label for label in labels]
    rows = repeats(4)
    switch = [(rows[index], column) for index in (0, 3, 2, 1)]
    library.verify()
    exponents, reads = dict(library.exponents), dict(library.reads)
    library.set_labels(switch, (1, 2, 3, 0))
    library.verify()
    assert dict(library.exponents) == exponents and dict(library.reads) == reads
    print("Offset anchors and bit-permuted geometric chains: complete ISA, bus, and counter checks pass", flush=True)


def bound_certificate():
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    degree = 32 * (2 * 55) + 13 * 42
    assert degree == 4066 and delta + Fraction(13 + 6 + 2 + degree, size) < Fraction(1, 1 << 157)
    print("Uniform determinant degree bound 4066; total privacy bound below 2^-157", flush=True)


def checked_roots(verifier, children, equality, challenge, roots):
    wire = late_view(verifier, children, equality, challenge, 4)
    work = children
    for coin in challenge[:4]:
        work = [[child[2 * row] + coin * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in work]
    target = verifier.E.sum(
        coefficient * work[0][group] * work[1][group] * work[2][group] * work[3][group]
        for group, coefficient in enumerate(verifier.eq_kernel(equality[4:]))
    )
    values, residuals = [], []
    for root in roots:
        direct = verifier.ZERO
        for bank, coefficient in enumerate(verifier.eq_kernel(equality[1:])):
            point = [child[2 * bank] + root * (child[2 * bank] + child[2 * bank + 1]) for child in children]
            direct += coefficient * point[0] * point[1] * point[2] * point[3]
        weights = [challenge[0] ** power + root**power for power in range(1, 5)]
        weights += [equality[round_index] + challenge[round_index] ** power for round_index in range(1, 4) for power in range(1, 5)]
        assert direct == target + verifier.dot(weights, wire[:16])
        values.append(direct)
        residuals.append(direct + target + verifier.dot(weights[2:], wire[2:16]))
    x, y = challenge[0] + roots[0], challenge[0] + roots[1]
    determinant = x * y**2 + y * x**2
    assert determinant == x * y != verifier.ZERO
    assert (residuals[0] * y**2 + residuals[1] * x**2) / determinant == wire[0]
    assert (x * residuals[1] + y * residuals[0]) / determinant == wire[1]
    return values


def audit(verifier):
    count, group_bits, anchor, rng = 13, 4, 384, Random(148)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    banks = BLOCK * (1 << group_bits)
    equality, challenge = ([sample() for _ in range(count + 4 + group_bits)] for _ in range(2))
    challenge[:count] = [verifier.ONE if anchor >> bit & 1 else verifier.ZERO for bit in range(count)]
    children, g = [[] for _ in range(4)], verifier.GEN
    for bank, (kind, edge) in enumerate(banks):
        mask = verifier.ZERO if edge == EDGES[0] else sample()
        folded = folded_bank(verifier, kind, edge, challenge[:count], anchor, mask)
        if edge == EDGES[0]:
            labels = anchor_labels(bank)
            for branch in (0, 1):
                for child in (0, 1):
                    folded[child][branch] += verifier.ONE + g ** labels[2 * branch + child]
        permutation = [(bit + bank) % (count + 1) for bit in range(count + 1)]
        geometric = verifier.ONE
        for bit, coin in enumerate(challenge[:count]):
            geometric *= verifier.ONE + (verifier.ONE + g ** (1 << permutation[bit])) * coin
        for number, child in enumerate(child for child in range(4) if child not in edge):
            if number < kind:
                folded[child] = [geometric * g ** (branch << permutation[count]) for branch in (0, 1)]
        for destination, source in zip(children, folded):
            destination.extend(source)
    pivots = [bank for bank, (_, edge) in enumerate(banks) if edge == EDGES[0]]
    coefficients = late_columns(verifier, children, equality[count:], challenge[count:], pivots)
    roots = (verifier.ONE / (verifier.ONE + g**2), g**2 / (verifier.ONE + g**2))
    tags = verifier.eq_kernel(equality[count + 1 :])
    for bank, (linear, square) in zip(pivots, coefficients):
        for coordinate, root in enumerate(roots):
            point = [child[2 * bank] + root * (child[2 * bank] + child[2 * bank + 1]) for child in children]
            left, right = verifier.ONE + (verifier.ONE + g**2) * root, g**2 + (verifier.ONE + g**2) * root
            linear[coordinate] = tags[bank] * (verifier.ONE + g) * (left * point[1] + right * point[0]) * point[2] * point[3]
            square[coordinate] = verifier.ZERO
    work = children
    for coin in challenge[count : count + 3]:
        work = [[child[2 * row] + coin * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in work]
    separator = challenge[count]
    left, right = verifier.ONE + (verifier.ONE + g**2) * separator, g**2 + (verifier.ONE + g**2) * separator
    derivative = []
    for group, coefficient in enumerate(verifier.eq_kernel(equality[count + 4 :])):
        c0, c1 = work[2][2 * group], work[2][2 * group] + work[2][2 * group + 1]
        d0, d1 = work[3][2 * group], work[3][2 * group] + work[3][2 * group + 1]
        derivative.append(coefficient * right / left * (c0 * d1 + c1 * d0))
    for linear, square in coefficients:
        assert square[12] + challenge[count + 3] ** 2 * square[14] == verifier.E.sum(
            value * coordinate**2 for value, coordinate in zip(derivative, linear[16:])
        )
    pure = (0, 1, *range(16, 32))
    assert all(square[index] == verifier.ZERO for _, square in coefficients for index in pure)
    quadratic = tuple(index for index in range(2, 16) if index != 12)
    constraints = [[*(linear[index] ** 2 for index in pure), *(square[index] for index in quadratic)] for linear, square in coefficients]
    full = [[*(value**2 for value in linear), *(square[index] for index in quadratic)] for linear, square in coefficients]
    constraint_rank, full_rank = len(echelon(verifier, constraints)), len(echelon(verifier, full))
    assert (constraint_rank, full_rank) == (31, 45)
    print(
        f"Triangular certificate: constraint rank {constraint_rank}/31, full rank {full_rank}/45, residual rank {full_rank - constraint_rank}/14",
        flush=True,
    )
    for _ in range(2):
        samples = [sample() for _ in pivots]
        changed = [child[:] for child in children]
        for bank, value in zip(pivots, samples):
            for branch, first, second in ((0, verifier.ONE, g**2), (1, g**2, verifier.ONE)):
                changed[0][2 * bank + branch] += (verifier.ONE + g) * first * value
                changed[1][2 * bank + branch] += (verifier.ONE + g) * second * value
        base_view = late_view(verifier, children, equality[count:], challenge[count:], 4)
        other_view = late_view(verifier, changed, equality[count:], challenge[count:], 4)
        base_view[:2] = checked_roots(verifier, children, equality[count:], challenge[count:], roots)
        other_view[:2] = checked_roots(verifier, changed, equality[count:], challenge[count:], roots)
        for output, (before, after) in enumerate(zip(base_view, other_view)):
            assert before + after == verifier.E.sum(
                linear[output] * value + square[output] * value**2 for (linear, square), value in zip(coefficients, samples)
            )
    print("Root-coordinate linearized map and inverse agree with direct polynomial evaluation and the backward wire identities", flush=True)
    square_rank = len(echelon(verifier, [square for _, square in coefficients]))
    stacked_rank = len(echelon(verifier, [[*(value**2 for value in linear), *square] for linear, square in coefficients]))
    linear_rank = len(echelon(verifier, [linear for linear, _ in coefficients]))
    print(
        f"Offset anchors: linear rank {linear_rank}, square rank {square_rank}, stacked rank {stacked_rank}, elimination rank {stacked_rank - square_rank}/32",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    cycle_certificate(verifier)
    bound_certificate()
    audit(verifier)
