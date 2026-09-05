"""Trace-dual closure for count-head maps and a rank-specialization guardrail."""

from random import Random

from zk_count_children_audit import EDGES, SPARSE
from zk_count_full_head_audit import BLOCK, folded_bank, late_columns, weight
from zk_count_mixed_audit import echelon
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis


def kernel(verifier, rows, width):
    basis = echelon(verifier, rows)
    result = []
    for free in range(width):
        if free in basis:
            continue
        vector = [verifier.ZERO] * width
        vector[free] = verifier.ONE
        for pivot in sorted(basis, reverse=True):
            vector[pivot] = verifier.dot(basis[pivot][pivot + 1 :], vector[pivot + 1 :])
        assert all(verifier.dot(row, vector) == verifier.ZERO for row in rows)
        result.append(vector)
    return result


def residual_constraints(verifier, rows, width):
    pivots, constraints = {}, []
    for source in rows:
        row = source[:]
        for pivot in sorted(pivots):
            factor = row[pivot]
            row = [a + factor * b for a, b in zip(row, pivots[pivot])]
        pivot = next((index for index in range(width) if row[index] != verifier.ZERO), None)
        if pivot is None:
            constraints.append(row[width:])
        else:
            inverse = verifier.ONE / row[pivot]
            pivots[pivot] = [value * inverse for value in row]
    return constraints, len(pivots)


def frobenius_closure(verifier, coefficients, both=False):
    outputs = len(coefficients[0][0])
    subspace = [[verifier.ONE if row == column else verifier.ZERO for row in range(outputs)] for column in range(outputs)]
    dimensions = [outputs]
    while subspace:
        width = len(subspace)
        rows = [
            [verifier.dot(linear, vector) ** 2 for vector in subspace] + [verifier.dot(square, vector) for vector in subspace]
            for linear, square in coefficients
        ]
        constraints, leading_rank = residual_constraints(verifier, rows, width)
        if both:
            reverse, trailing_rank = residual_constraints(verifier, [row[width:] + row[:width] for row in rows], width)
            constraints.extend([value ** (1 << 191) for value in row] for row in reverse)
            print(f"Restricted dual width {width}: leading rank {leading_rank}, trailing rank {trailing_rank}", flush=True)
        directions = kernel(verifier, constraints, width)
        dimensions.append(len(directions))
        if len(directions) == width:
            break
        subspace = [
            [verifier.E.sum(vector[row] * coefficient for vector, coefficient in zip(subspace, direction)) for row in range(outputs)]
            for direction in directions
        ]
    print(f"Frobenius dual-space dimensions, both directions {both}: {dimensions}", flush=True)
    return dimensions


def binary_rank(verifier, coefficients):
    columns = []
    for linear, square in coefficients:
        for bit in range(192):
            limbs = [0, 0, 0]
            limbs[bit // 64] = 1 << (bit % 64)
            value = verifier.E(*limbs)
            squared = value**2
            columns.append(sum(int(a * value + b * squared) << (192 * output) for output, (a, b) in enumerate(zip(linear, square))))
    return len(binary_basis(columns))


def specialization_guardrail(verifier):
    for parameter in (verifier.ZERO, verifier.ONE, verifier.GEN):
        coefficients = [([parameter], [verifier.ONE])]
        dimensions = frobenius_closure(verifier, coefficients, both=True)
        rank = binary_rank(verifier, coefficients)
        assert rank == (192 if parameter == verifier.ZERO else 191)
        assert dimensions[-1] == (0 if parameter == verifier.ZERO else 1)
    print("Specialization guardrail: u^2 + t*u is invertible at t=0 and has binary rank 191 at every tested nonzero t", flush=True)


def audit(verifier):
    count, group_bits, anchor, rng = 13, 3, 384, Random(146)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    banks = BLOCK * (1 << group_bits)
    equality, challenge = ([sample() for _ in range(count + 4 + group_bits)] for _ in range(2))
    support = tuple(2 * index + bit for index in SPARSE for bit in (0, 1))
    weights = [weight(verifier, challenge[:count], index) for index in support]
    children = [[] for _ in range(4)]
    for kind, edge in banks:
        mask = verifier.ZERO if edge == EDGES[0] else verifier.E.sum(value for value in weights if rng.getrandbits(1))
        folded = folded_bank(verifier, kind, edge, challenge[:count], anchor, mask)
        for destination, source in zip(children, folded):
            destination.extend(source)
    pivots = [bank for bank, (_, edge) in enumerate(banks) if edge == EDGES[0]]
    coefficients = late_columns(verifier, children, equality[count:], challenge[count:], pivots)
    square_rank = len(echelon(verifier, [square for _, square in coefficients]))
    stacked_rank = len(echelon(verifier, [[*(value**2 for value in linear), *square] for linear, square in coefficients]))
    outputs = len(coefficients[0][0])
    print(
        f"Square rank {square_rank}, stacked rank {stacked_rank}, ordinary quadratic-elimination rank {stacked_rank - square_rank}/{outputs}",
        flush=True,
    )
    print(f"Linear-part E-rank {len(echelon(verifier, [linear for linear, _ in coefficients]))}", flush=True)
    forward = frobenius_closure(verifier, coefficients)
    dimensions = frobenius_closure(verifier, coefficients, both=True)
    rank = binary_rank(verifier, coefficients)
    assert forward[-1] > 0 and dimensions[-1] == 0 and rank == 192 * outputs
    print(
        f"Full-completion post-sparse map: independently expanded binary rank {rank}; two-sided closure proves the same surjectivity at these fixed data",
        flush=True,
    )
    return coefficients, square_rank, stacked_rank, dimensions


if __name__ == "__main__":
    verifier = verifier_module()
    specialization_guardrail(verifier)
    audit(verifier)
