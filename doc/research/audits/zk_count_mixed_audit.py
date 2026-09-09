"""Exact mixed-bank Boolean coefficients of a whole count-GKR layer."""

import argparse
from fractions import Fraction
from random import Random

from zk_count_children_audit import SPARSE, gkr_replay
from zk_count_first_round_audit import library_rows
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis


def add_scaled(left, right, scale):
    result = left.copy()
    for monomial, coefficient in right.items():
        value = result.get(monomial, coefficient + coefficient) + scale * coefficient
        if int(value):
            result[monomial] = value
        else:
            result.pop(monomial, None)
    return result


def multiply(left, right):
    result = {}
    for first, a in left.items():
        for second, b in right.items():
            monomial = first | second
            value = result.get(monomial, a + a) + a * b
            if int(value):
                result[monomial] = value
            else:
                result.pop(monomial, None)
    return result


def evaluate(verifier, polynomial, bits):
    return verifier.E.sum(value for monomial, value in polynomial.items() if bits & monomial == monomial)


def source_library(verifier, sparse_bits, anchors=False):
    anchor_kinds = {(bank, (1 << (sparse_bits + 1)) - 1): "ones" if bank == 0 else "plain" for bank in range(6)} if anchors else None
    library, positions, masks = library_rows(verifier, tuple(range(1 << sparse_bits)), sparse_bits, geometric=True, twist=True, anchors=anchor_kinds)
    column, real_switches = verifier.JUMP_COLUMNS.index("cnt_c"), []
    base = 6 << (sparse_bits + 4)

    def repeats(count):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        return [library.append(template)[0] for _ in range(count)]

    for first in (0, 1):
        for second in (0, 1):
            rows = repeats(4)
            ordered = rows[0], rows[3], rows[1], rows[2]
            locations = tuple(base + 4 * first + 8 * second + 16 * branch + child for branch in (0, 1) for child in (0, 1))
            assert not positions.keys() & set(locations)
            positions.update(zip(locations, ordered, strict=True))
            if second == 0:
                real_switches.append(tuple((row, column) for row in ordered))
        for branch in (0, 1):
            rows = repeats(2)
            for second, row in enumerate(rows):
                positions[base + 4 * first + 8 * second + 16 * branch + 2] = row
                positions[base + 4 * first + 8 * second + 16 * branch + 3] = repeats(1)[0]
    for position in range(1 << (sparse_bits + 7)):
        if position not in positions:
            positions[position] = repeats(1)[0]
    assert len(positions) == len(library.rows)
    library.verify()
    return library, positions, masks, real_switches


def symbolic_leaves(verifier, library, positions, masks):
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    leaves = [{0: library.rows[positions[position]][1][column]} for position in range(len(positions))]
    reverse = {row: position for position, row in positions.items()}
    for bit, switch in enumerate(masks):
        for (row, local_column), before, after in zip(switch, (0, 3, 2, 1), (1, 2, 3, 0)):
            assert local_column == column
            assert library.rows[row][1][column] == verifier.GEN**before
            leaves[reverse[row]][1 << bit] = verifier.GEN**before + verifier.GEN**after
    for offset in range(0, len(leaves), 4):
        product = {0: verifier.ONE}
        for leaf in leaves[offset : offset + 4]:
            product = multiply(product, leaf)
        assert set(product) == {0}
    return leaves


def layer_polynomials(verifier, leaves, equality, challenge, combiner):
    work = [leaves[child::4] for child in range(4)]
    outputs = []
    for coordinate, coin in enumerate(challenge):
        message = [{} for _ in range(5)]
        for row, weight in enumerate(verifier.eq_kernel(equality[coordinate + 1 :])):
            product = [{0: verifier.ONE}]
            for child in work:
                lines = child[2 * row], add_scaled(child[2 * row], child[2 * row + 1], verifier.ONE)
                expanded = [{} for _ in range(len(product) + 1)]
                for degree, term in enumerate(product):
                    for power, line in enumerate(lines):
                        expanded[degree + power] = add_scaled(expanded[degree + power], multiply(term, line), verifier.ONE)
                product = expanded
            for degree, term in enumerate(product):
                message[degree] = add_scaled(message[degree], term, weight * combiner**2)
        outputs.extend(message[1:])
        work = [
            [add_scaled(child[2 * row], add_scaled(child[2 * row], child[2 * row + 1], verifier.ONE), coin) for row in range(len(child) // 2)]
            for child in work
        ]
    return outputs + [child[0] for child in work]


def echelon(verifier, vectors):
    basis = {}
    for vector in vectors:
        row = list(vector)
        for pivot in sorted(basis):
            if row[pivot] != verifier.ZERO:
                factor = row[pivot]
                row = [a + factor * b for a, b in zip(row, basis[pivot])]
        pivot = next((index for index, value in enumerate(row) if value != verifier.ZERO), None)
        if pivot is not None:
            inverse = verifier.ONE / row[pivot]
            basis[pivot] = [value * inverse for value in row]
    return basis


def separating_form(verifier, basis, difference):
    residual = difference[:]
    for pivot in sorted(basis):
        factor = residual[pivot]
        residual = [a + factor * b for a, b in zip(residual, basis[pivot])]
    free = next((index for index, value in enumerate(residual) if value != verifier.ZERO), None)
    if free is None:
        return None
    form = [verifier.ZERO] * len(difference)
    form[free] = verifier.ONE
    for pivot in sorted(basis, reverse=True):
        form[pivot] = verifier.E.sum(value * coefficient for value, coefficient in zip(basis[pivot][pivot + 1 :], form[pivot + 1 :]))
    assert all(verifier.dot(row, form) == verifier.ZERO for row in basis.values())
    assert verifier.dot(difference, form) != verifier.ZERO
    return form


def root_form(verifier, equality, challenge, coordinate, root):
    result = [verifier.ZERO] * (4 * len(challenge) + 4)
    for round_index in range(coordinate + 1):
        point = root if round_index == coordinate else challenge[round_index]
        for degree in range(1, 5):
            result[4 * round_index + degree - 1] = equality[round_index] + point**degree
    return result


def anchor_root_certificate(verifier):
    rng, g = Random(138), verifier.GEN
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    weights, tags = verifier.eq_kernel([sample() for _ in range(13)]), verifier.eq_kernel([sample() for _ in range(3)])
    anchor, step = 2 * ((1 << 6) + (1 << 7)), verifier.ONE + g
    positions = [2 * index + parity for index in SPARSE for parity in (0, 1)]
    assert anchor not in positions
    columns = []
    for bank, direction in ((0, (verifier.ONE, verifier.ONE)), (3, (g / step, g**3 / step))):
        scale = step * (verifier.ONE + g**2) * tags[bank] * weights[anchor]
        columns.extend(int(scale * weights[index] * direction[0]) | (int(scale * weights[index] * direction[1]) << 192) for index in positions)
    assert len(binary_basis(columns)) == 384
    assert g / step + g**3 / step == g * step != verifier.ZERO
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert delta + Fraction(66, size) < Fraction(1, 1 << 157)
    library, _, masks = library_rows(verifier, (0,), 2, geometric=True, twist=True, anchors={(0, 6): "ones", (3, 6): "plain"})
    library.verify()
    assert len(masks) == 12
    print("Two different fixed anchors: joint common-root rank 384, privacy bound below 2^-157, and valid off-mask anchor cycles", flush=True)


def audit(verifier, sparse_bits, anchors=False):
    library, positions, masks, real_switches = source_library(verifier, sparse_bits, anchors=anchors)
    rng, systems, prefixes = Random(137), [], []
    for secret in (0, 1):
        for switch in real_switches:
            library.set_labels(switch, (1, 2, 0, 3) if secret else (0, 3, 1, 2))
        library.verify()
        leaves = symbolic_leaves(verifier, library, positions, masks)
        details = gkr_replay(verifier, [leaf[0] for leaf in leaves], details=True)
        polynomials = layer_polynomials(verifier, leaves, details["equality"], details["challenge"], details["combiner"])
        prefixes.append(details["view"][0])
        for bits in (0, 1, (1 << len(masks)) - 1, rng.getrandbits(len(masks))):
            values = [evaluate(verifier, leaf, bits) for leaf in leaves]
            view = gkr_replay(verifier, values)
            assert view[0] == prefixes[-1]
            actual = (*view[3][:-12], *view[2])
            assert tuple(evaluate(verifier, polynomial, bits) for polynomial in polynomials) == actual
        monomials = sorted(set().union(*(polynomial.keys() for polynomial in polynomials)) - {0})
        bits_per_bank = len(masks) // 6
        for monomial in monomials:
            bits = [index for index in range(len(masks)) if monomial >> index & 1]
            assert len(bits) <= 4 and len({index // bits_per_bank for index in bits}) == len(bits)
        print(
            f"Complement {secret}: {len(polynomials)} observations, {len(masks)} bits, monomial counts by degree {[sum(m.bit_count() == d for m in monomials) for d in range(1, 5)]}",
            flush=True,
        )
        systems.append((polynomials, monomials))
    assert prefixes[0] == prefixes[1]
    vectors = [
        [polynomial.get(monomial, verifier.ZERO) for polynomial in polynomials] for polynomials, monomials in systems for monomial in monomials
    ]
    linear_vectors = [
        [polynomial.get(monomial, verifier.ZERO) for polynomial in polynomials]
        for polynomials, monomials in systems
        for monomial in monomials
        if monomial.bit_count() == 1
    ]
    basis = echelon(verifier, vectors)
    individual_ranks = [
        len(echelon(verifier, [[polynomial.get(monomial, verifier.ZERO) for polynomial in polynomials] for monomial in monomials]))
        for polynomials, monomials in systems
    ]
    assert all(verifier.E.sum(vector[:4]) == verifier.ZERO for vector in vectors)
    difference = [a.get(0, verifier.ZERO) + b.get(0, verifier.ZERO) for a, b in zip(systems[0][0], systems[1][0])]
    form = separating_form(verifier, basis, difference)
    print(
        f"E-ranks: individual {individual_ranks}, combined single-bit {len(echelon(verifier, linear_vectors))}, all mixed terms {len(basis)} / {len(difference)}; separating E-linear form: {form is not None}",
        flush=True,
    )
    if form is not None:
        for polynomials, monomials in systems:
            assert all(
                verifier.dot([polynomial.get(monomial, verifier.ZERO) for polynomial in polynomials], form) == verifier.ZERO for monomial in monomials
            )
        print(f"Separating form support: {[index for index, value in enumerate(form) if value != verifier.ZERO]}", flush=True)
    separator = sparse_bits + 1
    roots = (verifier.ONE / (verifier.ONE + verifier.GEN**2), verifier.GEN**2 / (verifier.ONE + verifier.GEN**2))
    root_forms = [root_form(verifier, details["equality"], details["challenge"], separator, root) for root in roots]
    root_invariants = [all(verifier.dot(vector, root_functional) == verifier.ZERO for vector in vectors) for root_functional in root_forms]
    assert root_invariants == ([False, False] if anchors else [True, True])
    if not anchors:
        assert any(verifier.dot(difference, root_functional) != verifier.ZERO for root_functional in root_forms)
    print(f"Explicit common-root functionals annihilate every mixed term: {root_invariants}", flush=True)
    if sparse_bits == 2 and anchors:
        assert individual_ranks == [len(difference) - 1] * 2 and form is None
        print(
            "For both fixed complements the only E-affine constraint is the already-known first-endpoint relation; this is not a statistical hiding theorem",
            flush=True,
        )
    return systems, form


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--sparse-bits", type=int, default=0, choices=range(3))
    parser.add_argument("--anchors", action="store_true")
    args = parser.parse_args()
    verifier = verifier_module()
    anchor_root_certificate(verifier)
    audit(verifier, args.sparse_bits, anchors=args.anchors)
