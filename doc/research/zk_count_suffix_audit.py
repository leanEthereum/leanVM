"""Blockwise count padding: joint suffix simulation and a conditional head map."""

from fractions import Fraction
from random import Random

from zk_count_children_audit import EDGES, SPARSE, gkr_replay, polynomial_product
from zk_count_first_round_audit import library_rows
from zk_count_mixed_audit import evaluate, symbolic_leaves
from zk_pcs_audit import verifier_module
from zk_stacked_audit import binary_basis

BLOCK = tuple(zip((0, 1, 2, 0), EDGES, strict=True))


def suffix_view(verifier, children, equality, challenge, combiner):
    claim = verifier.E.sum(
        weight * children[0][row] * children[1][row] * children[2][row] * children[3][row] for row, weight in enumerate(verifier.eq_kernel(equality))
    )
    wire, work = [], children
    for coordinate, coin in enumerate(challenge):
        message = [verifier.ZERO] * 5
        for row, weight in enumerate(verifier.eq_kernel(equality[coordinate + 1 :])):
            product = polynomial_product(verifier, [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in work])
            for degree, value in enumerate(product):
                message[degree] += combiner**2 * weight * value
        wire.extend(message[1:])
        work = [[child[2 * row] + coin * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in work]
    return claim, (*wire, *(child[0] for child in work))


def pre_suffix(verifier, leaves, point):
    work = [leaves[child::4] for child in range(4)]
    for coin in point:
        work = [[child[2 * row] + coin * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in work]
    return work


def span_certificate(verifier):
    rng = Random(142)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    sparse_weights, tags, separator = verifier.eq_kernel([sample() for _ in range(13)]), verifier.eq_kernel([sample(), sample()]), sample()
    g, step = verifier.GEN, verifier.ONE + verifier.GEN
    left, right = verifier.ONE + (verifier.ONE + g**2) * separator, g**2 + (verifier.ONE + g**2) * separator
    assert left**4 + right**4 == (verifier.ONE + g**2) ** 4 != verifier.ZERO
    columns = []
    for bank, (first, second) in enumerate(EDGES):
        for index in SPARSE:
            for parity in (0, 1):
                scale = step * tags[bank] * sparse_weights[2 * index + parity]
                columns.append((int(scale * left) << (192 * first)) ^ (int(scale * right) << (192 * second)))
    assert len(binary_basis(columns)) == 768
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert delta + Fraction(17, size) < Fraction(1, 1 << 157)
    print("Full support: rank 768 per suffix group; common good-coin bound below 2^-157, independent of the number of groups", flush=True)


def audit(verifier, suffix_bits=2, sparse_bits=1, replica_bits=1):
    banks = tuple(
        ((bank // 4) % (1 << replica_bits) % 3 if bank % 4 == 0 else BLOCK[bank % 4][0], EDGES[bank % 4])
        for bank in range(1 << (suffix_bits + replica_bits + 2))
    )
    anchors = {(bank, (1 << (sparse_bits + 1)) - 1): "ones" if bank % 4 == 0 else "plain" for bank in range(len(banks)) if bank % 4 in (0, 3)}
    library, positions, masks = library_rows(
        verifier, tuple(range(1 << sparse_bits)), sparse_bits, geometric=True, twist=True, anchors=anchors, banks=banks
    )
    library.verify()
    assert len(positions) == len(library.rows) == 1 << (sparse_bits + suffix_bits + replica_bits + 6)
    polynomials = symbolic_leaves(verifier, library, positions, masks)
    rng, head, prefix = Random(143), sparse_bits + replica_bits + 4, None
    for bits in (0, (1 << len(masks)) - 1, rng.getrandbits(len(masks))):
        leaves = [evaluate(verifier, polynomial, bits) for polynomial in polynomials]
        for bit, switch in enumerate(masks):
            library.set_labels(switch, (1, 2, 3, 0) if bits >> bit & 1 else (0, 3, 2, 1))
        library.verify()
        details = gkr_replay(verifier, leaves, details=True)
        if prefix is None:
            prefix = details["view"][0]
        assert details["view"][0] == prefix
        children = pre_suffix(verifier, leaves, details["challenge"][:head])
        claim, actual = suffix_view(verifier, children, details["equality"][head:], details["challenge"][head:], details["combiner"])
        wire, packet = details["view"][3], details["view"][2]
        assert actual == (*wire[4 * head : -12], *packet)
        tail = wire[4 * head : 4 * head + 4]
        constant = claim * details["combiner"] ** 2 + details["equality"][head] * verifier.E.sum(tail)
        expected = suffix_view(verifier, children, [verifier.ZERO, *details["equality"][head + 1 :]], details["challenge"][head:], verifier.ONE)[0]
        assert constant == expected * details["combiner"] ** 2

    bit_banks = []
    reverse = {row: position for position, row in positions.items()}
    for switch in masks:
        bit_banks.append(reverse[switch[0][0]] >> (sparse_bits + 4))
    base = rng.getrandbits(len(masks))

    def head_wire(bits):
        values = [evaluate(verifier, polynomial, bits) for polynomial in polynomials]
        return gkr_replay(verifier, values)[3][: 4 * head]

    original = head_wire(base)
    for first, second in ((0, 1), (0, bit_banks.index(4)), (0, bit_banks.index(4 << replica_bits))):
        assert bit_banks[first] % 4 == bit_banks[second] % 4
        views = [original, head_wire(base ^ (1 << first)), head_wire(base ^ (1 << second)), head_wire(base ^ (1 << first) ^ (1 << second))]
        assert all(verifier.E.sum(values) == verifier.ZERO for values in zip(*views))
    print(
        f"{len(banks)} banks, {len(positions)} valid rows: exact last-{suffix_bits}-round replay from the pre-suffix table, with its incoming count claim",
        flush=True,
    )
    other_edge = bit_banks.index(1)
    views = [original, head_wire(base ^ 1), head_wire(base ^ (1 << other_edge)), head_wire(base ^ 1 ^ (1 << other_edge))]
    assert any(verifier.E.sum(values) != verifier.ZERO for values in zip(*views))
    print(
        "Same-edge pivot bits have zero mixed derivatives within a bank, across replicas, and across groups; a different-edge control is nonlinear",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    span_certificate(verifier)
    audit(verifier)
