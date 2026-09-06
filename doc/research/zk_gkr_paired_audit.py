"""Joint push/pull product mixing, retaining the actual linear-view marginal."""

from collections import Counter
from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_bus_packet_audit import table_packets, weight
from zk_gkr_coarse_audit import (
    HEIGHT,
    PAD_FRAME,
    block_product,
    cycles,
    first_packet,
    layout_certificate,
)
from zk_padding_experiments import Field
from zk_pcs_audit import verifier_module

NOISE = 40


def small_field_joint():
    field, base, size, factors = Field(4, 0x13), 4, 16, 16
    product = field.mul
    generator = next(a for a in range(2, size) if product[a][a] ^ a == 1)
    subfield = (0, 1, generator, generator ^ 1)
    basis = next(a for a in range(size) if a not in subfield)
    images = [subfield[word & 3] ^ product[basis][subfield[(word >> 2) & 3]] for word in range(base**3)]
    assert Counter(images) == Counter({a: base for a in range(size)})
    for mode, shift in (("image", 1), ("kernel", 1), ("mixed", 1), ("mixed", 0)):
        counts, total = [0] * size**3, 1
        counts[(size + 1) * size] = 1
        for step in range(factors if shift else 4):
            transitions = Counter()
            for word, image in enumerate(images):
                leaf = image ^ step
                if leaf in (0, shift):
                    continue
                observed_image = product[1 + step % (size - 1)][image]
                kernel = subfield[word >> 4]
                observed = observed_image if mode == "image" else kernel if mode == "kernel" else observed_image ^ kernel
                transitions[leaf, observed] += 1
            following = [0] * size**3
            for state, count in enumerate(counts):
                if not count:
                    continue
                pair, observed = divmod(state, size)
                left, right = divmod(pair, size)
                for (leaf, delta), multiplicity in transitions.items():
                    target = (product[left][leaf] * size + product[right][leaf ^ shift]) * size + (observed ^ delta)
                    following[target] += count * multiplicity
            counts, total = following, total * sum(transitions.values())
        marginal = [sum(counts[(a * size + b) * size + y] for a in range(1, size) for b in range(1, size)) for y in range(size)]
        distance = Fraction(
            sum(
                abs((size - 1) ** 2 * counts[(a * size + b) * size + y] - marginal[y])
                for a in range(1, size)
                for b in range(1, size)
                for y in range(size)
            ),
            2 * (size - 1) ** 2 * total,
        )
        assert sum(marginal) == total
        if shift:
            bound_squared = Fraction(((size - 1) ** 2 - 1) * size, 4) * Fraction(4 * size, (base**2 - 2) ** 2) ** factors
            assert distance**2 <= bound_squared < Fraction(1, 10000)
            if mode == "kernel":
                assert all(value == 0 for y, value in enumerate(marginal) if y not in subfield)
        else:
            assert all(count == 0 or (state // size) // size == (state // size) % size for state, count in enumerate(counts))
            assert distance >= Fraction(size - 2, size - 1)
    print("Exact GF(4)-linear/GF(16) convolutions verify a nonvacuous joint bound with image, kernel and mixed views; zero shift fails", flush=True)


def actual_pair(verifier):
    layout, bus = layout_certificate(verifier, NOISE)
    pull_layout = verifier.bus_layout((0, 20, 20), layout.pull)
    assert bus == pull_layout
    push_mul = [(block, place) for block, place in zip(layout.push, bus.tables, strict=True) if block.owner == verifier.OP_MUL]
    pull_mul = [(block, place) for block, place in zip(layout.pull, pull_layout.tables, strict=True) if block.owner == verifier.OP_MUL]
    assert [place for _, place in push_mul] == [place for _, place in pull_mul]
    assert [block.coordinates[0] for block, _ in push_mul] == [block.coordinates[0] for block, _ in pull_mul]
    rng = Random(164)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = verifier.eq_kernel([sample() for _ in range(4)]), sample()
    point, y = [sample() for _ in range(bus.depth - 2)], [sample() for _ in range(2)]
    z, shift = [*y, *point], e[2] * (verifier.ONE + verifier.GEN)
    assert shift != verifier.ZERO
    left, right = ([[rng.getrandbits(64) for _ in range(3)] for _ in range(NOISE)] for _ in range(2))
    payload_sets = [[(0, 0, 0)] * NOISE, left, right, [[a ^ b for a, b in zip(x, y, strict=True)] for x, y in zip(left, right, strict=True)]]
    cofactors, views, images, counts, exponents = [], [], [], [], []
    for payloads in payload_sets:
        library, positions, mask_rows = cycles(verifier, 1, payloads)
        factor_pairs = [
            [
                beta
                + verifier.dot(
                    e[:6], [form.evaluate(library.rows[row_id][1].__getitem__) for form in getattr(verifier.TABLES[verifier.OP_MUL].flushes, side)[2]]
                )
                for side in ("push", "pull")
            ]
            for row_id in mask_rows
        ]
        assert all(a + b == shift for a, b in factor_pairs)
        children = [block_product(verifier, library, e, beta, side) for side in ("push", "pull")]
        cofactors.append(
            [child / reduce(mul, factors, verifier.ONE) for child, factors in zip(children, zip(*factor_pairs, strict=True), strict=True)]
        )
        first_packet(verifier, *children)
        push, pull = table_packets(verifier, library, positions, bus, layout, point, e)
        memory = [verifier.ZERO] * 3
        for index, payload in enumerate(payloads):
            for address in (PAD_FRAME + 128 * index, PAD_FRAME + 128 * index + 2):
                global_index = bus.framework[1].index + address
                contribution = weight(verifier, point, global_index >> 2) * verifier.dot(e[3:6], [verifier.E(value) for value in payload])
                push[global_index % 4] += contribution
                pull[global_index % 4] += contribution
                for lane, value in enumerate(payload):
                    memory[lane] += weight(verifier, z[: layout.log_memory], address) * verifier.E(value)
        views.append(push + pull + memory)
        images.append(library.images["code"])
        counts.append(dict(library.reads))
        exponents.append(dict(library.exponents))
    assert all(pair == cofactors[0] for pair in cofactors)
    assert all(image == images[0] for image in images) and all(value == counts[0] for value in counts)
    assert all(value == exponents[0] for value in exponents)
    assert all(verifier.E.sum(values) == verifier.ZERO for values in zip(*views, strict=True))
    assert all(view[i] + view[4 + i] == views[0][i] + views[0][4 + i] for view in views for i in range(4))
    print(
        "Forty valid MUL cycles: actual paired factors differ by e2(1+g), both cofactors are payload-independent, and boundary changes use seven linear fields",
        flush=True,
    )
    print(
        "Both actual block placements, disjoint reservations, fixed code/count profiles and accepted algebraic first-packet prefixes checked",
        flush=True,
    )


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    _, boundary = error_bound()
    root_mix = Fraction(1 << 767) * Fraction(1 << 96, base**2 - 1) ** 32
    root = Fraction((1 << 22) + 40, size) + Fraction(base**2, (size - 2) ** 2) + root_mix
    pair_mix = Fraction(1 << 863) * Fraction(1 << 97, base**2 - 2) ** NOISE
    pair = Fraction(8 * (1 << HEIGHT) + 8, size) + Fraction(base**2, (size - 2) ** 2) + pair_mix
    assert pair_mix < Fraction(1, 1 << 376)
    assert root + pair + boundary < Fraction(1, 1 << 155)
    print("Exact rational bound: shared root, both selected first children and all seventeen boundary values jointly hidden below 2^-155", flush=True)
    print("The remaining first packet and all intermediate GKR messages remain excluded", flush=True)


if __name__ == "__main__":
    small_field_joint()
    actual_pair(verifier_module())
    concrete_bound()
