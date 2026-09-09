"""Exact joint product/linear-observation checks for the shared-root hybrid."""

from collections import Counter
from fractions import Fraction

from zk_bus_boundary_audit import error_bound
from zk_pcs_audit import Tower


def mixed_convolution():
    field, base, size, factors = Tower(2), 4, 64, 12
    product = [[field.mul(a, b) for b in range(size)] for a in range(size)]
    for mode in ("image", "kernel", "mixed"):
        counts, total = [0] * (size * size), 1
        counts[size] = 1
        for step in range(factors):
            shift = (step % 4) * 16
            pairs = Counter()
            for word in range(size):
                leaf = shift ^ (word & 15)
                if not leaf:
                    continue
                image = product[(1, 4, 16)[step % 3]][word & 15]
                kernel = word >> 4
                observed = image if mode == "image" else kernel if mode == "kernel" else image ^ kernel
                pairs[leaf, observed] += 1
            following = [0] * (size * size)
            for state, count in enumerate(counts):
                if not count:
                    continue
                root, observation = divmod(state, size)
                for (leaf, observed), multiplicity in pairs.items():
                    following[product[root][leaf] * size + (observation ^ observed)] += count * multiplicity
            counts, total = following, total * sum(pairs.values())
        marginal = [sum(counts[root * size + observed] for root in range(1, size)) for observed in range(size)]
        distance = Fraction(
            sum(abs((size - 1) * counts[root * size + observed] - marginal[observed]) for root in range(1, size) for observed in range(size)),
            2 * (size - 1) * total,
        )
        bound_squared = Fraction((size - 2) * size, 4) * Fraction(size, (base**2 - 1) ** 2) ** factors
        assert distance**2 <= bound_squared
        if mode == "kernel":
            assert all(value == 0 for value in marginal[base:])
        assert sum(marginal) == total
    print(
        "Exact GF(4)/GF(64) convolutions match the joint bound against uniform-root times the actual linear-view law, including nonuniform and kernel-sensitive views",
        flush=True,
    )


def concrete_joint_bound():
    base, size = 1 << 64, 1 << 192
    mixing = Fraction(1 << 767) * Fraction(1 << 96, base**2 - 1) ** 32
    root = Fraction((1 << 40) + 40, size) + Fraction(base**2, (size - 2) ** 2) + mixing
    _, endpoint = error_bound()
    assert mixing < Fraction(1, 1 << 256)
    assert root + endpoint < Fraction(1, 1 << 151)
    print("Thirty-two actual-field words with seven E-valued linear observations: mixed-character error below 2^-256", flush=True)
    print("Shared root plus the complete seventeen-value boundary: exact combined error below 2^-151 for at most 2^40 other factors", flush=True)


if __name__ == "__main__":
    mixed_convolution()
    concrete_joint_bound()
