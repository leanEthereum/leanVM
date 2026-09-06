"""Sparse exact replay of the unchanged GKR reader, with omitted leaves equal to one."""

from functools import reduce
from operator import mul
from random import Random

from zk_count_children_audit import gkr_replay, polynomial_product
from zk_pcs_audit import verifier_module


def weight(v, point, index):
    return reduce(mul, (value if index >> bit & 1 else v.ONE + value for bit, value in enumerate(point)), v.ONE)


def contract(v, nodes, arity=4):
    result = {}
    for index, value in nodes.items():
        parent = index // arity
        result[parent] = result.get(parent, v.ONE) * value
    return {index: value for index, value in result.items() if value != v.ONE}


def fold(v, nodes, challenge):
    result = {}
    for parent in {index // 2 for index in nodes}:
        left, right = (nodes.get(2 * parent + bit, v.ONE) for bit in (0, 1))
        value = left + challenge * (left + right)
        if value != v.ONE:
            result[parent] = value
    return result


def replay(v, channels, depth, seed):
    assert len(channels) == 3 and all(0 <= index < 1 << depth for nodes in channels for index in nodes)
    trees = []
    for nodes in channels:
        tree = {0: nodes}
        for height in range(2, depth + 1, 2):
            tree[height] = contract(v, tree[height - 2])
        if depth % 2:
            tree[depth] = contract(v, tree[depth - 1], 2)
        trees.append(tree)
    roots = [tree[depth].get(0, v.ONE) for tree in trees]
    assert roots[0] == roots[1]
    rng, wire, coins = Random(seed), [roots[0], roots[2]], []

    def sample():
        value = v.E(*(rng.getrandbits(64) for _ in range(3)))
        coins.append(value)
        return value

    point, combiner, height = [], sample(), depth
    final = None
    while height:
        step = 1 if height % 2 else 2
        arity = 1 << step
        work = [
            [{index // arity: value for index, value in tree[height - step].items() if index % arity == child} for child in range(arity)]
            for tree in trees
        ]
        prefix, challenges = tuple(wire), []
        for coordinate in range(len(point)):
            message = [v.ONE + combiner + combiner**2] + [v.ZERO] * arity
            for side, children in enumerate(work):
                for row in {index // 2 for child in children for index in child}:
                    lines = []
                    for child in children:
                        left, right = (child.get(2 * row + bit, v.ONE) for bit in (0, 1))
                        lines.append((left, left + right))
                    change = polynomial_product(v, lines)
                    change[0] += v.ONE
                    scalar = combiner**side * weight(v, point[coordinate + 1 :], row)
                    message = [old + scalar * delta for old, delta in zip(message, change, strict=True)]
            wire.extend(message[1:])
            challenge = sample()
            challenges.append(challenge)
            work = [[fold(v, child, challenge) for child in children] for children in work]
        children = tuple(tuple(child.get(0, v.ONE) for child in side) for side in work)
        wire.extend(value for side in children for value in side)
        if height == 2:
            final = {
                "view": (prefix, tuple(challenges), children[2], tuple(wire[len(prefix) :])),
                "equality": tuple(point),
                "challenge": tuple(challenges),
                "combiner": combiner,
                "children": children,
            }
        low = [sample() for _ in range(step)]
        combiner = sample()
        point = [*low, *challenges]
        height -= step

    class Stream:
        def __init__(self):
            self.values, self.coins = iter(wire), iter(coins)

        def next_scalar(self):
            return next(self.values)

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            return next(self.coins)

        def samples(self, count):
            return [self.sample() for _ in range(count)]

        sumcheck_round_poly = v.Transcript.sumcheck_round_poly

    stream = Stream()
    result = v.verify_gkr_grand_products(depth, stream)
    assert next(stream.values, None) is None and next(stream.coins, None) is None
    expected = tuple(v.ONE + v.E.sum(weight(v, result[1], index) * (v.ONE + value) for index, value in nodes.items()) for nodes in channels)
    assert result[2] == expected
    final["result"] = result
    final["coins"] = tuple(coins)
    return final


def dense_certificate(v):
    rng = Random(208)
    for depth in (6, 7):
        nodes = {index: v.E(*(rng.getrandbits(64) for _ in range(3))) for index in (0, 3, 8, 15, 31, 47)}
        nodes[8] = v.ZERO
        pull = {index ^ 1: value for index, value in nodes.items()}
        counts = {index: v.GEN**index for index in (0, 7, 15, 33)}
        sparse = replay(v, (nodes, pull, counts), depth, 209)
        dense_nodes = [[side.get(index, v.ONE) for index in range(1 << depth)] for side in (nodes, pull, counts)]
        dense = gkr_replay(v, dense_nodes[2], seed=209, details=True, bus_leaves=dense_nodes[:2])
        assert sparse == dense
    print(
        "Sparse and independent dense GKR replays agree on the entire wire, coins and result at odd and even depths, including zero nodes", flush=True
    )


if __name__ == "__main__":
    dense_certificate(verifier_module())
