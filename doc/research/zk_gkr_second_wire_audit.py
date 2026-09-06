"""Exact second-layer wire symmetries and Jacobian certificates, not VM ZK."""

from functools import reduce
from operator import mul
from random import Random

from zk_count_children_audit import gkr_replay
from zk_pcs_audit import verifier_module


def parent_products(nodes):
    return [reduce(mul, nodes[start : start + 4]) for start in range(0, 16, 4)]


def multiply_lines(lines):
    result = list(lines[0])
    for constant, slope in lines[1:]:
        following = [result[0] * constant]
        following.extend(result[i] * constant + result[i - 1] * slope for i in range(1, len(result)))
        following.append(result[-1] * slope)
        result = following
    return result


def stage_wire(v, channels, equality, challenges, combiner):
    zero = channels[0][0] * v.ZERO
    work = [[nodes[child::4] for child in range(4)] for nodes in channels]
    wire = []
    for coordinate, challenge in enumerate(challenges):
        message = [zero] * 5
        weights = v.eq_kernel(equality[coordinate + 1 :])
        for channel, children in enumerate(work):
            for row, weight in enumerate(weights):
                lines = [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in children]
                polynomial = multiply_lines(lines)
                message = [current + value * (combiner**channel * weight) for current, value in zip(message, polynomial, strict=True)]
        wire.extend(message[1:])
        work = [
            [[child[2 * row] + (child[2 * row] + child[2 * row + 1]) * challenge for row in range(len(child) // 2)] for child in children]
            for children in work
        ]
    wire.extend(child[0] for children in work for child in children)
    return tuple(wire)


def full_depth_prefix(v, replay, seed):
    prefix, _, _, wire = replay["view"]
    values, rng, samples = iter((*prefix, *wire)), Random(seed), 0

    class EndOfPrefix(Exception):
        pass

    class Stream:
        def next_scalar(self):
            try:
                return next(values)
            except StopIteration:
                assert samples == 9
                raise EndOfPrefix from None

        def next_scalars(self, count):
            return [self.next_scalar() for _ in range(count)]

        def sample(self):
            nonlocal samples
            samples += 1
            assert samples <= 9
            return v.E(*(rng.getrandbits(64) for _ in range(3)))

        def samples(self, count):
            return [self.sample() for _ in range(count)]

        sumcheck_round_poly = v.Transcript.sumcheck_round_poly

    try:
        v.verify_gkr_grand_products(22, Stream())
    except EndOfPrefix:
        return
    raise AssertionError("the actual verifier should request its third-layer message")


def exact_symmetry(v, push, pull, count, seed):
    replay = gkr_replay(v, count, seed=seed, details=True, bus_leaves=(push, pull))
    prefix, _, _, wire = replay["view"]
    assert stage_wire(v, (push, pull, count), replay["equality"], replay["challenge"], replay["combiner"]) == wire
    terminal = replay["children"][1]
    assert all(terminal)
    full_depth_prefix(v, replay, seed)
    changed = []
    for permutation in ((1, 0, 2, 3), (1, 2, 3, 0), (3, 2, 1, 0)):
        transformed = [terminal[j] / terminal[permutation[j]] * pull[4 * row + permutation[j]] for row in range(4) for j in range(4)]
        assert parent_products(transformed) == parent_products(pull)
        other = gkr_replay(v, count, seed=seed, details=True, bus_leaves=(push, transformed))
        assert other == replay
        assert other["view"][0] == prefix
        full_depth_prefix(v, other, seed)
        changed.append(push[9] / transformed[9] != push[9] / pull[9])
    assert all(changed)
    print(
        "Normalized pull-column permutations preserve every first/second-layer wire value and challenge while changing the MUL bytecode-node ratio",
        flush=True,
    )
    return replay


def layout_certificate(v):
    layout = v.build_layout(range(16 << 20), 20, (4, 18, 15, 4, 17, 3))
    bus, counts = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22 and layout.stack_log == 24
    assert bus.framework[2].index == 4 << 18 and bus.framework[2].variables == 20
    for blocks in (layout.push, layout.pull):
        mul_blocks = [(block, place) for block, place in zip(blocks, bus.tables, strict=True) if block.owner == v.OP_MUL]
        assert mul_blocks[1][0].coordinates[0].terms[()] == v.SEP_BYTECODE
        assert mul_blocks[1][1].index == 9 << 18 and mul_blocks[1][1].variables == 18
    assert all(place.index >> 18 == (place.index + (1 << place.variables) - 1) >> 18 for place in counts.tables)
    print("Actual depth-22 layout: node 9 is MUL bytecode; push nodes 4..7 and every normalized second-frontier count node are public", flush=True)


class Dual:
    def __init__(self, value, derivatives):
        self.value, self.derivatives = value, tuple(derivatives)

    def __add__(self, other):
        if not isinstance(other, Dual):
            return Dual(self.value + other, self.derivatives)
        return Dual(self.value + other.value, [a + b for a, b in zip(self.derivatives, other.derivatives, strict=True)])

    def __mul__(self, other):
        if not isinstance(other, Dual):
            return Dual(self.value * other, [a * other for a in self.derivatives])
        return Dual(
            self.value * other.value,
            [a * other.value + b * self.value for a, b in zip(self.derivatives, other.derivatives, strict=True)],
        )


def row_basis(v, rows):
    basis = {}
    for original in rows:
        row = list(original)
        for pivot, vector in sorted(basis.items()):
            if row[pivot]:
                scale = row[pivot]
                row = [a + scale * b for a, b in zip(row, vector, strict=True)]
        pivot = next((index for index, value in enumerate(row) if value), None)
        if pivot is not None:
            inverse = v.ONE / row[pivot]
            basis[pivot] = tuple(value * inverse for value in row)
    return basis


def kernel_direction(v, rows, target):
    basis, size = row_basis(v, rows), len(target)
    for free in range(size):
        if free in basis:
            continue
        direction = [v.ZERO] * size
        direction[free] = v.ONE
        for pivot, row in sorted(basis.items(), reverse=True):
            direction[pivot] = v.dot(row[pivot + 1 :], direction[pivot + 1 :])
        assert all(v.dot(row, direction) == v.ZERO for row in rows)
        if v.dot(target, direction):
            return direction
    raise AssertionError("the ratio derivative was expected to vary on the wire fiber")


def jacobian_certificate(v, push, pull, count, replay):
    variables = [(0, index) for index in (*range(4), *range(8, 16))] + [(1, index) for index in range(16)]
    size, lookup = len(variables), {variable: i for i, variable in enumerate(variables)}
    channels = [
        [Dual(value, [v.ONE if lookup.get((channel, index)) == i else v.ZERO for i in range(size)]) for index, value in enumerate(nodes)]
        for channel, nodes in enumerate((push, pull, count))
    ]
    parents = [parent_products(nodes) for nodes in channels]
    balance = reduce(mul, parents[0]) + reduce(mul, parents[1])
    wire = stage_wire(v, channels, replay["equality"], replay["challenge"], replay["combiner"])
    assert tuple(value.value for value in wire) == replay["view"][3]
    assert balance.value == v.ZERO
    observations = [balance, *parents[0], *parents[1], *wire]
    rows = [value.derivatives for value in observations]
    ratio_numerator = [v.ZERO] * size
    ratio_numerator[lookup[0, 9]], ratio_numerator[lookup[1, 9]] = pull[9], push[9]
    assert len(row_basis(v, rows)) == 21
    assert len(row_basis(v, [*rows, ratio_numerator])) == 22
    direction = kernel_direction(v, rows, ratio_numerator)
    assert v.dot(ratio_numerator, direction) != v.ZERO
    fixed_push_rows = [channels[0][index].derivatives for index in (*range(4), *range(8, 16))]
    stronger = [*rows, *fixed_push_rows]
    assert len(row_basis(v, stronger)) == 26
    assert len(row_basis(v, [*stronger, ratio_numerator])) == 27
    direction = kernel_direction(v, stronger, ratio_numerator)
    assert all(direction[lookup[0, index]] == v.ZERO for index in (*range(4), *range(8, 16)))
    assert v.dot(ratio_numerator, direction) != v.ZERO
    print("Exact E-valued Jacobian ranks: 21 -> 22 with the ratio; with the entire push frontier supplied, 26 -> 27", flush=True)
    print("Explicit tangent directions fix balance, parent products, every wire coefficient and terminal child while varying that ratio", flush=True)


def limitation_example(v, push, pull, count, replay):
    e0, e1 = replay["challenge"]
    weights = v.eq_kernel((e0, e1))
    terminal = replay["children"][1]
    normalized = [pull[8 + j] / terminal[j] for j in range(4)]
    permutation = (1, 0, 2, 3)
    transformed = [terminal[j] / terminal[permutation[j]] * pull[4 * row + permutation[j]] for row in range(4) for j in range(4)]
    assert sorted(int(transformed[8 + j] / terminal[j]) for j in range(4)) == sorted(map(int, normalized))
    assert all(v.dot(weights, transformed[j::4]) == terminal[j] for j in range(4))
    assert reduce(mul, normalized) == reduce(mul, pull[8:12]) / reduce(mul, terminal)
    print("The permutation ambiguity is finite and preserves symmetric information; it is not a statistical-hiding proof", flush=True)


if __name__ == "__main__":
    verifier, rng = verifier_module(), Random(178)
    layout_certificate(verifier)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    push_nodes, pull_nodes = [[sample() for _ in range(16)] for _ in range(2)]
    pull_nodes[-1] = reduce(mul, push_nodes) / reduce(mul, pull_nodes[:-1])
    count_nodes = [verifier.GEN**i for i in range(16)]
    instance = exact_symmetry(verifier, push_nodes, pull_nodes, count_nodes, seed=179)
    jacobian_certificate(verifier, push_nodes, pull_nodes, count_nodes, instance)
    limitation_example(verifier, push_nodes, pull_nodes, count_nodes, instance)
