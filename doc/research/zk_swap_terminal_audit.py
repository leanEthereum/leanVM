"""The last quartic's unmoved-half residual under valid row permutations."""

from functools import reduce
from operator import mul
from random import Random

from zk_audit_field import accelerate
from zk_count_children_audit import polynomial_product
from zk_pcs_audit import verifier_module
from zk_sparse_gkr_audit import fold, replay, weight
from zk_stacked_audit import binary_basis
from zk_subtree_swap_audit import (
    affine_columns,
    boundary,
    encode,
    fingerprint_parameters,
    native_library,
    permute,
)


def penultimate(v, nodes, challenges):
    work = [[{index // 4: value for index, value in side.items() if index % 4 == child} for child in range(4)] for side in nodes]
    for challenge in challenges[:-1]:
        work = [[fold(v, child, challenge) for child in side] for side in work]
    return tuple(tuple((child.get(0, v.ONE), child.get(0, v.ONE) + child.get(1, v.ONE)) for child in side) for side in work)


def terminal_polynomial(v, view):
    tails = view["view"][3][-16:-12]
    challenge, combiner = view["challenge"][-1], view["combiner"]
    value = v.E.sum(combiner**side * reduce(mul, children) for side, children in enumerate(view["children"]))
    constant = value + v.poly_eval((v.ZERO, *tails), challenge)
    return constant, *tails


def residual(v, view):
    challenge, combiner = view["challenge"][-1], view["combiner"]
    assert challenge != v.ONE
    count_lines = tuple(((value + challenge) / (v.ONE + challenge), (v.ONE + value) / (v.ONE + challenge)) for value in view["children"][2])
    count = polynomial_product(v, count_lines)
    return terminal_polynomial(v, view)[0] + combiner**2 * count[0]


def layout_support(v):
    for memory, code, shape, expected in ((16, 6, (2, 4, 2, 2, 4, 3), 17), (20, 20, (6, 18, 15, 4, 17, 3), 22)):
        layout = v.build_layout(range(16 << code), memory, shape)
        bus, count = v.bus_layout((0, memory, code), layout.push), v.bus_layout((), layout.count)
        assert bus.depth == expected and count.depth < bus.depth
        half = 1 << (bus.depth - 1)
        assert bus.framework[1].index == 0 and bus.framework[1].variables == memory
        if expected == 22:
            assert bus.framework[2].index == 1 << 20 and bus.framework[2].variables == 20
        else:
            assert 1 << bus.framework[1].variables == half
        assert all(half <= place.index and place.index + (1 << place.variables) <= 2 * half for place in bus.tables)
        assert all(place.index + (1 << place.variables) <= half for place in count.tables)
    print("Actual depth-17 and depth-22 layouts: every bus table is in the upper half; every count block is in the lower half", flush=True)


def audit(v):
    layout_support(v)
    values = []
    for word in ((0, 0, 0), (7, 11, 13)):
        library, positions, _, _, original, placements, depth = native_library(v, unused_word=word)
        cases = (
            [],
            [(v.OP_MUL, 0, 1, (0, 1)), (v.OP_JUMP, 4, 1, (2, 3))],
            [(v.OP_MUL, 0, 4, (0, 3)), (v.OP_JUMP, 0, 4, (1, 2))],
        )
        extracted, previous = [], None
        for swaps in cases:
            nodes, _ = permute(v, library, positions, original, placements, swaps)
            view = replay(v, nodes, depth, 212)
            lines = penultimate(v, nodes, view["challenge"])
            actual = v.E.sum(view["combiner"] ** side * reduce(mul, (line[0] for line in lines[side])) for side in range(2))
            assert all(left + slope == v.ONE for left, slope in lines[2])
            assert residual(v, view) == actual
            q = [v.ZERO] * 5
            for side in range(3):
                for degree, value in enumerate(polynomial_product(v, lines[side])):
                    q[degree] += view["combiner"] ** side * value
            assert tuple(q) == terminal_polynomial(v, view)
            extracted.append(actual)
            if previous is not None:
                assert view["view"][3] != previous["view"][3]
            previous = view
        assert len(set(extracted)) == 1
        values.append(extracted[0])
        base = replay(v, original, depth, 212)
        swaps = [(opcode, start, 1, (0, 1)) for opcode in (v.OP_MUL, v.OP_JUMP) for start in range(0, 16, 4)]
        columns = affine_columns(v, original, placements, swaps, base)
        assert len(binary_basis([encode(column[-16:]) for column in columns])) == len(binary_basis([encode(column[-12:]) for column in columns]))
    assert values[0] != values[1]
    print(
        "The extracted mixed unmoved-half product is identical under valid row permutations and changes with an unused private memory word",
        flush=True,
    )
    print(
        "The last quartic is reconstructed from native penultimate lines; for fixed-pair swaps it adds no binary rank after the terminal children",
        flush=True,
    )


def reconstruction_certificate(v):
    rng = Random(213)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    challenge, combiner = sample(), sample()
    terminal = [[sample() for _ in range(4)] for _ in range(3)]
    fixed = [[sample() for _ in range(4)] for _ in range(2)] + [[v.ONE] * 4]
    lines = []
    for side in range(3):
        side_lines = []
        for value, endpoint in zip(terminal[side], fixed[side], strict=True):
            if side < 2:
                constant, slope = endpoint, (value + endpoint) / challenge
            else:
                slope = (value + endpoint) / (v.ONE + challenge)
                constant = endpoint + slope
            assert constant + challenge * slope == value
            assert (constant if side < 2 else constant + slope) == endpoint
            side_lines.append((constant, slope))
        lines.append(side_lines)
    q = [v.ZERO] * 5
    for side in range(3):
        for degree, value in enumerate(polynomial_product(v, lines[side])):
            q[degree] += combiner**side * value
    assert v.poly_eval(q, challenge) == v.E.sum(combiner**side * reduce(mul, values) for side, values in enumerate(terminal))
    print(
        "The last quartic is a deterministic function of terminal children and the unchanged opposite-half endpoints; corner challenges are explicitly excluded",
        flush=True,
    )


def framework_relation(v):
    library, _, indices, layout, nodes, _, depth = native_library(v, unused_word=(7, 11, 13))
    view = replay(v, nodes, depth, 212)
    _, e, beta = fingerprint_parameters(v)
    point = view["result"][1]
    y, x = point[:2], point[2 : layout.log_memory]
    endpoint = [[], []]
    for child in range(4):
        memory, final = [v.ZERO] * 3, v.ONE
        for index in indices["memory"]:
            if index % 4 != child:
                continue
            scalar, address = weight(v, x, index // 4), int(v.GEN**index)
            for limb, value in enumerate(library.images["memory"][address]):
                memory[limb] += scalar * v.E(value)
            final += scalar * (v.ONE + v.GEN ** library.reads["memory", address])
        address = v.index_mle((v.E(child & 1), v.E(child >> 1), *x))
        for side, count in ((0, v.ONE), (1, final)):
            endpoint[side].append(beta + v.dot(e[:6], (v.SEP_MEM, address, count, *memory)))
    memory0, memory1, memory2, final, _ = boundary(v, library, indices, layout, view)[-5:]
    totals = [beta + v.dot(e[:6], (v.SEP_MEM, v.index_mle(point[: layout.log_memory]), count, memory0, memory1, memory2)) for count in (v.ONE, final)]
    weights = v.eq_kernel(y)
    for side in range(2):
        assert v.dot(weights, endpoint[side]) == totals[side]
        recovered = (totals[side] + v.dot(weights[:3], endpoint[side][:3])) / weights[3]
        assert recovered == endpoint[side][3]
    print(
        "Coherent full-memory fingerprint evaluations satisfy both weighted endpoint constraints; six residual fields reconstruct all eight bus endpoints",
        flush=True,
    )


def combined_framework_relation(v):
    library, _, indices, _, _, _, _ = native_library(v, unused_word=(7, 11, 13))
    _, e, beta = fingerprint_parameters(v)
    rng = Random(214)
    point = [v.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(22)]

    def fingerprint_eval(kind, local):
        tag = v.SEP_MEM if kind == "memory" else v.SEP_BYTECODE
        payload, final = v.ZERO, v.ONE
        for index in indices[kind]:
            scalar, address = weight(v, local, index), int(v.GEN**index)
            values = library.images[kind][address]
            payload += scalar * v.dot(e[3 : 3 + len(values)], [v.E(value) for value in values])
            final += scalar * (v.ONE + v.GEN ** library.reads[kind, address])
        shared = beta + e[0] * tag + e[1] * v.index_mle(local) + payload
        return shared + e[2], shared + e[2] * final

    selector, weights = point[20], v.eq_kernel(point[:2])
    memory, code = fingerprint_eval("memory", point[:20]), fingerprint_eval("code", point[:20])
    totals = [(v.ONE + selector) * left + selector * right for left, right in zip(memory, code, strict=True)]
    endpoint = [[], []]
    for child in range(4):
        local = (v.E(child & 1), v.E(child >> 1), *point[2:20])
        memory, code = fingerprint_eval("memory", local), fingerprint_eval("code", local)
        for side in range(2):
            endpoint[side].append((v.ONE + selector) * memory[side] + selector * code[side])
    for side in range(2):
        assert v.dot(weights, endpoint[side]) == totals[side]
        assert (totals[side] + v.dot(weights[:3], endpoint[side][:3])) / weights[3] == endpoint[side][3]
    print(
        "At depth 22 the penultimate selector combines memory and bytecode exactly; the two public boundary totals again leave six endpoint coordinates",
        flush=True,
    )


if __name__ == "__main__":
    module = verifier_module()
    accelerate(module)
    audit(module)
    reconstruction_certificate(module)
    framework_relation(module)
    combined_framework_relation(module)
