"""Count-GKR quartet invariants and valid balanced-trade masks, not joint ZK."""

from functools import reduce
from operator import mul
from random import Random

from zk_column_count_audit import Library
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

SPARSE = tuple(range(64)) + tuple(low + (1 << high) for high in range(6, 12) for low in range(64))
EDGES = ((0, 1), (1, 2), (2, 3), (3, 0))


def polynomial_product(verifier, lines):
    result = [verifier.ONE]
    for line in lines:
        product = [verifier.ZERO] * (len(result) + 1)
        for index, coefficient in enumerate(result):
            product[index] += coefficient * line[0]
            product[index + 1] += coefficient * line[1]
        result = product
    return result


def known_first_endpoints(verifier, previous_children, previous_low):
    if len(previous_children) == 2:
        assert len(previous_low) == 1
        return tuple(previous_children)
    assert len(previous_children) == 4 and len(previous_low) == 2
    high = previous_low[1]
    return tuple(previous_children[bit] + high * (previous_children[bit] + previous_children[bit + 2]) for bit in (0, 1))


def gkr_replay(verifier, count_leaves, seed=128, details=False, *, bus_leaves=None):
    depth, rng = verifier.log2_strict(len(count_leaves)), Random(seed)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    if bus_leaves is None:
        bus_leaves = ([verifier.ONE] * len(count_leaves), [verifier.ONE] * len(count_leaves))
    assert len(bus_leaves) == 2 and all(len(leaves) == len(count_leaves) for leaves in bus_leaves)
    layers = []
    for leaves in (*bus_leaves, count_leaves):
        tree = {0: leaves}
        for level in range(2, depth + 1, 2):
            below = tree[level - 2]
            tree[level] = [reduce(mul, below[index : index + 4]) for index in range(0, len(below), 4)]
        if depth % 2:
            tree[depth] = [reduce(mul, tree[depth - 1])]
        layers.append(tree)
    assert layers[0][depth][0] == layers[1][depth][0]
    wire, coins = [layers[0][depth][0], layers[2][depth][0]], []

    def coin():
        value = sample()
        coins.append(value)
        return value

    point, combiner, height = [], coin(), depth
    final, final_details, previous_packet, previous_low = None, None, None, None
    while height:
        step = 1 if height % 2 else 2
        arity = 1 << step
        work = [[tree[height - step][child::arity] for child in range(arity)] for tree in layers]
        prefix = tuple(wire)
        folded_point = []
        for coordinate in range(len(point)):
            weights = verifier.eq_kernel(point[coordinate + 1 :])
            message = [verifier.ZERO] * (arity + 1)
            for channel, children in enumerate(work):
                for row, weight in enumerate(weights):
                    lines = [(child[2 * row], child[2 * row] + child[2 * row + 1]) for child in children]
                    polynomial = polynomial_product(verifier, lines)
                    for degree, value in enumerate(polynomial):
                        message[degree] += combiner**channel * weight * value
            if coordinate == 0:
                endpoints = [known_first_endpoints(verifier, children, previous_low) for children in previous_packet]
                assert message[0] == verifier.E.sum(combiner**channel * values[0] for channel, values in enumerate(endpoints))
                assert verifier.E.sum(message) == verifier.E.sum(combiner**channel * values[1] for channel, values in enumerate(endpoints))
            wire.extend(message[1:])
            challenge = coin()
            folded_point.append(challenge)
            work = [
                [[child[2 * row] + challenge * (child[2 * row] + child[2 * row + 1]) for row in range(len(child) // 2)] for child in children]
                for children in work
            ]
        packet = [[child[0] for child in children] for children in work]
        wire.extend(value for children in packet for value in children)
        if height == 2:
            final = prefix, tuple(folded_point), tuple(packet[2]), tuple(wire[len(prefix) :])
            final_details = {
                "view": final,
                "equality": tuple(point),
                "challenge": tuple(folded_point),
                "combiner": combiner,
                "children": tuple(tuple(children) for children in packet),
            }
        low = [coin() for _ in range(step)]
        combiner = coin()
        point = [*low, *folded_point]
        previous_packet, previous_low = packet, low
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

        sumcheck_round_poly = verifier.Transcript.sumcheck_round_poly

    stream = Stream()
    result = verifier.verify_gkr_grand_products(depth, stream)
    assert next(stream.values, None) is None and next(stream.coins, None) is None
    assert result[2] == tuple(verifier.multilinear_eval(leaves, result[1]) for leaves in (*bus_leaves, count_leaves))
    if details:
        final_details["result"] = result
        final_details["coins"] = tuple(coins)
    return final_details if details else final


def invariant_certificate(verifier):
    rng, g = Random(129), verifier.GEN
    leaves = [g ** rng.randrange(16) for _ in range(64)]
    leaves[:8] = [verifier.ONE, g**3, verifier.ONE, verifier.ONE, g, g**2, verifier.ONE, verifier.ONE]
    prefix, point, packet, view = gkr_replay(verifier, leaves)
    sums = [verifier.E.sum(leaves[index : index + 4]) for index in range(0, len(leaves), 4)]
    exposed = verifier.E.sum(packet)
    assert exposed == verifier.multilinear_eval(sums, point)
    for _ in range(4):
        permuted = leaves[:]
        for index in range(0, len(permuted), 4):
            quartet = permuted[index : index + 4]
            rng.shuffle(quartet)
            permuted[index : index + 4] = quartet
        other_prefix, other_point, other_packet, _ = gkr_replay(verifier, permuted)
        assert other_prefix == prefix and other_point == point
        assert verifier.E.sum(other_packet) == exposed
    traded = leaves[:]
    traded[:8] = [g, g**2, verifier.ONE, verifier.ONE, verifier.ONE, g**3, verifier.ONE, verifier.ONE]
    other_prefix, other_point, other_packet, other_view = gkr_replay(verifier, traded)
    assert other_prefix == prefix and other_point == point
    assert other_view[:4] == view[:4]
    difference = (verifier.ONE + g) * (verifier.ONE + g**2) * verifier.eq_kernel(point[1:])[0]
    assert verifier.E.sum(other_packet) + exposed == difference != verifier.ZERO
    print(
        "Accepted complete GKR replays: quartet permutations leave the exposed sum unchanged; a balanced trade changes it with every ancestor fixed",
        flush=True,
    )


def first_message_certificate(verifier):
    g, leaves = verifier.GEN, [verifier.ONE] * 64
    for kind in range(3):
        for parity in (0, 1):
            for branch in (0, 1):
                base = 16 * kind + 4 * parity + 8 * branch
                leaves[base], leaves[base + 1] = (verifier.ONE, g**3) if not branch else (g, g**2)
                leaves[base + 2] = g if parity and kind else verifier.ONE
                leaves[base + 3] = g if parity and kind == 2 else verifier.ONE
    prefix, _, _, view = gkr_replay(verifier, leaves)
    expected = (
        (verifier.ONE, verifier.ONE, verifier.ZERO, verifier.ZERO),
        (verifier.ONE, g, verifier.ONE + g, verifier.ZERO),
        (verifier.ONE, verifier.ONE, (verifier.ONE + g) ** 2, (verifier.ONE + g) ** 2),
    )
    for kind in range(3):
        changed = leaves[:]
        base = 16 * kind
        changed[base], changed[base + 1] = g, g**2
        changed[base + 8], changed[base + 9] = verifier.ONE, g**3
        other_prefix, _, _, other_view = gkr_replay(verifier, changed)
        assert other_prefix == prefix
        delta = [a + b for a, b in zip(view[:4], other_view[:4])]
        assert delta[0] != verifier.ZERO
        assert tuple(value / delta[0] for value in delta) == expected[kind]
    assert (verifier.ONE + g) ** 3 != verifier.ZERO
    print(
        "Separated trades with three fixed backgrounds span all three quartic directions vanishing at 0 and 1; complete GKR replays accept",
        flush=True,
    )


def linearity_certificate(verifier):
    g, rng = verifier.GEN, Random(132)
    for second_pair in ((0, 1), (1, 2)):
        leaves = [g ** rng.randrange(16) for _ in range(64)]
        locations = []
        for base, (first, second) in zip((0, 8), ((0, 1), second_pair)):
            selected = (base + first, base + second, base + 4 + first, base + 4 + second)
            leaves[base : base + 8] = [verifier.ONE] * 8
            for index, exponent in zip(selected, (0, 3, 1, 2)):
                leaves[index] = g**exponent
            locations.append(selected)
        views, prefixes = [], []
        for choice in range(4):
            changed = leaves[:]
            for bit, selected in enumerate(locations):
                if choice >> bit & 1:
                    for index, exponent in zip(selected, (1, 2, 0, 3)):
                        changed[index] = g**exponent
            prefix, _, _, view = gkr_replay(verifier, changed)
            prefixes.append(prefix)
            views.append(view)
        assert all(prefix == prefixes[0] for prefix in prefixes)
        affine = all(verifier.E.sum(values) == verifier.ZERO for values in zip(*views))
        assert affine == (second_pair == (0, 1))
    print("Complete final-layer views are binary-affine for one trade direction; mixing pair directions has a nonzero cross term", flush=True)


def cycle_certificate(verifier):
    library, positions, switches = Library(verifier), {}, []
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    for bank, (first, second) in enumerate(EDGES):
        for index in SPARSE:
            base = 8 * ((bank << 12) + index)
            template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
            repeated = [library.append(template)[0] for _ in range(4)]
            locations = (base + first, base + second, base + 4 + first, base + 4 + second)
            ordered = (repeated[0], repeated[3], repeated[1], repeated[2])
            positions.update(zip(locations, ordered, strict=True))
            switches.append(tuple((row, column) for row in ordered))
            for offset in range(8):
                if base + offset not in positions:
                    filler = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
                    positions[base + offset] = library.append(filler)[0]
    assert len(positions) == len(library.rows) == 14336

    def ancestors():
        return {base: reduce(mul, (library.rows[positions[base + offset]][1][column] for offset in range(4))) for base in positions if base % 4 == 0}

    before = ancestors()
    library.verify()
    exponents, counts = dict(library.exponents), dict(library.reads)
    rng = Random(130)
    for switch in switches:
        if rng.getrandbits(1):
            library.set_labels(switch, (1, 2, 0, 3))
    library.verify()
    assert ancestors() == before
    assert dict(library.exponents) == exponents and dict(library.reads) == counts
    assert set(before.values()) == {verifier.GEN**3}
    print(
        "14336 valid JUMP rows: balanced trades preserve the actual bus, final counters, all count-column products and every designated quartet product",
        flush=True,
    )


def packet_rank_certificate(verifier):
    field, rng = Tower(64, verifier), Random(131)
    point = [field.random(rng) for _ in range(15)]
    weights, selectors = field.eq(point[1:13]), field.eq(point[13:])
    g, columns = int(verifier.GEN), []
    g2 = field.mul(g, g)
    for bank, (first, second) in enumerate(EDGES):
        for index in SPARSE:
            scale = field.mul(1 ^ g, field.mul(selectors[bank], weights[index]))
            vector = (scale << (192 * first)) ^ (field.mul(g2, scale) << (192 * second))
            columns.append(vector)
    assert len(binary_basis(columns)) == 768
    assert verifier.ONE + verifier.GEN**8 != verifier.ZERO
    print(
        "Actual-field child packet: four independent sparse banks have binary rank 768, covering all four extension-field child evaluations",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    invariant_certificate(verifier)
    first_message_certificate(verifier)
    linearity_certificate(verifier)
    packet_rank_certificate(verifier)
    cycle_certificate(verifier)
