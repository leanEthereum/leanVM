"""Complete second-frontier leakage reduction; eight residual fields remain."""

from fractions import Fraction
from functools import reduce
from itertools import product
from operator import mul
from random import Random

from zk_bus_boundary_audit import error_bound
from zk_bytecode_frontier_audit import CODE_BASES
from zk_bytecode_public_library_audit import FRAME_BASE, set_library
from zk_control_composition_audit import frontier, reconstruct, view
from zk_control_residual_audit import add_library
from zk_count_children_audit import SPARSE, gkr_replay
from zk_even_children_audit import (
    MUL_NOISE,
    UNUSED,
    four_products,
    payload_factors,
    two_inputs,
)
from zk_gkr_coarse_audit import PAD_PC
from zk_gkr_first_packet_audit import fingerprint, linear_view
from zk_gkr_second_wire_audit import (
    Dual,
    full_depth_prefix,
    parent_products,
    row_basis,
    stage_wire,
)
from zk_odd_children_audit import NOISE as XOR_NOISE
from zk_odd_children_audit import OLD_ROWS, xor_library
from zk_pcs_audit import verifier_module
from zk_public_seed_leakage_audit import reservations
from zk_set_payload_products_audit import BANKS, BITS

SPREAD_FRAMES = (393216, 557056, 819200)
FIXED = (4, 5, 6, 7, 8, 9, 14, 24, 25, 30)
FREE = tuple(index for index in range(32) if index not in (*FIXED, 31))


def joint_factors(v, raw, free, residual, seed):
    push, pull = payload_factors(v, raw)
    sets, controls = reconstruct(free, residual, seed)
    c_plus, c_minus, m_plus, m_minus = sets
    s_plus, j_plus, hc_plus, hd_plus, f_plus, s_minus, j_minus, hc_minus, hd_minus, f_minus = controls
    push[13], pull[13] = s_plus * j_plus, s_minus * j_minus
    push[14], pull[14] = hc_plus * hd_plus, hc_minus * hd_minus
    push[15] *= s_minus * c_plus * m_plus * f_plus
    pull[15] *= s_plus * c_minus * m_minus * f_minus
    pull[1] = m_plus * f_plus / (m_minus * f_minus) * (hc_plus * hd_plus / (hc_minus * hd_minus))
    pull[4:8] = free[:4]
    return push, pull


class Monomial:
    def __init__(self, powers):
        self.powers = tuple(powers)

    def __mul__(self, other):
        if not isinstance(other, Monomial):
            assert other == 1
            return self
        return Monomial([a + b for a, b in zip(self.powers, other.powers, strict=True)])

    def __truediv__(self, other):
        if not isinstance(other, Monomial):
            assert other == 1
            return self
        return Monomial([a - b for a, b in zip(self.powers, other.powers, strict=True)])


def spread_factors(channels, products, quarters):
    for (a1, ag, c1, cg), quarter in zip(products, quarters, strict=True):
        for side, incoming, outgoing in ((0, (a1, c1), (ag, cg)), (1, (ag, cg), (a1, c1))):
            channels[side][quarter] *= incoming[0] * incoming[1]
            channels[side][10] *= outgoing[0]
            channels[side][12] *= outgoing[1]
    return channels


def exponent_rows(v, extra_quarters=(), mul_quarters=()):
    size = 22 + len(extra_quarters) + 4 * len(mul_quarters)
    inputs = [Monomial([int(i == j) for i in range(size)]) for j in range(size)]
    one = Monomial([0] * size)
    channels = joint_factors(v, inputs[:9], inputs[9:22], [one] * 7, one)
    for offset, quarter in enumerate(extra_quarters):
        for channel in channels:
            if isinstance(channel[quarter], Monomial):
                channel[quarter] *= inputs[22 + offset]
            else:
                channel[quarter] = inputs[22 + offset]
    for channel in channels:
        for i, value in enumerate(channel):
            if not isinstance(value, Monomial):
                channel[i] = one
    start = 22 + len(extra_quarters)
    products = [inputs[start + 4 * i : start + 4 * i + 4] for i in range(len(mul_quarters))]
    spread_factors(channels, products, mul_quarters)
    return [list(value.powers) if isinstance(value, Monomial) else [0] * size for channel in channels for value in channel]


def unit_rank(matrix):
    work, rank = [row[:] for row in matrix], 0
    while rank < min(len(work), len(work[0])):
        pivot = next(((i, j) for i in range(rank, len(work)) for j in range(rank, len(work[0])) if abs(work[i][j]) == 1), None)
        if pivot is None:
            assert all(value == 0 for row in work[rank:] for value in row[rank:])
            return rank
        i, j = pivot
        work[rank], work[i] = work[i], work[rank]
        for row in work:
            row[rank], row[j] = row[j], row[rank]
        if work[rank][rank] == -1:
            work[rank] = [-value for value in work[rank]]
        for i in range(len(work)):
            if i != rank:
                scale = work[i][rank]
                work[i] = [a - scale * b for a, b in zip(work[i], work[rank], strict=True)]
        for j in range(rank + 1, len(work[0])):
            scale = work[rank][j]
            for i in range(len(work)):
                work[i][j] -= scale * work[i][rank]
        rank += 1
    return rank


def wire_rank(v, exponents, nodes, count, equality, challenges, combiner):
    size = len(exponents[0])
    channels = [
        [
            Dual(value, [value if exponent % 2 else v.ZERO for exponent in row])
            for value, row in zip(channel, exponents[16 * side : 16 * side + 16], strict=True)
        ]
        for side, channel in enumerate(nodes)
    ]
    channels.append([Dual(value, [v.ZERO] * size) for value in count])
    parents = [parent_products(channel) for channel in channels[:2]]
    wire = stage_wire(v, channels, equality, challenges, combiner)
    prefix_rows = [value.derivatives for values in parents for value in values]
    terminal_rows = [value.derivatives for value in wire[8:16]]
    all_rows = [*prefix_rows, *(value.derivatives for value in wire)]
    return len(row_basis(v, prefix_rows)), len(row_basis(v, [*prefix_rows, *terminal_rows])), len(row_basis(v, all_rows))


def algebraic_footprint(v):
    rng = Random(193)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    raw, free = [sample() for _ in range(9)], [sample() for _ in range(13)]
    nodes = joint_factors(v, raw, free, [v.ONE] * 7, v.ONE)
    assert reduce(mul, nodes[0]) == reduce(mul, nodes[1])
    count = [v.GEN**i for i in range(16)]
    equality, challenges, combiner = [sample(), sample()], [sample(), sample()], sample()
    for quarters in ((), (0,), (1, 3)):
        exponents = exponent_rows(v, quarters)
        assert all(sum(exponents[i][j] for i in range(16)) == sum(exponents[i][j] for i in range(16, 32)) for j in range(len(exponents[0])))
        extended = [list(channel) for channel in nodes]
        for quarter in quarters:
            noise = sample()
            for channel in extended:
                channel[quarter] *= noise
        print(
            "Additional unused-memory quarters",
            quarters,
            "unit mask rank",
            unit_rank(exponents),
            "prefix/terminal/wire ranks",
            wire_rank(v, exponents, extended, count, equality, challenges, combiner),
            flush=True,
        )
    for quarters in ((1, 3), (1, 2, 3)):
        exponents = exponent_rows(v, mul_quarters=quarters)
        extended = spread_factors([list(channel) for channel in nodes], [[sample() for _ in range(4)] for _ in quarters], quarters)
        print(
            "Additional MUL memory quarters",
            quarters,
            "unit mask rank",
            unit_rank(exponents),
            "prefix/terminal/wire ranks",
            wire_rank(v, exponents, extended, count, equality, challenges, combiner),
            flush=True,
        )
    exponents = exponent_rows(v, mul_quarters=(1, 2, 3))
    assert len(FREE) == 21
    assert all(not any(exponents[index]) for index in FIXED)
    assert all(sum(row[j] for row in exponents[:16]) == sum(row[j] for row in exponents[16:]) for j in range(34))
    assert unit_rank([exponents[index] for index in FREE]) == 21
    assert unit_rank(exponents) == 21
    assert unit_rank([[row[j] for j in (*range(9), *range(22, 34))] for row in exponents]) == 15
    print(
        "Integer unit pivots certify surjection onto all 21 unfixed balanced-frontier coordinates, for every finite multiplicative group", flush=True
    )


def spread_cycles(v, library, positions, indices, words):
    rows = []
    for bank, (base, payloads) in enumerate(zip(SPREAD_FRAMES, words, strict=True)):
        current = []
        for index, word in enumerate(payloads):
            frame = base + 128 * index
            templates = library.templates((v.OP_MUL, PAD_PC, [], True), v.GEN**frame)
            for limb, value in enumerate(word):
                templates[0][1][v.ARITH_COLUMNS.index(f"va_{limb}")] = v.E(value)
            templates[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.ONE
            row, closing = library.append(templates)
            ordinal = bank * MUL_NOISE + index
            positions[row], positions[closing] = (1 << 18) - 5 * MUL_NOISE + ordinal, 60001 + 2 * MUL_NOISE + ordinal
            current.append(row)
            indices["memory"].update(frame + offset for offset in (0, 1, 2, 64, 65, 66))
        rows.append(current)
    for opcode, height in ((v.OP_MUL, 18), (v.OP_JUMP, 17)):
        assigned = [positions[row] for row, (owner, _) in enumerate(library.rows) if owner == opcode]
        assert len(set(assigned)) == len(assigned) and all(0 <= position < 1 << height for position in assigned)
    return rows


def sample_frontier(v, fixed, sample):
    nodes = [sample() for _ in range(32)]
    for index, value in zip(FIXED, fixed, strict=True):
        nodes[index] = value
    nodes[31] = reduce(mul, nodes[:16]) / reduce(mul, nodes[16:31])
    return nodes[:16], nodes[16:]


def actual_frontier(v):
    rng = Random(194)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    generate = lambda n: [[rng.getrandbits(64) for _ in range(3)] for _ in range(n)]
    e, beta, points = v.eq_kernel([sample() for _ in range(4)]), sample(), [[sample() for _ in range(20)] for _ in range(2)]
    point, y = [sample() for _ in range(20)], [sample(), sample()]
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    words = [[generate(2) for _ in range(2)] for _ in range(BANKS)]
    gauges = [[[rng.getrandbits(64) or 1 for _ in range(2)] for _ in range(2)] for _ in range(BANKS)]
    payloads = [[generate(MUL_NOISE) for _ in range(5)] for _ in range(2)]
    xor_words, unused_words = [generate(XOR_NOISE) for _ in range(2)], [generate(32) for _ in range(2)]
    old = [rng.getrandbits(64) for _ in range(OLD_ROWS)]
    cofactors, counts, residuals, boundaries = [], [], {}, {}
    for payload, choice in product(range(2), repeat=2):
        library, positions, indices, a_rows, b_rows = two_inputs(v, *payloads[payload][:2], unused_words[payload])
        spread = spread_cycles(v, library, positions, indices, payloads[payload][2:])
        boundaries[payload, choice] = linear_view(v, library, positions, layout, bus, point, y, e, indices["memory"])
        a1, ag, c1a, cga = four_products(v, library, a_rows, 2, e, beta)
        b1, bg, c1b, cgb = four_products(v, library, b_rows, 3, e, beta)
        extra = [four_products(v, library, rows, 2, e, beta) for rows in spread]
        unused = reduce(
            mul, (fingerprint(v, e, beta, v.SEP_MEM, int(v.GEN ** (UNUSED + i)), v.ONE, word) for i, word in enumerate(unused_words[payload])), v.ONE
        )
        xor, _, x_indices = xor_library(v, old, xor_words[payload])
        xa1, xag, xc1, xcg = four_products(v, xor, [2 * (OLD_ROWS + i) for i in range(XOR_NOISE)], 2, e, beta)
        add_library(library, xor)
        for kind, selected in indices.items():
            selected.update(x_indices[kind])
        for bank in range(BANKS):
            local, selected = set_library(
                v,
                (0, 64),
                words[bank],
                (choice, 1 - choice),
                code_base=CODE_BASES[bank],
                frame_base=FRAME_BASE + 8 * BITS * bank,
                compact=True,
                gauges=gauges[bank],
            )
            add_library(library, local)
            for kind, values in indices.items():
                values.update(selected[kind])
        library.verify()
        raw = a1, ag, b1, bg, c1a * c1b, cga * cgb, xag * xcg, xa1 * xc1, unused
        free, residual, _, seed = view(v, library, indices, e, beta, points)
        push, pull, count = frontier(v, library, indices, e, beta, xor_log=6)
        factors = spread_factors(joint_factors(v, raw, free, residual, seed), extra, (1, 2, 3))
        normalized = [[node / factor for node, factor in zip(nodes, masks, strict=True)] for nodes, masks in zip((push, pull), factors, strict=True)]
        cofactors.append(normalized)
        counts.append(dict(library.exponents))
        retained = (*[push[index] for index in (8, 9, 14)], *[pull[index] for index in (8, 9, 14)], *residual[4:6])
        residuals[payload, choice] = retained
        replay = gkr_replay(v, count, seed=195, details=True, bus_leaves=(push, pull))
        full_depth_prefix(v, replay, 195)
        assert stage_wire(v, (push, pull, count), replay["equality"], replay["challenge"], replay["combiner"]) == replay["view"][3]
        sampled = sample_frontier(v, [(*push, *pull)[i] for i in FIXED], sample)
        simulated = gkr_replay(v, count, seed=195, details=True, bus_leaves=sampled)
        full_depth_prefix(v, simulated, 195)
    assert all(value == cofactors[0] for value in cofactors)
    assert all(value == counts[0] for value in counts)
    assert all(residuals[0, choice] == residuals[1, choice] for choice in range(2))
    delta = [a + b for a, b in zip(boundaries[0, 0], boundaries[1, 0], strict=True)]
    assert delta[:4] == delta[4:8] and any(delta[:4]) and any(delta[8:])
    print("Valid cycles in all four memory quarters match every full-frontier cofactor across private payload and occupancy changes", flush=True)
    print("Private MUL payload changes still have equal push/pull boundary deltas and three memory evaluations", flush=True)
    print("The 21-coordinate sampler preserves the ten fixed nodes and replays both complete layers through the depth-22 verifier", flush=True)


def spread_reservations(v):
    reservations(v, BITS, xor_rows=OLD_ROWS + XOR_NOISE, mul_rows=5 * MUL_NOISE)
    occupied = (
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (131072, 131072 + 44 * 128),
        (196608, 196608 + 96 * 128),
        (FRAME_BASE, FRAME_BASE + 8 * BANKS * BITS),
        (UNUSED, UNUSED + 32),
        (786432, 819200),
    )
    for quarter, start in enumerate(SPREAD_FRAMES, 1):
        end = start + MUL_NOISE * 128
        assert start >> 18 == (end - 1) >> 18 == quarter
        assert all(end <= left or right <= start for left, right in occupied)
        assert end < 1 << 20
    print("Three new 48-row banks fit their memory quarters and MUL/JUMP slots without increasing table heights", flush=True)


def concrete_bound():
    base, size = 1 << 64, 1 << 192
    rank = Fraction(base**2, (size - 2) ** 2)
    mul_error = Fraction((1 << 23) + 8 * MUL_NOISE + 8, size) + rank + Fraction(1, 1 << 384)
    xor_error = Fraction((1 << 23) + 8 * XOR_NOISE + 8, size) + rank + Fraction(1, 1 << 216)
    unused_error = Fraction((1 << 23) + 40, size) + rank + Fraction(1, 1 << 256)
    boundary, _ = error_bound()
    assert 5 * mul_error + xor_error + unused_error + boundary + Fraction(1, 1 << 159) < Fraction(1, 1 << 155)
    print(
        "Full first/second-layer wire and boundary reduce below 2^-155 to eight actual fields; no extra fold-challenge exclusion is needed",
        flush=True,
    )
    print("Residual simulation, later GKR layers, the PCS and Fiat-Shamir remain open; this is not full VM ZK", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    algebraic_footprint(verifier)
    actual_frontier(verifier)
    spread_reservations(verifier)
    concrete_bound()
