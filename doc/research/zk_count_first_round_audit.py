"""Joint first-round and final-child count masks, excluding intervening rounds."""

from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_column_count_audit import Library
from zk_count_children_audit import EDGES, SPARSE, gkr_replay
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis

BANKS = ((0, EDGES[0]), (1, EDGES[0]), (2, EDGES[0]), *((0, edge) for edge in EDGES[1:]))


def library_rows(verifier, sparse=SPARSE, sparse_bits=12, geometric=False, twist=False, anchors=None):
    library, positions, switches = Library(verifier), {}, []
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    anchors = {} if anchors is None else anchors

    def repeats(count):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        return [library.append(template)[0] for _ in range(count)]

    for bank, (kind, edge) in enumerate(BANKS):
        indices = sorted(set(sparse) | {index // 2 for source, index in anchors if source == bank})
        for index in indices:
            base = (bank << (sparse_bits + 4)) + 8 * index
            for parity in (0, 1):
                anchor = anchors.get((bank, 2 * index + parity))
                if index not in sparse and anchor is None:
                    continue
                rows = [repeats(1)[0] for _ in range(4)] if anchor == "ones" else repeats(4)
                ordered = (rows[0], rows[3], rows[2], rows[1]) if twist and anchor is None else (rows[0], rows[3], rows[1], rows[2])
                locations = tuple(base + 4 * parity + (branch << (sparse_bits + 3)) + child for branch in (0, 1) for child in edge)
                assert not positions.keys() & set(locations)
                positions.update(zip(locations, ordered, strict=True))
                if anchor is None:
                    switches.append(tuple((row, column) for row in ordered))
            if geometric:
                continue
            for branch in (0, 1):
                for index_in_pair, child in enumerate(child for child in range(4) if child not in edge):
                    rows = repeats(2) if index_in_pair < kind else [repeats(1)[0] for _ in range(2)]
                    for parity, row in enumerate(rows):
                        position = base + 4 * parity + (branch << (sparse_bits + 3)) + child
                        assert position not in positions
                        positions[position] = row
        if geometric:
            size = 1 << (sparse_bits + 1)
            for index_in_pair, child in enumerate(child for child in range(4) if child not in edge):
                rows = repeats(2 * size) if index_in_pair < kind else [repeats(1)[0] for _ in range(2 * size)]
                for index, row in enumerate(rows):
                    position = (bank << (sparse_bits + 4)) + 4 * index + child
                    assert position not in positions
                    positions[position] = row
    return library, positions, switches


def isa_certificate(verifier):
    library, positions, switches = library_rows(verifier)
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    assert len(positions) == len(library.rows) == 43008
    assert len(switches) == 5376

    def parents():
        return {base: reduce(mul, (library.rows[positions[base + offset]][1][column] for offset in range(4))) for base in positions if base % 4 == 0}

    library.verify()
    before, exponents, reads = parents(), dict(library.exponents), dict(library.reads)
    rng = Random(134)
    for switch in switches:
        if rng.getrandbits(1):
            library.set_labels(switch, (1, 2, 0, 3))
    library.verify()
    assert parents() == before and dict(library.exponents) == exponents and dict(library.reads) == reads
    assert set(before.values()) == {verifier.GEN**exponent for exponent in (3, 4, 5)}
    print("43008 valid JUMP rows: six separated banks and all three backgrounds preserve the bus, final counts and every quartet product", flush=True)


def rank_certificate(verifier):
    field, rng = Tower(64, verifier), Random(135)
    equality, challenge = ([field.random(rng) for _ in range(17)] for _ in range(2))
    first_weights, child_weights = field.eq(equality[1:13]), field.eq(challenge[1:13])
    first_tags, child_tags = field.eq(equality[14:]), field.eq(challenge[14:])
    g = int(verifier.GEN)
    step, g2 = 1 ^ g, field.mul(g, g)
    squared_step = field.mul(step, step)
    product_step = field.mul(g2, squared_step)
    first_directions = ((1, 0, 0), (1, step, 0), (1, squared_step, squared_step))
    columns = []
    for bank, (kind, (left, right)) in enumerate(BANKS):
        for index in SPARSE:
            first_scale = field.mul(product_step, field.mul(first_tags[bank], first_weights[index]))
            first_vector = sum(
                field.mul(first_scale, coefficient) << (192 * coordinate) for coordinate, coefficient in enumerate(first_directions[kind])
            )
            child_scale = field.mul(step, field.mul(child_tags[bank], child_weights[index]))
            for parity in (0, 1):
                scale = field.mul(child_scale, challenge[0] ^ (1 ^ parity))
                child_vector = (scale << (192 * (3 + left))) ^ (field.mul(g2, scale) << (192 * (3 + right)))
                columns.append(first_vector ^ child_vector)
    assert len(columns) == 5376 and len(binary_basis(columns)) == 1344
    size = 1 << 192
    delta = sum((Fraction(((1 << d) - 1) ** 2, size - 1) for d in (1, 2, 4, 8, 16)), Fraction())
    delta += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    assert 2 * delta + Fraction(78, size) < Fraction(1, 1 << 157)
    print("Joint first coefficients and final children: binary rank 1344; exact sparse-span bound below 2^-157 for depth at most 40", flush=True)


def small_replay(verifier):
    for depth in (4, 5, 6, 7):
        gkr_replay(verifier, [verifier.GEN ** (index % 13) for index in range(1 << depth)])
    library, positions, switches = library_rows(verifier, (0,), 0)
    column = verifier.JUMP_COLUMNS.index("cnt_c")

    def leaves():
        result = [verifier.ONE] * 128
        for position, row in positions.items():
            result[position] = library.rows[row][1][column]
        return result

    before = gkr_replay(verifier, leaves())
    for switch in switches[::3]:
        library.set_labels(switch, (1, 2, 0, 3))
    library.verify()
    after = gkr_replay(verifier, leaves())
    assert before[0] == after[0]
    assert before[3][:4] != after[3][:4] and before[2] != after[2]
    print(
        "Odd/even GKR schedules derive first endpoints from the preceding packet; the ISA-derived separated banks change both observations",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    small_replay(verifier)
    rank_certificate(verifier)
    isa_certificate(verifier)
