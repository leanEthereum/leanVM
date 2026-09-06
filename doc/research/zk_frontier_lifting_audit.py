"""A next-frontier contract and valid-cycle count-refinement example, not full ZK."""

from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_column_count_audit import Library
from zk_count_children_audit import SPARSE, gkr_replay
from zk_even_children_audit import four_products
from zk_frontier_entropy_audit import unit_rank
from zk_gkr_first_packet_audit import fingerprint, linear_view
from zk_gkr_second_wire_audit import full_depth_prefix, parent_products, stage_wire
from zk_pcs_audit import verifier_module


def fiber_matrix(v):
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    assert bus.depth == 22 and bus.framework[2].index >> 16 == 16 and bus.framework[2].variables == 20
    groups = [(side, parent) for side in range(2) for parent in range(16) if side != 0 or parent not in range(4, 8)]
    matrix = [[0] * (3 * len(groups)) for _ in range(128)]
    selected = []
    for group, (side, parent) in enumerate(groups):
        start = 64 * side + 4 * parent
        for child in range(3):
            matrix[start + child][3 * group + child] = 1
            matrix[start + 3][3 * group + child] = -1
            selected.append(start + child)
    assert len(groups) == 28 and len(selected) == 84
    assert unit_rank([matrix[index] for index in selected]) == 84
    assert all(sum(matrix[start + child][column] for child in range(4)) == 0 for start in range(0, 128, 4) for column in range(84))
    assert all(not any(matrix[index]) for index in range(16, 32))
    print("The 16-to-64 fingerprint lift has an 84-dimensional quartet-product kernel with an integer identity minor", flush=True)


def lift(v, parents, public_code, sample):
    children = []
    for side in range(2):
        nodes = []
        for parent, value in enumerate(parents[side]):
            if side == 0 and 4 <= parent < 8:
                quartet = public_code[4 * (parent - 4) : 4 * (parent - 3)]
                assert reduce(mul, quartet) == value
            else:
                quartet = [sample() for _ in range(3)]
                quartet.append(value / reduce(mul, quartet))
            nodes.extend(quartet)
        children.append(nodes)
    assert [parent_products(nodes) for nodes in children] == parents
    return children


def sampler_certificate(v):
    rng = Random(200)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    public_code = [sample() for _ in range(16)]
    parents = [[sample() for _ in range(16)] for _ in range(2)]
    parents[0][4:8] = parent_products(public_code)
    parents[1][-1] = reduce(mul, parents[0]) / reduce(mul, parents[1][:-1])
    count = [v.GEN**index for index in range(64)]
    coarse = gkr_replay(v, parent_products(count), seed=201, details=True, bus_leaves=parents)
    expected_prefix = (*coarse["view"][0], *coarse["view"][3])
    transcripts = []
    for _ in range(2):
        nodes = lift(v, parents, public_code, sample)
        replay = gkr_replay(v, count, seed=201, details=True, bus_leaves=nodes)
        assert replay["view"][0] == expected_prefix
        assert len(replay["challenge"]) == 4 and len(replay["view"][3]) == 28
        assert stage_wire(v, (*nodes, count), replay["equality"], replay["challenge"], replay["combiner"]) == replay["view"][3]
        full_depth_prefix(v, replay, 201)
        transcripts.append(replay["view"][3])
    assert transcripts[0] != transcripts[1]
    print(
        "Two independent fiber lifts preserve the entire two-layer wire and change the third; all three layers replay through the depth-22 reader",
        flush=True,
    )


def fine_frontier(v, library, positions, indices, e, beta):
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus, counts = v.bus_layout((0, 20, 20), layout.push), v.bus_layout((), layout.count)
    assert bus.depth == 22
    channels = [[v.ONE] * 64 for _ in range(3)]
    for side, blocks, placements in ((0, layout.push, bus.tables), (1, layout.pull, bus.tables), (2, layout.count, counts.tables)):
        for block, place in zip(blocks, placements, strict=True):
            for row_id, (opcode, row) in enumerate(library.rows):
                if opcode != block.owner:
                    continue
                values = [form.evaluate(row.__getitem__) for form in block.coordinates]
                value = values[0] if side == 2 else beta + v.dot(e[: len(values)], values)
                assert positions[row_id] < 1 << place.variables
                channels[side][(place.index + positions[row_id]) >> 16] *= value
    for kind, start, separator in (("memory", 0, v.SEP_MEM), ("code", 16, v.SEP_BYTECODE)):
        assert {int(v.GEN**index) for index in indices[kind]} == library.images[kind].keys()
        for index in indices[kind]:
            address = int(v.GEN**index)
            for side, label in ((0, v.ONE), (1, v.GEN ** library.reads[kind, address])):
                channels[side][start + (index >> 16)] *= fingerprint(v, e, beta, separator, address, label, library.images[kind][address])
    return channels


def count_refinement(v):
    rng = Random(202)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    library = Library(v)
    pc, frame = 4096, 65536
    template = [(v.OP_JUMP, library.row(v.OP_JUMP, pc, v.GEN**frame, pc))]
    rows = [library.append(template)[0] for _ in range(4)]
    positions = dict(zip(rows, (0, 1 << 16, 1, (1 << 16) + 1), strict=True))
    indices = {"memory": set(range(frame, frame + 3)), "code": {pc}}
    library.verify()
    first = fine_frontier(v, library, positions, indices, e, beta)
    exponents, counts = dict(library.exponents), dict(library.reads)
    column = v.JUMP_COLUMNS.index("cnt_f")
    library.set_labels(((rows[0], column), (rows[1], column)), (1, 0))
    library.verify()
    second = fine_frontier(v, library, positions, indices, e, beta)
    assert exponents == dict(library.exponents) and counts == dict(library.reads)
    assert [parent_products(nodes) for nodes in first] == [parent_products(nodes) for nodes in second]
    assert first[2] != second[2]
    replays = [gkr_replay(v, nodes[2], seed=203, details=True, bus_leaves=nodes[:2]) for nodes in (first, second)]
    assert replays[0]["view"][0] == replays[1]["view"][0]
    assert replays[0]["view"][3] != replays[1]["view"][3]
    for replay in replays:
        full_depth_prefix(v, replay, 203)
    print(
        "Four valid identical JUMPs preserve every count-column product, final counter and coarse frontier while changing the next count frontier",
        flush=True,
    )
    print(
        "The actual third-layer wire changes; this is not a witness-leakage attack or a counterexample to the earlier projected simulator", flush=True
    )


def striped_factors(v, products):
    push, pull = [[v.ONE] * 64 for _ in range(2)]
    for stripe, (a1, ag, c1, cg) in enumerate(products):
        push[40 + stripe], pull[40 + stripe] = ag, a1
        push[48 + stripe], pull[48 + stripe] = cg, c1
        push[7] *= a1 * c1
        pull[7] *= ag * cg
    return push, pull


def striped_payloads(v):
    rng = Random(204)
    sample = lambda: v.E(*(rng.getrandbits(64) for _ in range(3)))
    e, beta = v.eq_kernel([sample() for _ in range(4)]), sample()
    point, y = [sample() for _ in range(20)], [sample(), sample()]
    layout = v.build_layout(range(16 << 20), 20, (6, 18, 15, 4, 17, 3))
    bus = v.bus_layout((0, 20, 20), layout.push)
    occupied = {8 * ((bank << 12) + s) + low for bank in range(4) for s in SPARSE for low in range(8)}
    occupied.update(range(1536, 1580))
    occupied.update(range(60000, 60241))
    slots = [slot for slot in range(1 << 16) if slot not in occupied][:192]
    assert len(slots) == 192
    assert 2 * 4 * 3840 + 2 * len(SPARSE) + 2 * 3840 + 192 < (1 << 17) - len(occupied)
    frame_start, frame_end = 7 << 16, (7 << 16) + 192 * 128
    previous_frames = (
        (65536, 65536 + 4 * 5 * 4 * len(SPARSE)),
        (131072, 131072 + 44 * 128),
        (196608, 196608 + 96 * 128),
        (262144, 262144 + 8 * 4 * 3840),
        (393216, 393216 + 48 * 128),
        (524288, 524288 + 32),
        (557056, 557056 + 48 * 128),
        (589824, 589824 + 16 * 3840),
        (786432, 819200 + 48 * 128),
    )
    assert all(frame_end <= start or end <= frame_start for start, end in previous_frames)
    cofactors, counts, boundaries = [], [], []
    for random_words in (False, True):
        library, positions = Library(v), {}
        indices = {"memory": set(), "code": {32770, 32771}}
        groups = []
        for stripe in range(4):
            group = []
            for index in range(48):
                ordinal = 48 * stripe + index
                frame = (7 << 16) + 128 * ordinal
                templates = library.templates((v.OP_MUL, 32770, [], True), v.GEN**frame)
                for limb in range(3):
                    templates[0][1][v.ARITH_COLUMNS.index(f"va_{limb}")] = v.E(rng.getrandbits(64) if random_words else 0)
                templates[0][1][v.ARITH_COLUMNS.index("vb_0")] = v.ONE
                row, closing = library.append(templates)
                positions[row], positions[closing] = (stripe << 16) + (1 << 15) + index, slots[ordinal]
                group.append(row)
                indices["memory"].update(frame + offset for offset in (0, 1, 2, 64, 65, 66))
            groups.append(group)
        assert {index >> 16 for index in indices["memory"]} == {7}
        assert all(positions[row] >> 16 == stripe for stripe, group in enumerate(groups) for row in group)
        assert max(positions[row] for row in groups[-1]) < (1 << 18) - 240 - 7680
        library.verify()
        products = [four_products(v, library, group, 2, e, beta) for group in groups]
        native = fine_frontier(v, library, positions, indices, e, beta)
        factors = striped_factors(v, products)
        fixed = [[node / factor for node, factor in zip(nodes, masks, strict=True)] for nodes, masks in zip(native[:2], factors, strict=True)]
        cofactors.append(fixed)
        counts.append(native[2])
        boundaries.append(linear_view(v, library, positions, layout, bus, point, y, e, indices["memory"]))
        aggregates = [reduce(mul, column, v.ONE) for column in zip(*products, strict=True)]
        resampled = [[sample() for _ in range(4)] for _ in range(3)]
        resampled.append([value / reduce(mul, (quad[index] for quad in resampled), v.ONE) for index, value in enumerate(aggregates)])
        changed_factors = striped_factors(v, resampled)
        assert [parent_products(nodes) for nodes in factors] == [parent_products(nodes) for nodes in changed_factors]
        assert all(
            before[index] == after[index]
            for before, after in zip(factors, changed_factors, strict=True)
            for index in range(64)
            if index not in (*range(40, 44), *range(48, 52))
        )
        changed = [
            [cofactor * factor for cofactor, factor in zip(nodes, masks, strict=True)] for nodes, masks in zip(fixed, changed_factors, strict=True)
        ]
        replays = [gkr_replay(v, native[2], seed=205, details=True, bus_leaves=nodes) for nodes in (native[:2], changed)]
        assert replays[0]["view"][0] == replays[1]["view"][0]
        assert replays[0]["view"][3] != replays[1]["view"][3]
        full_depth_prefix(v, replays[1], 205)
        for row_id in groups[0]:
            opcode, row = library.rows[row_id]
            block = v.TABLES[opcode].flushes
            push, pull = [beta + v.dot(e[:6], [form.evaluate(row.__getitem__) for form in getattr(block, side)[2]]) for side in ("push", "pull")]
            assert (push + pull) / (e[2] * (v.ONE + v.GEN)) == row[v.ARITH_COLUMNS.index("cnt_a")]
    assert cofactors[0] == cofactors[1] and counts[0] == counts[1]
    delta = [after + before for before, after in zip(*boundaries, strict=True)]
    assert delta[:4] == delta[4:8] and any(delta[:4]) and any(delta[8:])
    print(
        "Four valid 48-word MUL stripes supply twelve product-preserving fine-frontier directions; the memory node and count frontier stay fixed",
        flush=True,
    )
    print("The actual boundary has seven linear payload fields; native leaf push/pull differences retain their base-field count relation", flush=True)


def error_bounds():
    base, size, words = 1 << 64, 1 << 192, 48
    mixing_squared = Fraction(((size - 1) ** 4 - 1) * size**7, 4) * Fraction(16 * size, (base**2 - 4) ** 2) ** words
    assert mixing_squared < Fraction(1, 1 << 768)
    one_bank = Fraction((1 << 23) + 8 * words + 8, size) + Fraction(base**2, (size - 2) ** 2) + Fraction(1, 1 << 384)
    assert 8 * one_bank < Fraction(1, 1 << 165)
    assert Fraction(base, size - 1) < Fraction(1, 1 << 127)
    print("Preserving the actual coarse marginal costs at most twice the four-bank hybrid error, below 2^-165", flush=True)
    print(
        "An independent-unit leaf target violates the exact count relation with probability at least 1 - Q/(q-1); this invariant cannot reach the leaves",
        flush=True,
    )


if __name__ == "__main__":
    verifier = verifier_module()
    fiber_matrix(verifier)
    sampler_certificate(verifier)
    count_refinement(verifier)
    striped_payloads(verifier)
    error_bounds()
