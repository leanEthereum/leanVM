"""Frozen coarse count products in the balanced source and an actual GKR child leak."""

import argparse
import subprocess
from pathlib import Path

from zk_column_count_audit import Library
from zk_flock_children_audit import families, pair
from zk_flock_coset_audit import reordered_index
from zk_flock_lowbank_audit import positions
from zk_gkr_second_wire_audit import full_depth_prefix
from zk_pcs_audit import verifier_module
from zk_sparse_gkr_audit import replay, weight


def geometry(verifier):
    layout = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    count = verifier.bus_layout((), layout.count)
    assert count.depth == 24 and verifier.bus_layout((0, 25, 11), layout.push).depth == 26
    offsets = {}
    for block, placement in zip(layout.count, count.tables, strict=True):
        assert placement.variables >= 18 and placement.index % (1 << 14) == 0
        ((column,),) = block.coordinates[0].terms
        assert block.coordinates[0].terms[column,] == verifier.ONE
        offsets[block.owner, column] = placement.index
    assert len(offsets) == 28
    swaps = 0
    for kind, banks, support in families(True):
        for bank in range(banks):
            for index in support:
                left, right = map(reordered_index, pair(kind, bank, index))
                assert left >> 14 == right >> 14
                swaps += 10 if kind in ("count", "wide") else 1
    for left, right in positions():
        assert left >> 14 == right >> 14 == 0
        swaps += 16 * 10
    assert swaps == 129788
    cv1 = verifier.BLAKE2S_COLUMNS.index("cnt_cv1")
    assert offsets[verifier.OP_BLAKE2S, cv1] == 49 << 18
    print("All 129788 metadata bits preserve each aligned 2^14-leaf count product; the native count block starts at 49 * 2^18.", flush=True)
    return offsets


def cycles(verifier, secret, offsets):
    library, placement = Library(verifier), {}
    for group, target in enumerate((9, 20) if secret == 0 else (20, 9)):
        frame = verifier.GEN ** ((1 << 22) + 1280 + 32 * group)
        reference = library.row(verifier.OP_BLAKE2S, 101, frame)
        names = verifier.BLAKE2S_COLUMNS
        value = (reference[names.index("cv1_lo")], reference[names.index("cv1_hi")], verifier.ZERO)
        library.images["memory"][int(frame * verifier.GEN**20)] = tuple(map(int, value))
        row = library.row(verifier.OP_DEREF, 100, frame, pointer=frame * verifier.GEN**target)
        for name, entry in zip(("o1", "o2", "o3", "v3_0", "v3_1", "v3_2"), (verifier.GEN**18, verifier.ONE, verifier.GEN**19, *value)):
            row[verifier.DEREF_COLUMNS.index(name)] = entry
        placement[library.append([(verifier.OP_DEREF, row)])[0]] = group
        for index in range(8):
            row = library.row(verifier.OP_BLAKE2S, 101 + index, frame)
            row_id = library.append([(verifier.OP_BLAKE2S, row)])[0]
            placement[row_id] = reordered_index((96 << 11) + 8 * group + index)
        row = library.row(verifier.OP_JUMP, 109, frame, 100)
        for name, offset in zip(("o_c", "o_d", "o_f"), (24, 25, 26)):
            row[verifier.JUMP_COLUMNS.index(name)] = verifier.GEN**offset
        placement[library.append([(verifier.OP_JUMP, row)])[0]] = group
    library.verify()
    frontier = {}
    for row_id, (opcode, row) in enumerate(library.rows):
        for column in verifier.TABLES[opcode].count_columns:
            index = (offsets[opcode, column] + placement[row_id]) >> 14
            frontier[index] = frontier.get(index, verifier.ONE) * row[column]
    products = tuple(library.exponents[table.opcode, column] for table in verifier.TABLES for column in table.count_columns)
    return {index: value for index, value in frontier.items() if value != verifier.ONE}, products


def certificate(verifier):
    offsets = geometry(verifier)
    first, roots = cycles(verifier, 0, offsets)
    second, other_roots = cycles(verifier, 1, offsets)
    assert roots == other_roots and len(roots) == 28
    differences = {index for index in first.keys() | second.keys() if first.get(index, verifier.ONE) != second.get(index, verifier.ONE)}
    assert differences == {784, 785}
    assert [first[index] for index in (784, 785)] == [verifier.GEN**36, verifier.GEN**28]
    assert [second[index] for index in (784, 785)] == [verifier.GEN**28, verifier.GEN**36]
    seed = 659
    views = []
    for frontier in (first, second):
        view = replay(verifier, ({}, {}, frontier), 12, seed)
        full_depth_prefix(verifier, view, seed, depth=26)
        assert len(view["challenge"]) == 10
        views.append(view)
    assert views[0]["coins"] == views[1]["coins"]
    assert views[0]["result"][0] == views[1]["result"][0]
    assert (
        views[0]["children"][2][0] + views[1]["children"][2][0]
        == ((verifier.GEN**36 + verifier.GEN**28) * weight(verifier, views[0]["challenge"], 196))
        != verifier.ZERO
    )
    print("Two valid small-frame cycle unions have identical 28 column products but different coarse nodes 784 and 785.", flush=True)
    print("Six accepted depth-26 GKR packets expose their nonzero degree-10 difference; this replay excludes the later VM proof.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="also verify two complete small-frame VM executions with the same count root")
    arguments = parser.parse_args()
    certificate(verifier_module())
    if arguments.native:
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--balanced-pointer-witnesses"],
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
