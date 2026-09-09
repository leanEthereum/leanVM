"""A valid-complement obstruction and an all-coordinate background diagnostic."""

from random import Random

from zk_count_children_audit import gkr_replay
from zk_count_first_round_audit import library_rows
from zk_pcs_audit import verifier_module


def middle_round_obstruction(verifier, geometric=False, twist=False):
    library, positions, masks = library_rows(verifier, tuple(range(4)), 2, geometric=geometric, twist=twist)
    column = verifier.JUMP_COLUMNS.index("cnt_c")
    real_switches, base = [], 6 << 6

    def repeats(count):
        template = library.templates(library.block(verifier.OP_JUMP), library.fresh_frame())
        return [library.append(template)[0] for _ in range(count)]

    for first in (0, 1):
        for second in (0, 1):
            rows = repeats(4)
            ordered = (rows[0], rows[3], rows[1], rows[2])
            locations = tuple(base + 4 * first + 8 * second + 16 * branch + child for branch in (0, 1) for child in (0, 1))
            assert not positions.keys() & set(locations)
            positions.update(zip(locations, ordered, strict=True))
            if second == 0:
                real_switches.append(tuple((row, column) for row in ordered))
        for branch in (0, 1):
            rows = repeats(2)
            for second, row in enumerate(rows):
                positions[base + 4 * first + 8 * second + 16 * branch + 2] = row
                positions[base + 4 * first + 8 * second + 16 * branch + 3] = repeats(1)[0]
    for position in range(512):
        if position not in positions:
            positions[position] = repeats(1)[0]
    assert len(positions) == len(library.rows) == 512
    library.verify()
    original_exponents, original_reads = dict(library.exponents), dict(library.reads)
    rng, observations = Random(136), []
    for choice in (0, 1):
        for switch in real_switches:
            library.set_labels(switch, (1, 2, 0, 3) if choice else (0, 3, 1, 2))
        views = []
        for randomize in (False, True, True):
            for switch in masks:
                initial, changed = ((0, 3, 2, 1), (1, 2, 3, 0)) if twist else ((0, 3, 1, 2), (1, 2, 0, 3))
                library.set_labels(switch, changed if randomize and rng.getrandbits(1) else initial)
            library.verify()
            assert dict(library.exponents) == original_exponents and dict(library.reads) == original_reads
            leaves = [library.rows[positions[position]][1][column] for position in range(512)]
            views.append(gkr_replay(verifier, leaves))
        assert all(view[0] == views[0][0] for view in views)
        if geometric:
            assert all(any(view[3][coefficient] != views[0][3][coefficient] for view in views) for coefficient in (6, 7))
        else:
            assert all(view[3][6:8] == views[0][3][6:8] for view in views)
        if twist:
            assert any(view[3][15] != views[0][3][15] for view in views)
        else:
            assert all(view[3][15] == views[0][3][15] for view in views)
        assert any(view[3][:4] != views[0][3][:4] for view in views)
        observations.append(views)
    assert observations[0][0][0] == observations[1][0][0]
    assert observations[0][0][3][:4] == observations[1][0][3][:4]
    assert observations[0][0][3][6] != observations[1][0][3][6]
    if twist:
        print(
            "Valid twisted trades and full geometric chains also supply noise to the separator-round quartic coefficient; joint hiding is not established",
            flush=True,
        )
    elif geometric:
        print(
            "Valid geometric counter chains restore second-round noise, but the untwisted separator-round quartic coefficient remains invariant",
            flush=True,
        )
    else:
        print(
            "Accepted GKR replays from 512 valid JUMP rows: the same ancestor prefix and fixed counter totals admit a second-round cubic coefficient that changes with the complement and is untouched by the six-bank masks",
            flush=True,
        )


def twisted_linearity(verifier):
    library, positions, switches = library_rows(verifier, (0,), 0, geometric=True, twist=True)
    column, views = verifier.JUMP_COLUMNS.index("cnt_c"), []
    for choice in range(4):
        for bit, switch in enumerate(switches[4:6]):
            library.set_labels(switch, (1, 2, 3, 0) if choice >> bit & 1 else (0, 3, 2, 1))
        leaves = [verifier.ONE] * 128
        for position, row in positions.items():
            leaves[position] = library.rows[row][1][column]
        views.append(gkr_replay(verifier, leaves))
    assert all(view[0] == views[0][0] for view in views)
    assert all(verifier.E.sum(coefficients) == verifier.ZERO for coefficients in zip(*(view[3] for view in views)))
    print("A complete twisted-bank layer remains binary-affine in its own bits, including all sumcheck messages and children", flush=True)


if __name__ == "__main__":
    verifier = verifier_module()
    middle_round_obstruction(verifier)
    middle_round_obstruction(verifier, geometric=True)
    middle_round_obstruction(verifier, geometric=True, twist=True)
    twisted_linearity(verifier)
