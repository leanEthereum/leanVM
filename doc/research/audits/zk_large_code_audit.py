"""Code-log-19 relocation: exact bus minors, count-prefix law and restricted joint fibers."""

import argparse
import subprocess
from fractions import Fraction
from itertools import product
from pathlib import Path
from random import Random

from zk_count_adapter_audit import adapter_error
from zk_count_adapter_audit import positions as adapter_positions
from zk_flock_children_audit import (
    METADATA_ROWS,
    PROGRAM,
    THREE_POINT_SUPPORT,
    build,
    error_bound,
    families,
    pair,
    randomize,
)
from zk_flock_coset_audit import reordered_index
from zk_flock_lowbank_audit import build as low_build
from zk_flock_lowbank_audit import (
    decomposition_certificate,
    extra_joint_sources,
    extra_query_sources,
    positions,
    public_prefix_sources,
)
from zk_flock_multicoset_audit import (
    joint_query_sources,
    query_sources,
    source_certificate,
)
from zk_flock_pair_opening_audit import blake_bus_forms, lane_count_columns
from zk_memory_frames_audit import joint_root_bound
from zk_pcs_audit import Tower, verifier_module
from zk_two_point_audit import dense_fixed_error

CODE_LOG = 19
CODE_SHIFT = (1 << CODE_LOG) - (1 << 11)
FRAME_SHIFT = 1 << 16


def selector_product(left, right):
    powers = []
    for bit in range(8):
        a, b = (left >> bit) & 1, (right >> bit) & 1
        powers.append((2,) if a == b == 1 else ((0, 2) if a == b == 0 else (1, 2)))
    return set(product(*powers))


def geometry(verifier, field):
    rng = Random(739)
    point = [verifier.E(*field.coords(field.random(rng))) for _ in range(26)]
    alphas = [verifier.E(*field.coords(field.random(rng))) for _ in range(4)]
    forms, indices = blake_bus_forms(verifier, point, alphas, CODE_LOG)
    columns = verifier.BLAKE2S_COLUMNS
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    lane_columns = lane_count_columns(verifier, CODE_LOG)
    assert [columns[column] for column in lane_columns] == ["cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md", "cnt_bc"]
    layout = verifier.build_layout(range(16 << CODE_LOG), 25, (19, 19, 19, 19, 20, 18))
    assert layout.stack_log == 28
    assert layout.placements[verifier.BYTECODE_FINAL_COUNTERS].index == (51 << 22) + (1 << 21)
    smaller = verifier.build_layout(range(16 << 11), 25, (19, 19, 19, 19, 20, 18))
    assert [placement.index for placement in verifier.bus_layout((), layout.count).tables] == [
        placement.index for placement in verifier.bus_layout((), smaller.count).tables
    ]
    fingerprint = verifier.eq_eval(alphas, [verifier.ZERO, verifier.ONE, verifier.ZERO, verifier.ZERO])

    def selector(index):
        return verifier.eq_eval(point[18:], [verifier.E((index >> bit) & 1) for bit in range(8)])

    for column in counts:
        name = columns[column]
        pull = forms[1].terms[column,]
        count = forms[2].terms[column,]
        assert pull == fingerprint * selector(indices[1][name]) and count == selector(indices[2][name])
        assert forms[0].terms[column,] == verifier.GEN * pull
    for left, right, expected in (("cv1", "out0", False), ("cv0", "out0", False), ("m3", "cv0", True), ("m2", "cv0", True)):
        a, b = "cnt_" + left, "cnt_" + right
        polynomial = selector_product(indices[1][a], indices[2][b]) ^ selector_product(indices[1][b], indices[2][a])
        assert bool(polynomial) == expected
        if expected:
            assert max(map(sum, polynomial)) <= 16
            diagonal = set()
            for monomial in polynomial:
                diagonal ^= {sum(monomial)}
            assert diagonal == (set(range(7, 15)) if left == "m3" else {6, 14})
        i, j = columns.index(a), columns.index(b)
        minor = forms[1].terms[i,] * forms[2].terms[j,] + forms[1].terms[j,] * forms[2].terms[i,]
        assert (minor != verifier.ZERO) == expected
        print(f"Exact {left}/{right} minor: {'nonzero, degree at most 20' if polynomial else 'identically zero'}.", flush=True)
    residual = verifier.Form(dict(forms[0].terms))
    residual.add_scaled(forms[1], verifier.GEN)
    pc_weight = verifier.eq_eval(alphas, [verifier.ONE, verifier.ZERO, verifier.ZERO, verifier.ZERO])
    assert indices[1]["cnt_bc"] == 187
    assert residual.terms[columns.index("pc"),] == (verifier.ONE + verifier.GEN) * pc_weight * selector(187)
    assert all(residual.terms.get((column,), verifier.ZERO) == verifier.ZERO for column in counts)
    table = verifier.TABLES[verifier.OP_BLAKE2S]
    for block in (*table.flushes.push, *table.flushes.pull):
        for form in block:
            assert all(len(monomial) == 1 for monomial in form.terms if columns.index("pc") in monomial or any(c in monomial for c in counts))
    for _, blake, _ in adapter_positions():
        assert all((2 << 18) + row >= 1 << 19 for row in blake)
    print("Lane 59 has seven count blocks; adapter CV1 noise vanishes on U19. Code-final counts move to lane 51.", flush=True)


def active_low_pairs(blocks):
    mandatory = {reordered_index(2048 * bank + index) for bank in range(96) for index in THREE_POINT_SUPPORT}
    metadata = {
        reordered_index(row)
        for kind, banks, support in families(True)
        for bank in range(banks)
        for index in support
        for row in pair(kind, bank, index)
    }
    pairs = [(left + child, right + child) for left, right in blocks for child in range(16)]
    occupied = {row for endpoints in pairs for row in endpoints}
    general = {reordered_index(row) for row in range(96 << 11)} - mandatory - metadata - occupied
    destinations = sorted(row for row in general if row >> 14 == 1)[:30]
    for child in range(15):
        pairs[16 * 119 + child] = tuple(destinations[2 * child : 2 * child + 2])
    pairs[-1] = (437, 438)
    moved = {row for endpoints in pairs[-16:] for row in endpoints}
    assert len(moved) == 32 and moved <= general - set(map(reordered_index, METADATA_ROWS))
    assert all(row % 64 >= 16 for row in moved)
    assert len({row for endpoints in pairs for row in endpoints}) == 3840
    return pairs


def prefix_and_bound(field, blocks, row_pairs):
    sources = query_sources(field, 7)[0] + extra_query_sources(field, blocks, 7, row_pairs)
    assert len(sources) == 77180 + 13440
    public_prefix_sources([(polynomial, 0) for polynomial in sources], expected_bits=1085)
    total = error_bound(128) + Fraction(20, 1 << 192) + joint_root_bound(envelope_numerator=3 * (2 * 22 + 12))
    total += sum((dense_fixed_error(bits) for bits in (176, 48, 240)), Fraction()) + adapter_error()
    assert total < Fraction(1, 1 << 151)
    print("Replacing both degree-20 minors preserves the restricted ledger below 2^-151; the full prefix has 1085 fair bits.", flush=True)


def native_fiber(field, sources):
    sources, bits = public_prefix_sources(sources, expected_bits=1085)
    queries = [*range(12288, 12304), *range(262144, 262176)]
    prefix_words = 93 + (bits + 63) // 64
    payload = [len(queries), prefix_words, *queries, 0, prefix_words - 93, *range(93, prefix_words), len(sources)]
    for polynomial, prefix in sources:
        payload.append(len(polynomial))
        payload.extend(value for term in polynomial for value in term)
        words = [(word, (prefix >> (64 * word)) & field.mask) for word in range(prefix_words) if (prefix >> (64 * word)) & field.mask]
        payload.append(len(words))
        payload.extend(value for term in words for value in term)
    payload.append(0)
    result = subprocess.run(
        ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--query-prefix-fiber-certificate"],
        input=" ".join(map(str, payload)),
        text=True,
        capture_output=True,
        check=True,
        cwd=Path(__file__).resolve().parents[3],
    )
    print(result.stdout, end="", flush=True)
    assert "RANK 10109 10112\n" in result.stdout
    assert "PUBLIC_RANK 1085 1088\n" in result.stdout
    assert "FIBER_RANK 9024 9024\n" in result.stdout


def full_certificate(verifier, field, blocks, row_pairs):
    library, groups = build(verifier, True, frame_shift=FRAME_SHIFT, code_shift=CODE_SHIFT)
    assert set(library.images["code"]) <= {verifier.GEN ** (CODE_SHIFT + pc) for pc in range(1024, 1152)}
    source_certificate(verifier, *query_sources(field, 7), library_groups=(library, groups), code_log=CODE_LOG)
    old = joint_query_sources(field, verifier, 743, library_groups=(library, groups), code_log=CODE_LOG)
    extra = extra_joint_sources(field, verifier, 743, blocks, code_log=CODE_LOG, row_pairs=row_pairs)
    decomposition_certificate(field, verifier, old, extra, code_log=CODE_LOG, omitted_pairs=(119,))
    native_fiber(field, old + extra)
    selected = [verifier.BLAKE2S_COLUMNS.index(name) for name in (*PROGRAM, "fp")] + list(verifier.TABLES[verifier.OP_BLAKE2S].count_columns)
    randomize(verifier, library, groups, selected, [column for column in range(37) if column not in selected])
    low_build(verifier, blocks, frame_shift=FRAME_SHIFT, code_shift=CODE_SHIFT)
    payload = " ".join(str(value) for endpoints in blocks for value in endpoints)
    for arguments in (("--lowbank-certificate", "4096", "119"), ("--balanced-quotient-certificate", "119")):
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", *arguments],
            input=payload,
            text=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
    print("Code/frame-relocated valid cycles and the restricted joint fiber pass; common completion and full ZK are not certified.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--full", action="store_true", help="rebuild all metadata cycles, check the joint fiber and exhaustive erased query spans")
    arguments = parser.parse_args()
    reference = verifier_module()
    tower = Tower(64, reference)
    geometry(reference, tower)
    low_blocks = positions()
    low_pairs = active_low_pairs(low_blocks)
    prefix_and_bound(tower, low_blocks, low_pairs)
    if arguments.full:
        full_certificate(reference, tower, low_blocks, low_pairs)
