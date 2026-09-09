"""Same-frame program swaps covering the actual three-side GKR leaf boundary."""

import argparse
import subprocess
from fractions import Fraction
from pathlib import Path
from random import Random

from zk_flock_columns_audit import (
    METADATA_ROWS,
    PROGRAM,
    SHARED_PC_SUPPORT,
    build,
    randomize,
)
from zk_flock_coset_audit import novel_factors, reordered_index
from zk_flock_pair_opening_audit import blake_bus_forms, copy_position, matching_bound
from zk_memory_frames_audit import joint_root_bound
from zk_metadata_audit import SPARSE
from zk_pcs_audit import Tower, verifier_module
from zk_stacked_audit import binary_basis
from zk_three_point_audit import THREE_POINT_SUPPORT, three_point_error
from zk_two_point_audit import DENSE_FIXED, dense_fixed_error, fixed_observation_error


def certificate(verifier, library, pairs):
    field, rng = Tower(64, verifier), Random(509)
    terminal = [field.random(rng) for _ in range(18)]
    point = [verifier.E(*field.coords(field.random(rng))) for _ in range(26)]
    alphas = [verifier.E(*field.coords(field.random(rng))) for _ in range(4)]
    logical_leaf = [int(point[reordered_index(1 << bit).bit_length() - 1]) for bit in range(18)]
    forms, positions = blake_bus_forms(verifier, point, alphas)
    residual = verifier.Form(dict(forms[0].terms))
    residual.add_scaled(forms[1], verifier.GEN)
    columns = verifier.BLAKE2S_COLUMNS
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    selected = [columns.index(name) for name in (*PROGRAM, "fp")] + list(counts)
    value_columns = [column for column in range(37) if column not in selected]
    pc = columns.index("pc")
    assert all(len(term) == 1 for term, value in residual.terms.items() if pc in term and value != verifier.ZERO)
    assert all(residual.terms.get((column,), verifier.ZERO) == verifier.ZERO for column in counts)
    block = positions[1]["cnt_bc"]
    selector = verifier.eq_eval(point[18:], [verifier.E((block >> bit) & 1) for bit in range(8)])
    weight = verifier.eq_eval(alphas, [verifier.ONE, verifier.ZERO, verifier.ZERO, verifier.ZERO])
    coefficient = (verifier.ONE + verifier.GEN) * weight * selector
    assert residual.terms[pc,] == coefficient != verifier.ZERO
    matrix = [[form.terms.get((column,), verifier.ZERO) for column in counts] for form in forms]
    left, right = (counts.index(columns.index(name)) for name in ("cnt_cv1", "cnt_out0"))
    assert matrix[1][left] * matrix[2][right] != matrix[1][right] * matrix[2][left]

    def pair_weight(index, at):
        result = 1
        for bit, coin in enumerate(at[1:], 1):
            result = field.mul(result, coin if index >> bit & 1 else coin ^ 1)
        return result

    def packed(values):
        return sum(value << (192 * index) for index, value in enumerate(values))

    query = (1 << 18) + 1234
    factors = novel_factors(field, 18, query)
    directions, intermediate, pc_weights = [], [], []
    for bank, group in enumerate(pairs):
        for index, first, second, logical, _ in group:
            if bank == 9 and index not in DENSE_FIXED:
                continue
            a, b = library.rows[first][1], library.rows[second][1]
            t, z = pair_weight(logical, terminal), pair_weight(logical, logical_leaf)
            if bank < 9:
                difference = [int(a[column] + b[column]) for column in selected]
                leaf = [field.mul(z, int(form.evaluate(a.__getitem__) + form.evaluate(b.__getitem__))) for form in forms]
                metadata = [field.mul(t, value) for value in difference]
                counter = [field.mul(z, value) for value in difference[9:]]
                missing = leaf[0] ^ field.mul(int(verifier.GEN), leaf[1])
                assert a[columns.index("cnt_cv1")] + b[columns.index("cnt_cv1")] == a[columns.index("cnt_out0")] + b[columns.index("cnt_out0")]
                if bank == 0:
                    assert all(a[column] == b[column] for column in selected[1:9])
                    assert all(a[column] == verifier.ONE and b[column] == verifier.GEN for column in counts[:-1])
                    assert missing == field.mul(z, int(coefficient * (a[pc] + b[pc])))
                    pc_weights.append(t | (z << 192))
                directions.append(packed([*metadata, *leaf]))
                intermediate.append(packed([*metadata, *counter, missing]))
            else:
                raw = query
                physical = reordered_index(logical)
                for bit, factor in enumerate(factors):
                    if physical >> bit & 1:
                        raw = field.kmul(raw, factor)
                for number, column in enumerate(counts):
                    difference = int(a[column] + b[column])
                    metadata = field.mul(t, difference) << (192 * (9 + number))
                    count_delta = field.mul(z, difference)
                    leaf = [field.mul(int(row[number]), count_delta) for row in matrix]
                    raw_delta = field.kmul(raw, difference) if columns[column] in ("cnt_cv1", "cnt_out0") else 0
                    directions.append(metadata | (packed(leaf) << (19 * 192)) | (raw_delta << (22 * 192)))
                    intermediate.append(metadata | (count_delta << ((19 + number) * 192)) | (raw_delta << (30 * 192)))
    assert len(pc_weights) == 1278 and len(binary_basis(pc_weights)) == 384
    assert len(binary_basis(intermediate)) == 30 * 192 + 64 == 5824
    assert len(binary_basis(directions)) == 22 * 192 + 64 == 4288
    print(f"The actual residual coefficient is (1+g)*eq(alpha,1)*eq(zeta_high,{block}), with no counter term.", flush=True)
    print(
        "Native joint ranks: 5824 for the counter/residual interface, 4288 for terminal metadata, the full GKR leaf and raw PCS kernel.", flush=True
    )
    print("The ten auxiliary counts must be discarded before the full leaf replacement; retaining both is not this theorem.", flush=True)
    return selected, value_columns


def libraries(verifier):
    first, pairs, placement = build(verifier, shared_pc=True)
    assert set(SPARSE) < set(SHARED_PC_SUPPORT) and set(DENSE_FIXED) - set(SHARED_PC_SUPPORT) == {192, 193}
    selected, value_columns = certificate(verifier, first, pairs)
    randomize(verifier, first, pairs, selected, value_columns, counter_support=DENSE_FIXED)
    second, second_pairs, _ = build(verifier, code_shift=64, frame_shift=1 << 22)
    extra = {
        copy_position(bank, logical, shared_pc=True): row
        for bank, group in enumerate(second_pairs)
        for _, first, second, left, right in group
        for logical, row in ((left, first), (right, second))
    }
    assert len(placement) == 17916 and len(extra) == 16256
    assert not set(extra).intersection(placement) and not set(extra).intersection(METADATA_ROWS)
    assert all((index & 2047) not in THREE_POINT_SUPPORT and index >> 11 < 96 for index in extra)
    assert not set(first.images["memory"]).intersection(second.images["memory"])
    assert not set(first.images["code"]).intersection(second.images["code"])
    assert len(first.images["code"]) + len(second.images["code"]) == 72
    assert 98304 - len(placement) - len(extra) == 64132
    frames = 196608 - 2 * 4096 - len(SHARED_PC_SUPPORT)
    assert frames == 187138 and 32 * frames == 5988416
    assert (3 * ((1 << 22) - 1280) - 32 * frames) // 256 == 25744
    print("The enlarged first bank and remapped second bank are disjoint; all compression frames fit the same small-frame reservation.", flush=True)
    positions = sorted(reordered_index(index) for index in extra)
    assert all(left ^ right == 1 for left, right in zip(positions[::2], positions[1::2]))
    positions = positions[::2]
    Random(467).shuffle(positions)
    return positions


def error_bound():
    size = 1 << 192
    span = sum((Fraction(((1 << dimension) - 1) ** 2, size - 1) for dimension in (1, 2, 4, 8, 16)), Fraction())
    span += Fraction(((1 << 32) - 1) ** 2, (size - 1) * (1 << 32)) + Fraction(1, 1 << 256)
    error = three_point_error() + 4 * span + fixed_observation_error(64)
    error += dense_fixed_error(256) + dense_fixed_error(192) + dense_fixed_error(194)
    error += Fraction(4366, size) + matching_bound()
    assert error < Fraction(1, 1 << 154)
    assert joint_root_bound() + error < Fraction(1, 1 << 151)
    print("Exact full-leaf boundary error below 2^-154, and below 2^-151 jointly with the memory envelope and invariant shared root.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--matching", action="store_true", help="certify all query pairs for the remapped second library")
    arguments = parser.parse_args()
    positions = libraries(verifier_module())
    error_bound()
    if arguments.matching:
        subprocess.run(
            ["cargo", "run", "--release", "-p", "lean_vm", "--example", "zk_flock_pair_opening_audit", "--", "--matching-certificate"],
            input=" ".join(map(str, positions)),
            text=True,
            check=True,
            cwd=Path(__file__).resolve().parents[3],
        )
