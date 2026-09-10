"""Public range-probe prefix, shifted unused masks and unchanged memory envelopes."""

import argparse
from fractions import Fraction
from random import Random

from zk_flock_coset_audit import novel_factors
from zk_memory_frames_audit import (
    actual_lane_schedule_certificate,
    joint_root_bound,
    pinned_translation,
)
from zk_pcs_audit import Audit, Tower, edot, verifier_module


def shifted_wire(field):
    for mode in ("random", "zero", "prefix", "small-subspace"):
        audit = Audit(field, 10, (3, 2), (5, 3), seed=17, query_mode=mode).run()
        rng = Random(719)
        difference = [rng.getrandbits(64) if i // 128 < 3 and i % 128 >= (104 if i < 128 else 40) else 0 for i in range(1024)]
        translated = pinned_translation(audit, difference, 64)
        assert translated[:64] == [0] * 64
        assert translated[104:128] == difference[104:128] and any(difference[104:128])
        assert all(edot(field, row, translated) == 0 for row in audit.rows)
        print(f"Public probe prefix, {mode}: every multilevel algebraic wire observation is annihilated by legal mask translations.", flush=True)


def basis_and_allocation(field):
    prefix, mask, length = 1 << 16, 1280, 1 << 22
    assert prefix == 65536 and mask <= prefix and prefix + mask < length
    rng = Random(727)
    for query in (0, 1, 2, 3, prefix - 1, prefix, prefix + 1, 1 << 22, (1 << 23) - 1):
        factors = novel_factors(field, 22, query)
        assert (factors[16] == 0) == (query < prefix)
        low = field.novel(11, query)
        for index in (0, 1, 255, 256, 1023, 1279):
            position = prefix + index
            value = 1
            for bit in range(22):
                if position >> bit & 1:
                    value = field.kmul(value, factors[bit])
            assert value == field.kmul(factors[16], low[index])
        if query < prefix:
            assert not any(factors[16:])

    frames = ({*range(21500), 65535}, set(range(57608)), set(range(98304)))
    occupied_slots = [{frame // 8 for frame in allocated} for allocated in frames]
    runs = []
    for segment, allocated in enumerate(frames):
        shift = prefix if segment == 0 else 0
        occupied = occupied_slots[segment]
        limit = (length - shift - mask) // 256
        start = None
        for slot in range(limit + 1):
            if slot < limit and slot not in occupied:
                if start is None:
                    start = slot
            elif start is not None:
                runs.append((segment, start, slot))
                start = None
        assert all(shift + mask + 32 * frame + 32 <= length for frame in allocated)
    assert runs == [(0, 2688, 8191), (0, 8192, 16123), (1, 7201, 16379), (2, 12288, 16379)]
    capacity = sum(end - start for _, start, end in runs)
    assert capacity == 26703
    for largest in (1, 2, 25, 64, 256, 4091):
        budget = capacity - 3 * (largest - 1)
        quotient, residue = divmod(budget, largest)
        packed = [largest] * quotient + ([residue] if residue else [])
        mixed, remaining = [], budget
        while remaining:
            size = rng.randrange(1, min(largest, remaining) + 1)
            mixed.append(size)
            remaining -= size
        for requests in ([1] * budget, packed, packed[::-1], mixed):
            run, cursor, wasted = 0, runs[0][1], 0
            for size in requests:
                while size > runs[run][2] - cursor:
                    wasted += runs[run][2] - cursor
                    run += 1
                    assert run < len(runs)
                    cursor = runs[run][1]
                segment, start, end = runs[run]
                assert start <= cursor < cursor + size <= end
                shift = prefix if segment == 0 else 0
                first = segment * length + shift + mask + 256 * cursor
                assert first >= segment * length + shift + mask and first + 256 * size <= (segment + 1) * length
                assert not any(slot in occupied_slots[segment] for slot in range(cursor, cursor + size))
                cursor += size
            assert wasted <= 3 * (largest - 1)
    print("Native-basis shifted support and all four relocated payload runs pass; 26703 free slots remain before fragmentation.", flush=True)


def relocated_library(verifier, field):
    from zk_count_adapter_audit import adapter_error
    from zk_flock_children_audit import build, certificate, error_bound, randomize
    from zk_flock_lowbank_audit import build as low_build
    from zk_flock_lowbank_audit import positions
    from zk_flock_multicoset_audit import query_sources, source_certificate
    from zk_flock_pair_opening_audit import blake_bus_forms
    from zk_two_point_audit import dense_fixed_error

    shift = 1 << 16
    library, groups = build(verifier, True, frame_shift=shift)
    source_certificate(verifier, *query_sources(field), library_groups=(library, groups))
    columns = verifier.BLAKE2S_COLUMNS
    pc, fp = columns.index("pc"), columns.index("fp")
    counts = verifier.TABLES[verifier.OP_BLAKE2S].count_columns
    scale = verifier.GEN**shift
    table = verifier.TABLES[verifier.OP_BLAKE2S]
    for block in (*table.flushes.push, *table.flushes.pull):
        for form in block:
            assert all(len(monomial) == 1 for monomial in form.terms if pc in monomial or any(column in monomial for column in counts))
    for index, first, second, _, _ in groups["operand", 7]:
        difference = library.rows[first][1][fp] + library.rows[second][1][fp]
        assert difference == scale * verifier.GEN**1280 * (verifier.ONE + verifier.GEN**32) * verifier.GEN ** (64 * index)

    rng = Random(733)
    point = [verifier.ZERO, verifier.ZERO, *(verifier.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(24))]
    alphas = [verifier.E(*(rng.getrandbits(64) for _ in range(3))) for _ in range(4)]
    forms, _ = blake_bus_forms(verifier, point, alphas)
    residual = verifier.Form(dict(forms[0].terms))
    residual.add_scaled(forms[1], verifier.GEN)
    assert all(residual.terms.get((column,), verifier.ZERO) == verifier.ZERO for column in counts)
    for form in forms:
        changed = verifier.Form({monomial: coefficient * scale ** monomial.count(fp) for monomial, coefficient in form.terms.items()})
        assert all(changed.terms.get((column,), verifier.ZERO) == form.terms.get((column,), verifier.ZERO) for column in counts)
    coefficient = residual.terms[pc,]
    assert coefficient != verifier.ZERO
    for child in range(4):
        for _, first, second, _, _ in groups["pc", child]:
            left, right = library.rows[first][1], library.rows[second][1]
            assert left[fp] == right[fp]
            assert residual.evaluate(left.__getitem__) + residual.evaluate(right.__getitem__) == coefficient * (left[pc] + right[pc])
    print("Relocated frame directions are nonzero rescalings; the count-plane coefficients and all PC residual directions are unchanged.", flush=True)

    selected, values = certificate(verifier, library, groups)
    randomize(verifier, library, groups, selected, values)
    low_build(verifier, positions(), frame_shift=shift)
    total = error_bound(128) + Fraction(20, 1 << 192) + joint_root_bound(envelope_numerator=3 * (2 * 22 + 12))
    total += sum((dense_fixed_error(bits) for bits in (176, 48, 240)), Fraction()) + adapter_error()
    assert total < Fraction(1, 1 << 151)
    print("The relocated restricted joint interface, including its adapter child and modified memory envelope, remains below 2^-151.", flush=True)


def larger_code_geometry(verifier):
    heights, lane = (19, 19, 19, 19, 20, 18), 1 << 22
    base = verifier.GLOBAL_COLUMN_BASES[verifier.OP_BLAKE2S]
    for code_log, first, second in ((11, "cnt_cv1", "cnt_out0"), (19, "cnt_m3", "cnt_cv0")):
        layout = verifier.build_layout(range(16 << code_log), 25, heights)
        assert layout.stack_log == 28
        for offset, column in enumerate((first, second)):
            assert layout.placements[base + verifier.BLAKE2S_COLUMNS.index(column)].index == 59 * lane + offset * (1 << 18)
        depths = [
            verifier.bus_layout(() if side == "count" else (0, 25, code_log), getattr(layout, side)).depth for side in ("push", "pull", "count")
        ]
        assert depths == [26, 26, 24]
        print(f"Bytecode log {code_log}: stack log 28 and bus depths {depths}, but lane 59 starts with {first}, {second}.", flush=True)
    assert layout.placements[verifier.BYTECODE_FINAL_COUNTERS].index == 51 * lane + (1 << 21)
    print("The larger code image fits in size; zk_large_code_audit.py checks its changed lane/prefix masks separately.", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--relocated-library", action="store_true", help="check every relocated metadata cycle, raw direction and joint boundary rank"
    )
    arguments = parser.parse_args()
    reference = verifier_module()
    tower = Tower(64, reference)
    basis_and_allocation(tower)
    larger_code_geometry(reference)
    shifted_wire(tower)
    actual_lane_schedule_certificate(tower, 32)
    joint_root_bound(envelope_numerator=3 * (2 * 22 + 12))
    if arguments.relocated_library:
        relocated_library(reference, tower)
