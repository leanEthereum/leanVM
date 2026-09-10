"""Public range-probe prefix, shifted unused masks and unchanged memory envelopes."""

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


if __name__ == "__main__":
    reference = verifier_module()
    tower = Tower(64, reference)
    basis_and_allocation(tower)
    shifted_wire(tower)
    actual_lane_schedule_certificate(tower, 32)
    joint_root_bound(envelope_numerator=3 * (2 * 22 + 12))
