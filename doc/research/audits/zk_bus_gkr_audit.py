"""Actual batched-GKR disclosure boundaries and joint unused-memory node mixing."""

from fractions import Fraction
from functools import reduce
from operator import mul
from random import Random

from zk_count_children_audit import gkr_replay
from zk_pcs_audit import verifier_module


def nonzero_terms(form):
    return {monomial: coefficient for monomial, coefficient in form.terms.items() if int(coefficient)}


def paired_forms(verifier):
    count_reads = 0
    for table in verifier.TABLES:
        assert len(table.flushes.push) == len(table.flushes.pull)
        covered_counts = set()
        for push, pull in zip(table.flushes.push, table.flushes.pull, strict=True):
            assert len(push) == len(pull)
            difference = [nonzero_terms(left + right) for left, right in zip(push, pull, strict=True)]
            tag = pull[0].terms[()]
            expected = [{} for _ in pull]
            if tag == verifier.SEP_STATE:
                pc, fp = (table.columns.index(name) for name in ("pc", "fp"))
                expected[1] = {(pc,): verifier.ONE + verifier.GEN}
                if table.opcode == verifier.OP_JUMP:
                    b, dest, frame = (table.columns.index(name) for name in ("b", "v_pc", "v_fp"))
                    expected[1].update({tuple(sorted((b, dest))): verifier.ONE, tuple(sorted((b, pc))): verifier.GEN})
                    expected[2] = {tuple(sorted((b, frame))): verifier.ONE, tuple(sorted((b, fp))): verifier.ONE}
            else:
                assert tag in (verifier.SEP_MEM, verifier.SEP_BYTECODE)
                ((column,),) = pull[2].terms
                assert pull[2].terms[(column,)] == verifier.ONE
                assert column in table.count_columns and column not in covered_counts
                covered_counts.add(column)
                expected[2] = {(column,): verifier.ONE + verifier.GEN}
                count_reads += 1
            assert difference == expected, table.name
        assert covered_counts == set(table.count_columns)
    assert count_reads == 28
    print("All six opcode schemas: paired payload and address forms cancel exactly; 28 read-count forms and the state transitions remain", flush=True)


def paired_layouts(verifier):
    rng = Random(155)
    heights = [[0, 0, 0, 0, 0, 3], [32] * 6]
    heights.extend([rng.randrange(33) for _ in range(5)] + [rng.randrange(3, 33)] for _ in range(32))
    for index, shape in enumerate(heights):
        log_memory = 16 + index % 17
        layout = verifier.build_layout([0] * (16 << (index % 6)), log_memory, shape)
        framework = (0, layout.log_memory, layout.log_bytecode)
        push = verifier.bus_layout(framework, layout.push)
        pull = verifier.bus_layout(framework, layout.pull)
        assert push == pull
        assert push.framework[1].index % (1 << log_memory) == 0
        assert all(a.owner == b.owner and a.log_rows == b.log_rows for a, b in zip(layout.push, layout.pull, strict=True))
    print("Matched actual stack placements, including unequal heights and extrema; memory blocks align to sixteen-leaf product nodes", flush=True)


def bundle_bound():
    base, size, bundles = 1 << 64, 1 << 192, 1 << 24
    mixing = Fraction(1 << 95) * Fraction(1 << 96, base**2 - 1) ** 16
    bound = Fraction(8 + 16 * bundles, size) + Fraction(base**2, (size - 2) ** 2) + bundles * mixing
    assert mixing < Fraction(1, 1 << 416)
    assert bound < Fraction(1, 1 << 163)
    print("Joint sixteen-cell node theorem: exact rational upper bound below 2^-163 for at most 2^24 bundles", flush=True)


def replay_payload_cancellation(verifier):
    rng = Random(156)
    sample = lambda: verifier.E(*(rng.getrandbits(64) for _ in range(3)))
    weights, beta = verifier.eq_kernel([sample() for _ in range(verifier.BUS_BITS)]), sample()
    prefix = [sample() for _ in range(32)]
    other_prefix = prefix[:]
    rng.shuffle(other_prefix)
    count = [verifier.GEN ** rng.randrange(16) for _ in range(64)]
    views, differences = [], []
    for _ in range(2):
        unused = []
        for address in range(32, 64):
            word = [verifier.E(rng.getrandbits(64)) for _ in range(3)]
            unused.append(beta + verifier.dot(weights[:6], (verifier.SEP_MEM, verifier.GEN**address, verifier.ONE, *word)))
        push, pull = prefix + unused, other_prefix + unused
        view = gkr_replay(verifier, count, seed=157, details=True, bus_leaves=(push, pull))
        delta = [a + b for a, b in zip(push, pull, strict=True)]
        disclosed = tuple(a + b for a, b in zip(view["children"][0], view["children"][1], strict=True))
        assert disclosed == tuple(verifier.multilinear_eval(delta[child::4], view["challenge"]) for child in range(4))
        quartets = [reduce(mul, push[start : start + 4]) for start in range(0, 64, 4)]
        nodes = [reduce(mul, quartets[start : start + 4]) for start in range(0, 16, 4)]
        assert nodes[2:] == [reduce(mul, unused[start : start + 16]) for start in (0, 16)]
        views.append(view)
        differences.append(disclosed)
    assert differences[0] == differences[1] and any(int(value) for value in differences[0])
    assert views[0]["children"][0] != views[1]["children"][0]
    assert views[0]["children"][2] == views[1]["children"][2]
    assert views[0]["view"][3][:-12] != views[1]["view"][3][:-12]
    print(
        "Accepted three-channel GKR replays: unused payloads change mixed messages and individual bus children, but not their exposed difference or count packet",
        flush=True,
    )
    print("The replay uses actual unused-memory fingerprints and abstract balanced complementary leaves, not a complete VM trace", flush=True)


if __name__ == "__main__":
    module = verifier_module()
    paired_forms(module)
    paired_layouts(module)
    bundle_bound()
    replay_payload_cancellation(module)
