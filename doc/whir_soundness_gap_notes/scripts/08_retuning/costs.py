"""Cost model of one WHIR opening (researcher 08): proof bytes, verifier Keccak, prover grinding and encoding.

What is sent and hashed follows crates/verifier/src/{whir,transcript,wire,merkle,hash}.rs; the recursive verifier's
Merkle cap follows crates/aggregation/src/child.rs (`merkle_cap_depth`) and guests/lean_ethereum.py (`walk_path`,
`verify_merkle_cap`). Query positions are i.i.d. uniform, so sibling and cap counts are exact expectations.
"""

from __future__ import annotations

import math
import os
import sys
from dataclasses import dataclass, field

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import whir_model as wm

SCALAR = 16  # bytes of an E element on the wire
DIGEST = 32
RATE_BYTES = 136  # Keccak-256 rate
QUERY_WINDOW_BITS = 6  # the guest's QW


def leaf_words(level, k):
    """K words per leaf: level 0 commits K (one word a lane), later levels E (two words a lane)."""
    return (1 << k) if level == 0 else 2 << k


def leaf_perms(words):
    """Keccak-f permutations of one leaf hash (136-byte blocks, padding in the last)."""
    return (8 * words) // RATE_BYTES + 1


def expected_distinct(n, t):
    return n * -math.expm1(t * math.log1p(-1.0 / n))


def expected_siblings(height, t):
    """Expected digests in the pruned opening (`wire::write_phase`) of t i.i.d. uniform leaves of a 2^height tree.

    At a tree level of N nodes, a sibling is sent for each node that is on some path while its sibling is on none:
    N [(1 - 1/N)^t - (1 - 2/N)^t]."""
    total = 0.0
    for lvl in range(height):
        nodes = 1 << (height - lvl)
        a = math.exp(t * math.log1p(-1.0 / nodes))
        b = math.exp(t * math.log1p(-2.0 / nodes)) if nodes > 2 else 0.0
        total += nodes * (a - b)
    return total


def merkle_cap_depth(queries, depth):
    """crates/aggregation/src/child.rs."""
    near = max((queries - 1).bit_length() - (QUERY_WINDOW_BITS - 1), 2)
    near = min(near, depth)
    return depth - (depth - near) // QUERY_WINDOW_BITS * QUERY_WINDOW_BITS


def expected_cap_hashes(cap_depth, t):
    """Internal cap nodes the guest hashes: the root always, a deeper node when a query reaches its subtree."""
    if cap_depth == 0:
        return 0.0
    total = 1.0
    for j in range(1, cap_depth):
        nodes = 1 << j
        total += nodes * -math.expm1(t * math.log1p(-1.0 / nodes))
    return total


class SpongeCount:
    """The permutation count of crates/verifier/src/transcript.rs's duplex sponge."""

    def __init__(self):
        self.pending, self.ground, self.perms = 0, False, 0

    def _duplex(self):
        self.perms += 1
        self.pending = 0

    def absorb(self, count=1):
        for _ in range(count):
            assert not self.ground
            if self.pending == 4:
                self._duplex()
            self.pending += 1

    def sample(self, count=1):
        for _ in range(count):
            if self.ground:
                self.ground = False
            else:
                self._duplex()

    def grind(self, bits):
        if bits:
            self.absorb()
            self._duplex()
            self.ground = True


@dataclass
class LevelCost:
    queries: int
    depth: int
    leaf_bytes: int
    leaf_perms: int
    proof_bytes: float
    sibling_digests: float
    native_merkle_perms: int
    cap_depth: int
    guest_merkle_perms: float
    guest_merkle_perms_cap8: float
    fold_mults: int
    guest_cycles: float


@dataclass
class Cost:
    levels: list = field(default_factory=list)
    stream_scalars: int = 0
    fs_perms: int = 0
    grind_perms: int = 0  # expected Keccak-f evaluations of all the opening's grinds
    grind_max_bits: int = 0
    encode_words: int = 0  # K words of all committed codewords
    encode_ntt: int = 0  # sum of words * log2(block length): butterfly count up to a constant
    commit_perms: int = 0  # Keccak-f permutations of all Merkle trees
    final_scalars: int = 0

    @property
    def merkle_bytes(self):
        return sum(lv.proof_bytes for lv in self.levels)

    @property
    def proof_bytes(self):
        return self.merkle_bytes + SCALAR * self.stream_scalars

    @property
    def guest_keccak(self):
        return sum(lv.guest_merkle_perms for lv in self.levels) + self.fs_perms

    @property
    def guest_keccak_cap8(self):
        """As guest_keccak with every level's cap eight levels deep, which removes the cap rule's dependence on the
        tree depth modulo the path window."""
        return sum(lv.guest_merkle_perms_cap8 for lv in self.levels) + self.fs_perms

    @property
    def native_keccak(self):
        return sum(lv.native_merkle_perms for lv in self.levels) + self.fs_perms

    @property
    def guest_cycles(self):
        return sum(lv.guest_cycles for lv in self.levels)

    @property
    def queries(self):
        return [lv.queries for lv in self.levels]


# Guest cycles per query: coefficients fitted to one DBG_PROF profile of the recursion guest (the note says which, and
# what it measured). An estimate, not an exact count; every other number of this module is exact.
def guest_query_cycles(level, k, path_levels, cols, final):
    fold = (4.5 * (1 << k) + 13) if level == 0 else (5.0 * (1 << k) + 12)
    walk = 3.85 * path_levels
    decode = 38.0
    residual = 0.0 if final else 7.6 * cols - 37
    final_eval = (2.2 * ((1 << cols) + k) + 60) if final else 0.0
    return fold + walk + decode + max(residual, 0.0) + final_eval


def cost(cfg: wm.Config, fill: float = 1.0) -> Cost:
    """The opening's costs. `fill` is the stack's share of 2^mu holding data: level 0 leaves carry only data rows."""
    kn = cfg.knobs
    out = Cost()
    sponge = SpongeCount()
    n_levels = len(cfg.levels)
    # The commitment: its root, then the OOD sample (outside verify_whir, part of the PCS).
    scalars = 2 + (1 if kn.g_ood else 0) + 1
    sponge.absorb(2)
    sponge.grind(kn.g_ood)
    sponge.sample(cfg.log_n)
    sponge.absorb()
    # Level 0's batching grind (ring_switch.rs), then lambda_0. The ring switch's own challenges are not counted.
    scalars += 1 if kn.g_batch else 0
    sponge.grind(kn.g_batch)
    sponge.sample()
    grind = n_levels * (1 << kn.g_ood if kn.g_ood else 0) + (1 << kn.g_batch if kn.g_batch else 0)
    max_bits = max(kn.g_ood, kn.g_batch, kn.g_fold)
    for i, lv in enumerate(cfg.levels):
        final = i == n_levels - 1
        depth = lv.log_block
        t = lv.queries
        g_query = kn.query_grind(i)
        for _ in range(lv.k):
            scalars += 4 + (1 if kn.g_fold else 0)
            sponge.absorb(4)
            sponge.grind(kn.g_fold)
            sponge.sample(2)
        grind += lv.k * (1 << kn.g_fold if kn.g_fold else 0) + (1 << g_query if g_query else 0)
        max_bits = max(max_bits, g_query)
        per_word = 128 // depth
        if final:
            n_final = (1 << lv.cols) + lv.k
            out.final_scalars = n_final
            scalars += n_final + (1 if g_query else 0) + 2 * lv.cols
            sponge.absorb(n_final)
            sponge.grind(g_query)
            sponge.sample(-(-t // per_word))
            for _ in range(lv.cols):
                sponge.absorb(2)
                sponge.sample()
        else:
            scalars += 2 + lv.k + (1 if kn.g_ood else 0) + 1 + (1 if g_query else 0)
            sponge.absorb(2 + lv.k)
            sponge.grind(kn.g_ood)
            sponge.sample(lv.cols)
            sponge.absorb()
            sponge.grind(g_query)
            sponge.sample(-(-t // per_word))
            sponge.sample()
        words = leaf_words(i, lv.k)
        perms = leaf_perms(words)
        sent_words = words
        if i == 0 and fill < 1.0:
            sent_words = min(words, math.ceil(fill * words - 1e-9))
        distinct = expected_distinct(1 << depth, t)
        siblings = expected_siblings(depth, t)
        phase = 4 + 4 * t + 12 + distinct * 8 * sent_words + DIGEST * siblings
        cap = merkle_cap_depth(t, depth)
        guest = t * (perms + depth - cap) + expected_cap_hashes(cap, t)
        out.levels.append(
            LevelCost(
                queries=t,
                depth=depth,
                leaf_bytes=8 * sent_words,
                leaf_perms=perms,
                proof_bytes=phase,
                sibling_digests=siblings,
                native_merkle_perms=t * (perms + depth),
                cap_depth=cap,
                guest_merkle_perms=guest,
                guest_merkle_perms_cap8=t * (perms + depth - min(8, depth)) + expected_cap_hashes(min(8, depth), t),
                fold_mults=t * ((1 << lv.k) - 1),
                guest_cycles=t * guest_query_cycles(i, lv.k, depth - cap, lv.cols, final),
            )
        )
        block_words = words << depth
        if i == 0:
            block_words = math.ceil(block_words * fill)
        out.encode_words += block_words
        out.encode_ntt += block_words * depth
        out.commit_perms += (perms + 1) << depth
    out.stream_scalars = scalars
    out.fs_perms = sponge.perms
    out.grind_perms = grind
    out.grind_max_bits = max_bits
    return out


def describe(cfg, fill=1.0):
    c = cost(cfg, fill)
    lines = []
    for i, (lv, lc) in enumerate(zip(cfg.levels, c.levels)):
        lines.append(
            f"  L{i}: rate 2^-{lv.log_inv_rate} kappa {lv.cols} k {lv.k} n 2^{lc.depth} list {lv.list_bound} queries {lv.queries}"
            f" | leaf {lc.leaf_bytes} B ({lc.leaf_perms} perms) siblings/query {lc.sibling_digests / lv.queries:.2f}"
            f" phase {lc.proof_bytes / 1024:.1f} KiB | guest: cap {lc.cap_depth}, {lc.guest_merkle_perms:.0f} Keccak, ~{lc.guest_cycles:.0f} cycles"
        )
    lines.append(
        f"  total: {c.proof_bytes / 1024:.1f} KiB (Merkle {c.merkle_bytes / 1024:.1f}, stream {c.stream_scalars} scalars)"
        f" | guest Keccak {c.guest_keccak:.0f} (FS {c.fs_perms}) native Keccak {c.native_keccak} | ~{c.guest_cycles:.0f} query cycles"
        f" | grind 2^{math.log2(c.grind_perms):.2f} perms | encode {c.encode_words / 2**cfg.log_n:.3f} x 2^mu words"
    )
    return "\n".join(lines)


if __name__ == "__main__":
    for mu, rate, fill in [(23, 1, 0.685), (23, 2, 0.685), (23, 3, 0.685), (23, 4, 0.685), (26, 1, 0.617), (26, 2, 0.617), (30, 1, 1.0)]:
        cfg = wm.derive(mu, rate)
        print(f"mu={mu} rate=2^-{rate} fill={fill} queries={cfg.queries}")
        print(describe(cfg, fill))
