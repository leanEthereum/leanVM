"""What the differential drivers (fuzz-verifier.py, wire-diff.py, prover-diff.py) share: the proof's
file formats, read without hashing, and the running of their child processes.

  * `merkle_phases.bin`, the structured openings (the `verifier` crate's `Vec<Vec<MerklePath>>`),
    every number little-endian: the `u32` phase count; per phase its `u32` path count; per path its
    `u64` position, its `u32` leaf length and that many `u64` words, its `u32` sibling count and
    that many 32-byte digests (`parse_phases`);
  * `proof.wire`, the one wire encoding (`Proof::to_bytes`, `crates/fiat_shamir/src/wire.rs`): the
    `u32` stream length and the stream, 16 bytes a scalar; the `u32` phase count; per phase its
    `u32` query count and positions, its `u32` height, leaf width and row width, the row of every
    distinct position, ascending, and the carried siblings (`parse_wire`, `Wire`, `Phase`).

The scripts run under `python3 -I`, so they load this module by its path.
"""

import resource
import struct
import subprocess
from pathlib import Path


def u32(value: int) -> bytes:
    return struct.pack("<I", value % 2**32)


def u64(value: int) -> bytes:
    return struct.pack("<Q", value)


# The structured openings ----------------------------------------------------------------------


def parse_phases(data: bytes) -> list:
    """The phases file's layout: per phase its count's offset and per path the offsets of its
    position, leaf length, leaf, sibling count and siblings, with the lengths."""
    at = 4
    phases = []
    for _ in range(int.from_bytes(data[:4], "little")):
        count_at = at
        count = int.from_bytes(data[at:at + 4], "little")
        at += 4
        paths = []
        for _ in range(count):
            path = {"index": at, "position": int.from_bytes(data[at:at + 8], "little")}
            at += 8
            path["leaf_length"] = at
            path["words"] = int.from_bytes(data[at:at + 4], "little")
            at += 4
            path["leaf"] = at
            at += 8 * path["words"]
            path["sibling_count"] = at
            path["height"] = int.from_bytes(data[at:at + 4], "little")
            at += 4
            path["siblings"] = at
            at += 32 * path["height"]
            path["end"] = at
            paths.append(path)
        phases.append({"count": count_at, "paths": paths, "start": count_at, "end": at})
    if at != len(data):
        raise ValueError("the phases file is not read whole")
    return phases


# The wire encoding, pruned (no hashing) ---------------------------------------------------------


def carried_nodes(positions: list, level: int) -> list:
    """The nodes of a level whose sibling a phase carries, ascending (`carriedSiblings`)."""
    nodes = sorted({p >> level for p in positions})
    present = set(nodes)
    return [n for n in nodes if n ^ 1 not in present]


class Phase:
    """A phase as its encoding gives it: queries, sizes, rows at the distinct positions, and the
    carried digests keyed by (level, node)."""

    def __init__(self, queries, height, leaf_words, row_words, rows, carried):
        self.queries, self.height, self.leaf_words, self.row_words = queries, height, leaf_words, row_words
        self.rows = rows  # position -> list of row words
        self.carried = carried  # (level, node) -> 32 bytes

    def copy(self):
        return Phase(list(self.queries), self.height, self.leaf_words, self.row_words,
                     {p: list(r) for p, r in self.rows.items()}, dict(self.carried))

    def positions(self) -> list:
        return sorted(set(self.queries))

    def encode(self, count=None, extra_digests=None, drop_digests=None) -> bytes:
        """The phase's bytes; `count` overrides the query count written, `extra_digests` adds
        digests at a (level, index) of the sibling section, `drop_digests` removes some."""
        out = bytearray(u32(len(self.queries) if count is None else count))
        for q in self.queries:
            out += u32(q)
        out += u32(self.height) + u32(self.leaf_words) + u32(self.row_words)
        for p in self.positions():
            for word in self.rows[p]:
                out += u64(word)
        digests = []
        for level in range(self.height):
            for node in carried_nodes(self.positions(), level):
                digests.append(self.carried.get((level, node), bytes(32)))
        for index in sorted(drop_digests or [], reverse=True):
            del digests[index]
        for index, digest in sorted(extra_digests or [], reverse=True):
            digests.insert(index, digest)
        for digest in digests:
            out += digest
        return bytes(out)

    def digest_count(self) -> int:
        return sum(len(carried_nodes(self.positions(), level)) for level in range(self.height))


class Wire:
    """A proof as its encoding gives it."""

    def __init__(self, stream: bytes, phases: list):
        self.stream, self.phases = stream, phases

    def encode(self, stream_count=None, phase_count=None) -> bytes:
        out = bytearray(u32(len(self.stream) // 16 if stream_count is None else stream_count))
        out += self.stream
        out += u32(len(self.phases) if phase_count is None else phase_count)
        for phase in self.phases:
            out += phase.encode()
        return bytes(out)


def parse_wire(data: bytes) -> tuple:
    """The honest bytes as a `Wire`, with, per phase, the offsets of its start (its query count),
    its rows (after the three sizes), its carried siblings and its end."""
    offset = 0

    def take(n):
        nonlocal offset
        if offset + n > len(data):
            raise ValueError("truncated")
        piece = data[offset:offset + n]
        offset += n
        return piece

    def read_u32():
        return struct.unpack("<I", take(4))[0]

    stream = take(16 * read_u32())
    phases, offsets = [], []
    for _ in range(read_u32()):
        start = offset
        queries = [read_u32() for _ in range(read_u32())]
        height, leaf_words, row_words = read_u32(), read_u32(), read_u32()
        positions = sorted(set(queries))
        rows_at = offset
        rows = {p: list(struct.unpack(f"<{row_words}Q", take(8 * row_words))) for p in positions}
        siblings_at = offset
        carried = {}
        for level in range(height):
            for node in carried_nodes(positions, level):
                carried[(level, node)] = take(32)
        phases.append(Phase(queries, height, leaf_words, row_words, rows, carried))
        offsets.append((start, rows_at, siblings_at, offset))
    if offset != len(data):
        raise ValueError("trailing bytes")
    return Wire(stream, phases), offsets


# Child processes --------------------------------------------------------------------------------


def limit(gigabytes: int, unlimited_stack: bool = False):
    """A `preexec_fn`: the address space capped at `gigabytes`, the stack unlimited if asked."""
    def apply():
        cap = gigabytes << 30
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))
        if unlimited_stack:
            resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, resource.RLIM_INFINITY))
    return apply


def batch(exe: Path, commands: list, memory_gb: int, strict: bool = False) -> list:
    """Run `exe --batch` on the commands, each a line of tab-separated words: one result line each.
    Lines a crash leaves out are `crash (exit <code>) <stderr>`; with `strict` a crash raises."""
    text = "".join("\t".join(map(str, c)) + "\n" for c in commands)
    done = subprocess.run([str(exe), "--batch"], input=text, capture_output=True, text=True,
                          preexec_fn=limit(memory_gb), check=strict)
    lines = done.stdout.splitlines()
    if strict:
        assert len(lines) == len(commands), done.stderr
    elif done.returncode != 0 or len(lines) != len(commands):
        lines += [f"crash (exit {done.returncode}) {done.stderr.strip()[:200]}"] * (len(commands) - len(lines))
    return lines
