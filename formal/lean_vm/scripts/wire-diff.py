"""Differential test of the Lean proof wire encoding against leanVM's Rust one.

leanVM's proof travels as one byte string, `Proof::to_bytes` (`crates/fiat_shamir/src/wire.rs`), which
prunes every Merkle phase, and is decoded by `Proof::from_bytes`, which unprunes it, hashing the
nodes the paths share, and refuses anything but the one encoding of a proof within its bounds (the
pruning is scaraven's idea, https://github.com/scaraven). lean_vm transcribes both (`Proof.fromBytes`, `Proof.toBytes`,
lean_vm/LeanVM/Wire/Encoding.lean). This driver runs, on the same bytes,

  * the Lean transcription, `lake exe wire-diff` (cli/WireDiff.lean), compiled, Keccak-f[1600] in
    `Id` for the permutation;
  * the Rust, scripts/wire-diff (`leanvm-rust-wire`, leanVM's `fiat_shamir` crate), in one
    `--batch` process;

and requires, on every case, the same verdict (`none`, or `some` and the proof decoded, compared as
its plain rendering, which prunes and hashes nothing), and, when decoding succeeds, that each
side's encoding of the decoded proof gives back the input bytes (the one encoding).

The cases, per honest wire proof:

  honest      the proof itself, and with one zero byte more (the Rust test's refusal);
  truncate    the bytes cut at the ends, inside the stream, and before and inside every phase;
  append      one zero byte, one 0xff byte, four bytes, a digest's 32 bytes, a copy of the first
              phase;
  stream      the stream's length one more, one fewer, zero (with and without the elements),
              2^32 - 1;
  phases      the phase count one more, one fewer, zero, 9 and 2^32 - 1 (bytes unchanged);
              no phase; the phases repeated up to `MAX_PHASES` (8, decodes) and one past it (9);
  count       a phase's query count one more, one fewer, zero, 257 and 2^32 - 1 (bytes unchanged);
              re-encoded with one query and with `MAX_QUERIES` (256) queries (decode) and 257;
  duplicate   a phase's first query repeated at the end, every query one position, the queries
              reversed: re-encoded, the rows and carried siblings for the new positions;
  position    a query moved to `2^height`, `2^height + 1`, `2^32 - 1` (out of range), and to an
              unopened position in range, and to `2^32 - 1` at height 32 (re-encoded with its row
              and siblings: decode);
  rowwidth    a non-minimal row width (one zero word more on every row, and the whole leaf), a row
              width past the leaf width, zero, one less (dropping a nonzero word), every row's first
              word made zero;
  leafwidth   the leaf width one more (one zero word more of padding), `MAX_LEAF_WORDS` (64), one
              past it (65);
  height      the height one more and `MAX_HEIGHT` (32) with the carried siblings it then needs
              (decode), one past it (33), one less;
  sibling     a surplus digest at the bottom and at the top level, a missing first and last digest,
              a phase's carried siblings all dropped;
  flip        one bit of a stream word, a query, the height, a row word, a carried digest, the last
              byte;
  random      random single-bit flips and random truncations, from `--seed`.

The phase mutations are made on the first and the last phase of a fixture's proof (every phase
with `--all-phases`), and on every phase of the vector.

The round trip, on every fixture: its proof as the Rust prover made it, unpruned (`stream.bin` and
`merkle_phases.bin`, the paths of every phase in the plain rendering below), encoded by the Lean
(`Proof.toBytes`), is the Rust's wire proof byte for byte, and decodes (`Proof.fromBytes`) back to
that proof; and the Rust's decoding of the wire proof is that proof. On the vector the proof is
the Rust's decoding of it.

The Rust test's vector (wire.rs, `proof_round_trips_through_its_one_encoding`) is a fixed case:
both sides build it (`vector`), and their bytes must equal tests/fixtures/wire/round-trip-vector.bin;
it then gets every mutation above, with the honest proofs.

The honest wire proofs are the files `proof.wire` in the fixture directories given, the Rust
prover's proofs as `Proof::to_bytes` writes them (scripts/export-verifier-fixtures-rust.sh). The
plain rendering of a proof prunes and hashes nothing: every count a little-endian u32, every word
and position a little-endian u64; the stream's length and its elements, each three words; the
number of phases, and for each its number of paths, and for each path its position, its leaf's
length and words, its siblings' count and their 32 bytes each (the length of `stream.bin` over 24,
`stream.bin`, then `merkle_phases.bin`).

Usage (from lean_vm; the two sides built first):
  ( ulimit -v 40000000; lake build wire-diff )
  cargo build --release --manifest-path scripts/wire-diff/Cargo.toml
  python3 -I scripts/wire-diff.py tests/fixtures/verifier [--jobs 4] [--random 10] [--seed 1] [--all-phases]
      [--keep <dir>] [--log <file>] [fixture ...]

It fails if any case differs, and prints the cases by kind: their number, how many decoded, and how
many differed. The bytes of every differing case are kept under `--keep` (default: a new directory
under the system temporary directory), with a `case.txt` saying what was changed.
"""

import argparse
import random
import shutil
import sys
import tempfile
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proofio import Phase, Wire, batch, carried_nodes, parse_wire, u32

ROOT = Path(__file__).resolve().parent.parent
LEAN_EXE = ROOT / ".lake" / "build" / "bin" / "wire-diff"
RUST_EXE = ROOT / "scripts" / "wire-diff" / "target" / "release" / "leanvm-rust-wire"
VECTOR = ROOT / "tests" / "fixtures" / "wire" / "round-trip-vector.bin"
VECTOR_LENGTH = (4 + 24) + 4 + (4 + 3 * 4) + 3 * 4 + 2 * 2 * 8 + 2 * 32

MAX_PHASES, MAX_QUERIES, MAX_LEAF_WORDS, MAX_HEIGHT = 8, 256, 64, 32


# The mutations -----------------------------------------------------------------------------


def reposition(phase: Phase, queries: list, rng: random.Random) -> Phase:
    """`phase` with these queries: the rows of the positions it had kept, a random row (its first
    word nonzero) at a new one, the carried digests it had kept, random ones for new nodes."""
    new = phase.copy()
    new.queries = list(queries)
    for p in new.positions():
        if p not in new.rows:
            new.rows[p] = [rng.getrandbits(64) | 1 for _ in range(new.row_words)]
    for level in range(new.height):
        for node in carried_nodes(new.positions(), level):
            new.carried.setdefault((level, node), rng.randbytes(32))
    return new


def flip(data: bytes, offset: int, bit: int = 0) -> bytes:
    out = bytearray(data)
    out[offset] ^= 1 << bit
    return bytes(out)


def put(data: bytes, offset: int, value: bytes) -> bytes:
    return data[:offset] + value + data[offset + len(value):]


def mutations(data: bytes, rng: random.Random, random_cases: int, all_phases: bool) -> list:
    """Every case of the honest bytes `data`: (kind, label, bytes); the phase mutations on every
    phase, or with `all_phases` false on the first and the last only."""
    wire, offsets = parse_wire(data)
    stream_count = len(wire.stream) // 24
    phase_count_at = 4 + len(wire.stream)
    cases = []

    def add(kind, label, value):
        cases.append((kind, label, value))

    def with_phase(i, phase):
        phases = list(wire.phases)
        phases[i] = phase
        return Wire(wire.stream, phases).encode()

    # truncate
    cuts = {0, 1, 3, 4, len(data) - 1, len(data) - 33, 4 + len(wire.stream) // 2, phase_count_at,
            phase_count_at + 2}
    for start, rows_at, siblings_at, end in offsets:
        cuts |= {start, start + 2, rows_at - 1, rows_at + 4, siblings_at + 16, end - 1}
    for cut in sorted(c for c in cuts if 0 <= c < len(data)):
        add("truncate", f"to {cut} bytes", data[:cut])

    # append
    first = wire.phases[0].encode() if wire.phases else b""
    for label, extra in [("a zero byte", b"\0"), ("a 0xff byte", b"\xff"), ("four bytes", b"\1\0\0\0"),
                         ("a digest", rng.randbytes(32)), ("a copy of the first phase", first)]:
        add("append", label, data + extra)

    # stream
    for label, count in [("+1", stream_count + 1), ("-1", stream_count - 1), ("0", 0),
                         ("2^32 - 1", 2**32 - 1)]:
        if count >= 0:
            add("stream", f"length {label}", put(data, 0, u32(count)))
    add("stream", "empty", Wire(b"", wire.phases).encode())

    # phases
    n = len(wire.phases)
    for label, count in [("+1", n + 1), ("-1", n - 1), ("0", 0), ("9", 9), ("2^32 - 1", 2**32 - 1)]:
        if count >= 0:
            add("phases", f"count {label}", put(data, phase_count_at, u32(count)))
    add("phases", "none", Wire(wire.stream, []).encode())
    if wire.phases:
        add("phases", "8 (MAX_PHASES)", Wire(wire.stream, (wire.phases * 8)[:8]).encode())
        add("phases", "9", Wire(wire.stream, (wire.phases * 9)[:9]).encode())

    for i, phase in enumerate(wire.phases):
        if not all_phases and 0 < i < len(wire.phases) - 1:
            continue
        start, rows_at, siblings_at, end = offsets[i]
        tag = f"phase {i}"
        k = len(phase.queries)
        positions = phase.positions()

        # count
        for label, count in [("+1", k + 1), ("-1", k - 1), ("0", 0), ("257", 257), ("2^32 - 1", 2**32 - 1)]:
            if count >= 0:
                add("count", f"{tag} count {label}", put(data, start, u32(count)))
        add("count", f"{tag} one query", with_phase(i, reposition(phase, phase.queries[:1], rng)))
        padded = (phase.queries * (MAX_QUERIES // k + 1))
        add("count", f"{tag} 256 queries", with_phase(i, reposition(phase, padded[:256], rng)))
        add("count", f"{tag} 257 queries", with_phase(i, reposition(phase, padded[:257], rng)))

        # duplicate
        add("duplicate", f"{tag} first query again", with_phase(i, reposition(phase, phase.queries + phase.queries[:1], rng)))
        add("duplicate", f"{tag} every query one position", with_phase(i, reposition(phase, [phase.queries[0]] * k, rng)))
        add("duplicate", f"{tag} reversed", with_phase(i, reposition(phase, phase.queries[::-1], rng)))

        # position
        for label, value in [("2^height", 2**phase.height), ("2^height + 1", 2**phase.height + 1),
                             ("2^32 - 1", 2**32 - 1)]:
            add("position", f"{tag} a query at {label}", with_phase(i, reposition(phase, [value] + phase.queries[1:], rng)))
            add("position", f"{tag} a query's bytes at {label}", put(data, start + 4, u32(value)))
        top = phase.copy()
        top.height = MAX_HEIGHT
        add("position", f"{tag} a query at 2^32 - 1, height 32", with_phase(i, reposition(top, [2**32 - 1] + phase.queries[1:], rng)))
        unopened = next((p for p in range(2**phase.height) if p not in set(positions)), None)
        if unopened is not None:
            add("position", f"{tag} a query at unopened {unopened}", with_phase(i, reposition(phase, [unopened] + phase.queries[1:], rng)))

        # rowwidth
        if phase.row_words < phase.leaf_words:
            wider = phase.copy()
            wider.row_words += 1
            wider.rows = {p: [0] + r for p, r in wider.rows.items()}
            add("rowwidth", f"{tag} one zero word more", with_phase(i, wider))
            whole = phase.copy()
            whole.row_words = phase.leaf_words
            whole.rows = {p: [0] * (phase.leaf_words - phase.row_words) + r for p, r in whole.rows.items()}
            add("rowwidth", f"{tag} the whole leaf", with_phase(i, whole))
        past = phase.copy()
        past.row_words = phase.leaf_words + 1
        past.rows = {p: [0] * (past.row_words - phase.row_words) + r for p, r in past.rows.items()}
        add("rowwidth", f"{tag} past the leaf width", with_phase(i, past))
        add("rowwidth", f"{tag} width zero (bytes)", put(data, rows_at - 4, u32(0)))
        zero = phase.copy()
        zero.row_words, zero.rows = 0, {p: [] for p in positions}
        add("rowwidth", f"{tag} width zero", with_phase(i, zero))
        if phase.row_words > 0:
            narrower = phase.copy()
            narrower.row_words -= 1
            narrower.rows = {p: r[1:] for p, r in narrower.rows.items()}
            add("rowwidth", f"{tag} one word less", with_phase(i, narrower))
            leading = phase.copy()
            leading.rows = {p: [0] + r[1:] for p, r in leading.rows.items()}
            add("rowwidth", f"{tag} first words zero", with_phase(i, leading))

        # leafwidth
        for label, words in [("+1", phase.leaf_words + 1), ("64 (MAX_LEAF_WORDS)", MAX_LEAF_WORDS),
                             ("65", MAX_LEAF_WORDS + 1)]:
            if words >= phase.row_words:
                wide = phase.copy()
                wide.leaf_words = words
                add("leafwidth", f"{tag} leaf width {label}", with_phase(i, wide))

        # height
        for label, height in [("+1", phase.height + 1), ("32 (MAX_HEIGHT)", MAX_HEIGHT), ("33", MAX_HEIGHT + 1),
                              ("-1", phase.height - 1)]:
            if height >= 0:
                tall = phase.copy()
                tall.height = height
                tall = reposition(tall, tall.queries, rng)
                add("height", f"{tag} height {label}", with_phase(i, tall))
        add("height", f"{tag} height +1 (bytes)", put(data, rows_at - 12, u32(phase.height + 1)))

        # sibling
        d = phase.digest_count()
        if phase.height > 0:
            add("sibling", f"{tag} surplus at the bottom",
                data[:start] + phase.encode(extra_digests=[(0, rng.randbytes(32))]) + data[end:])
            add("sibling", f"{tag} surplus at the top",
                data[:start] + phase.encode(extra_digests=[(d, rng.randbytes(32))]) + data[end:])
        if d > 0:
            add("sibling", f"{tag} first missing", data[:start] + phase.encode(drop_digests=[0]) + data[end:])
            add("sibling", f"{tag} last missing", data[:start] + phase.encode(drop_digests=[d - 1]) + data[end:])
            add("sibling", f"{tag} all missing", data[:start] + phase.encode(drop_digests=list(range(d))) + data[end:])

        # flip
        add("flip", f"{tag} a query's low bit", flip(data, start + 4))
        add("flip", f"{tag} the height's low bit", flip(data, rows_at - 12))
        if siblings_at > rows_at:
            add("flip", f"{tag} a row word", flip(data, rows_at + rng.randrange(siblings_at - rows_at), rng.randrange(8)))
        if end > siblings_at:
            add("flip", f"{tag} a carried digest", flip(data, siblings_at + rng.randrange(end - siblings_at), rng.randrange(8)))

    if wire.stream:
        add("flip", "a stream word", flip(data, 4 + rng.randrange(len(wire.stream)), rng.randrange(8)))
    add("flip", "the last byte", flip(data, len(data) - 1, 7))

    # random
    for _ in range(random_cases):
        add("random", "bit flip", flip(data, rng.randrange(len(data)), rng.randrange(8)))
        add("random", "truncation", data[:rng.randrange(len(data))])
    return cases


# Running the two sides ---------------------------------------------------------------------


def batch_parallel(exe: Path, commands: list, jobs: int, memory_gb: int) -> list:
    chunks = [commands[k::jobs] for k in range(jobs)]
    with ThreadPoolExecutor(jobs) as pool:
        results = list(pool.map(lambda chunk: batch(exe, chunk, memory_gb), chunks))
    lines = [None] * len(commands)
    for k, chunk in enumerate(results):
        for j, line in enumerate(chunk):
            lines[k + j * jobs] = line
    return lines


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("fixtures", type=Path, help="the directory of fixture directories")
    parser.add_argument("names", nargs="*", help="only these fixtures")
    parser.add_argument("--jobs", type=int, default=4, help="Lean processes at once (default 4)")
    parser.add_argument("--random", type=int, default=10, help="random flips and truncations per proof (default 10)")
    parser.add_argument("--all-phases", action="store_true",
                        help="mutate every phase of a fixture's proof (default: its first and last; every phase of the vector)")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--memory-gb", type=int, default=40, help="address-space cap of each process (default 40)")
    parser.add_argument("--keep", type=Path, help="where to keep the differing cases")
    parser.add_argument("--log", type=Path, help="write one line per case: proof, kind, label, Rust, Lean")
    arguments = parser.parse_args()

    for exe, how in [(LEAN_EXE, "lake build wire-diff"),
                     (RUST_EXE, "cargo build --release --manifest-path scripts/wire-diff/Cargo.toml")]:
        if not exe.exists():
            sys.exit(f"{exe} is missing: {how}")

    work = Path(tempfile.mkdtemp(prefix="wire-diff-"))
    rng = random.Random(arguments.seed)
    failures = []

    # The Rust test's vector: both sides build it, and it is the committed one.
    rust_vector, lean_vector = work / "vector.rust.bin", work / "vector.lean.bin"
    rust_line = batch(RUST_EXE, [("vector", rust_vector)], arguments.memory_gb)[0]
    lean_line = batch(LEAN_EXE, [("vector", lean_vector)], arguments.memory_gb)[0]
    expected = f"vector {VECTOR_LENGTH}"
    if rust_line != expected or lean_line != expected:
        failures.append(f"vector: Rust `{rust_line}`, Lean `{lean_line}`, expected `{expected}`")
    elif rust_vector.read_bytes() != lean_vector.read_bytes() or rust_vector.read_bytes() != VECTOR.read_bytes():
        failures.append(f"vector: the Rust's, the Lean's and {VECTOR.name} differ")
    print(f"vector: Rust `{rust_line}`, Lean `{lean_line}`, equal to {VECTOR.relative_to(ROOT)}")

    proofs = [("vector", VECTOR.read_bytes(), None)]
    directories = sorted(d for d in arguments.fixtures.iterdir() if d.is_dir())
    if arguments.names:
        directories = [d for d in directories if d.name in arguments.names]
    for directory in directories:
        paths = [directory / name for name in ("proof.wire", "stream.bin", "merkle_phases.bin")]
        for path in paths:
            if not path.exists():
                sys.exit(f"{path} is missing: the fixtures' files (scripts/export-verifier-fixtures-rust.sh)")
        wire, stream, phases = (path.read_bytes() for path in paths)
        if len(stream) % 24:
            sys.exit(f"{paths[1]} is not a whole number of scalars")
        proofs.append((directory.name, wire, u32(len(stream) // 24) + stream + phases))

    # The cases: (proof, kind, label, bytes).
    cases = []
    for name, data, _ in proofs:
        cases.append((name, "honest", "the proof", data))
        cases.append((name, "honest", "one zero byte more (the test's refusal)", data + b"\0"))
        every = arguments.all_phases or name == "vector"
        cases += [(name, kind, label, value) for kind, label, value in mutations(data, rng, arguments.random, every)]
    for index, (_, _, _, value) in enumerate(cases):
        (work / f"{index}.bin").write_bytes(value)

    def commands(side):
        return [("decode", work / f"{i}.bin", work / f"{i}.{side}.plain") for i in range(len(cases))]

    rust_lines = batch(RUST_EXE, commands("rust"), arguments.memory_gb)
    lean_lines = batch_parallel(LEAN_EXE, commands("lean"), arguments.jobs, arguments.memory_gb)

    # The round trip on the honest proofs: the Lean encoding of the Rust prover's proof.
    honest = [i for i, case in enumerate(cases) if case[1] == "honest" and case[2] == "the proof"]
    for i, (_, _, plain) in zip(honest, proofs):
        rust_plain = work / f"{i}.rust.plain"
        if plain is None and rust_plain.exists():
            plain = rust_plain.read_bytes()
        (work / f"{i}.prover.plain").write_bytes(plain or b"")
    trips = batch_parallel(LEAN_EXE, [("encode", work / f"{i}.prover.plain", work / f"{i}.lean.wire") for i in honest],
                           arguments.jobs, arguments.memory_gb)

    if arguments.log:
        arguments.log.write_text("".join(f"{name}\t{kind}\t{label}\t{rust}\t{lean}\n" for (name, kind, label, _), rust, lean
                                         in zip(cases, rust_lines, lean_lines)))

    table = defaultdict(Counter)
    differing = []
    for index, ((name, kind, label, value), rust, lean) in enumerate(zip(cases, rust_lines, lean_lines)):
        table[kind]["cases"] += 1
        problem = None
        if rust != lean:
            problem = f"Rust `{rust}`, Lean `{lean}`"
        elif rust.startswith("some"):
            table[kind]["decoded"] += 1
            if (work / f"{index}.rust.plain").read_bytes() != (work / f"{index}.lean.plain").read_bytes():
                problem = "different proofs decoded"
            elif rust != "some reencode-ok":
                problem = f"the encoding of the decoded proof is not the input: `{rust}`"
        elif rust != "none":
            problem = f"Rust `{rust}`"
        if kind == "honest" and label == "the proof" and rust != "some reencode-ok":
            problem = problem or f"the honest proof does not decode: `{rust}`"
        if problem:
            table[kind]["differ"] += 1
            differing.append((index, name, kind, label, problem))
    for i, line, (_, _, plain) in zip(honest, trips, proofs):
        table["roundtrip"]["cases"] += 1
        wire, decoded = work / f"{i}.lean.wire", work / f"{i}.rust.plain"
        problem = None
        if line != "encoded roundtrip-ok":
            problem = f"Lean `{line}`"
        elif wire.read_bytes() != cases[i][3]:
            problem = "the Lean encoding of the prover's proof is not the Rust's"
        elif not decoded.exists() or decoded.read_bytes() != (work / f"{i}.prover.plain").read_bytes():
            problem = "the Rust's decoding of the wire proof is not the prover's proof"
        if problem:
            table["roundtrip"]["differ"] += 1
            differing.append((i, cases[i][0], "roundtrip", "the prover's proof through Proof.toBytes", problem))
        else:
            table["roundtrip"]["decoded"] += 1

    print(f"{len(proofs)} wire proofs ({', '.join(name for name, _, _ in proofs)})")
    print(f"{'kind':<12}{'cases':>8}{'decoded':>9}{'differ':>8}")
    total = Counter()
    for kind in list(dict.fromkeys(case[1] for case in cases)) + ["roundtrip"]:
        row = table[kind]
        total.update(row)
        print(f"{kind:<12}{row['cases']:>8}{row['decoded']:>9}{row['differ']:>8}")
    print(f"{'total':<12}{total['cases']:>8}{total['decoded']:>9}{total['differ']:>8}")

    if differing or failures:
        keep = arguments.keep or Path(tempfile.mkdtemp(prefix="wire-diff-differ-"))
        keep.mkdir(parents=True, exist_ok=True)
        for index, name, kind, label, problem in differing:
            case = keep / f"{index}-{name}-{kind}"
            case.mkdir(exist_ok=True)
            shutil.copy(work / f"{index}.bin", case / "wire.bin")
            (case / "case.txt").write_text(f"{name}: {kind}: {label}\n{problem}\n")
            print(f"DIFFER {name}: {kind}: {label}: {problem}")
        for failure in failures:
            print(f"FAIL {failure}")
        shutil.rmtree(work)
        sys.exit(f"{len(differing)} differing cases, {len(failures)} failures; kept under {keep}")
    shutil.rmtree(work)
    print("0 differences")


if __name__ == "__main__":
    main()
