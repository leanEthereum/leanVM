"""Differential fuzzing of the Lean verifier against the deployed Rust verifier on real proofs.

The fixtures under tests/fixtures/verifier/ are proofs of the leanVM Rust prover in the
Python verifier's four-file format (scripts/export-verifier-fixtures-rust.sh). This driver
mutates every fixture and runs, on the honest proof and on every mutation,

  * the Lean verifier, `lake exe leanvm-verify` (cli/LeanvmVerify.lean): the Lean
    transcription of `python-verifier/verifier.py`, compiled;
  * the Rust verifier, scripts/rust-verifier-cli (`verifier::verify_execution` of leanVM's
    `crates/verifier`, the deployed one), in one `--batch` process;
  * with `--python`, also the Python verifier itself, as a tie-breaker.

It fails if the Lean and the Rust verdicts ever differ, and prints a table of verdicts by
mutation class. A Rust panic or a Lean crash counts as a rejection but is reported.

The structured mutation positions come from an instrumented run of the Python verifier on
the honest proof: the stream offset where every phase of `verify_execution` starts, every
commitment root's two halves, every proof-of-work nonce, and the byte offset and shape of every
Merkle opening. Each structured case changes one thing:

  phase       one bit of the first, middle or last scalar of a phase (low bit of limb 0, top bit
              of limb 2);
  root        the low bit, or a bit of the (must-be-zero) top limb, of a root half;
  nonce       the low bit, the top bit, or a bit of limb 1, of a proof-of-work nonce;
  opening     one bit of a level's first or last leaf word, its first sibling, its top sibling,
              and of a random opening of the level;
  public      one bit of a public input byte (0, 15, 16, 31);
  rows        a table's announced row count one fewer, one more, zero, its full height and above
              the cap, which moves its padding rows (or its height);
  bytecode    one bit of the first, the first nonzero, a middle and the last bytecode byte;
  length      truncations and appends of every file (whole and partial elements, words, digests).

The random cases, from `--seed`, are single random bit flips anywhere (weighted by file size),
random multi-byte corruptions (several bytes of one file, or one random run of bytes), a random
scalar replaced by a random element or by zero, two scalars of one phase swapped, and a random
opening's leaf word replaced; a random edit that leaves the proof unchanged is drawn again.

Usage (from the repository root; the two verifiers built first, see below):
  python3 -I scripts/fuzz-verifier.py tests/fixtures/verifier \\
      [--mutations 250] [--seed 1] [--jobs 8] [--python] [--keep <dir>] [fixture ...]

  ( ulimit -v 40000000; lake build leanvm-verify )
  cargo build --release --manifest-path scripts/rust-verifier-cli/Cargo.toml

The Rust and Python verifiers are those of the containing leanVM commit.

`--mutations` is the number of cases per fixture, structured ones first, then random ones up to
it. Every child process runs under an address-space limit (`--memory-gb`, default 40). The
mutated files of every case on which the verifiers disagree are kept under `--keep` (default: a
new directory under the system temporary directory), with a `case.txt` saying what was changed;
`--log` writes one line per case.
"""

import argparse
import contextlib
import hashlib
import importlib.util
import os
import random
import resource
import shutil
import subprocess
import sys
import tempfile
import time
import zlib
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

PIN = "3a37fb6e1c7423e36b67d1cac4eda70c3ad4dd45"
VERIFIER_SHA256 = "16ac4c0dd33894ddb14e8dad92eb7f9d75ef7d543764903aec983b45e862beef"
FILES = ("bytecode.bin", "public_input.bin", "stream.bin", "merkle_openings.bin")
ROOT = Path(__file__).resolve().parent.parent
TREE = ROOT.parent.parent
LEAN_EXE = ROOT / ".lake" / "build" / "bin" / "leanvm-verify"
RUST_EXE = ROOT / "scripts" / "rust-verifier-cli" / "target" / "release" / "leanvm-rust-verify"


# The Python verifier, instrumented -------------------------------------------------------------


def load_verifier(tree: Path):
    """A fresh copy of the verifier module, so that instrumenting it touches no other."""
    path = tree / "python-verifier" / "verifier.py"
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != VERIFIER_SHA256:
        sys.exit(f"{path} is not the verifier at {PIN} (sha256 {digest})")
    spec = importlib.util.spec_from_file_location("instrumented_verifier", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["instrumented_verifier"] = module
    spec.loader.exec_module(module)
    return module


def instrument(tree: Path, directory: Path) -> dict:
    """Run the Python on the honest proof, recording where each phase, root, nonce and opening is."""
    V = load_verifier(tree)
    events = {"phase": [("sizes", 0)], "nonce": [], "root": [], "merkle": []}
    state = {}
    original_init = V.Transcript.__init__

    def init(self, *args, **kwargs):
        original_init(self, *args, **kwargs)
        state["transcript"] = self

    def offset() -> int:
        return state["transcript"].stream_offset

    def phase(name, function):
        def wrapped(*args, **kwargs):
            events["phase"].append((name, offset()))
            return function(*args, **kwargs)

        return wrapped

    original_grind = V.Transcript.grind_check

    def grind(self, bits):
        events["nonce"].append((self.stream_offset, bits))
        return original_grind(self, bits)

    original_merkle = V.Transcript.merkle

    def merkle(self, root, block_length, queries, leaf_words):
        start = self.opening_offset
        result = original_merkle(self, root, block_length, queries, leaf_words)
        events["merkle"].append((start, len(queries), V.log2_strict(block_length), leaf_words))
        return result

    original_from_halves = V.Digest.from_halves.__func__

    def from_halves(cls, low, high):
        events["root"].append(offset() - 2)
        return original_from_halves(cls, low, high)

    V.Transcript.__init__ = init
    V.Transcript.grind_check = grind
    V.Transcript.merkle = merkle
    V.Digest.from_halves = classmethod(from_halves)
    for name, attribute in (("bus", "verify_bus_balance"), ("flock-zerocheck", "verify_flock_zerocheck"),
                            ("flock-lincheck", "verify_flock_lincheck"), ("ring", "ring_switch"),
                            ("whir", "verify_stacked_opening")):
        setattr(V, attribute, phase(name, getattr(V, attribute)))
    original_table = V.table_sumcheck

    def table(*args, **kwargs):  # the public input phase starts where the table sumcheck ends
        result = original_table(*args, **kwargs)
        events["phase"].append(("public", offset()))
        return result

    V.table_sumcheck = phase("tables", table)
    with contextlib.redirect_stdout(sys.stderr):
        code = V.main([str(directory / name) for name in FILES])
    assert code == 0, f"{directory}: the honest proof is rejected by the Python"
    transcript = state["transcript"]
    events["stream_length"] = len(transcript.proof.stream)
    events["openings_length"] = len(transcript.proof.merkle_openings)
    # The root is read between the sizes and the bus; give it a phase of its own.
    events["phase"].insert(1, ("root", events["root"][0]))
    return events


# Mutations --------------------------------------------------------------------------------------
#
# A case is (category, label, edits); an edit is one of
#   ("flip", file, offset, mask)   XOR a mask into a byte;
#   ("set", file, offset, bytes)   overwrite bytes;
#   ("truncate", file, n)          drop the last n bytes;
#   ("append", file, bytes)        append bytes.


def flip(file, offset, bit=0):
    return ("flip", file, offset, 1 << bit)


def structured_cases(events: dict, sizes: dict, data: dict, rng: random.Random) -> list:
    cases = [("honest", "the honest proof", [])]
    S, O = "stream.bin", "merkle_openings.bin"
    bounds = events["phase"] + [("end", events["stream_length"])]
    for (phase, first), (_, end) in zip(bounds, bounds[1:]):
        if first == end:  # the public phase and the ring switch may read no scalar
            continue
        for position in sorted({first, (first + end) // 2, end - 1}):
            cases.append(("phase", f"{phase} scalar {position} limb 0 bit 0", [flip(S, 24 * position)]))
            cases.append(("phase", f"{phase} scalar {position} limb 2 bit 63", [flip(S, 24 * position + 23, 7)]))
    for index, position in enumerate(events["root"]):
        for half in (0, 1):
            at = 24 * (position + half)
            cases.append(("root", f"root {index} half {half} low bit", [flip(S, at)]))
            cases.append(("root", f"root {index} half {half} limb 2 bit 0", [flip(S, at + 16)]))
    for position, bits in events["nonce"]:
        at = 24 * position
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) low bit", [flip(S, at)]))
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) bit 63", [flip(S, at + 7, 7)]))
        cases.append(("nonce", f"nonce at scalar {position} ({bits} bits) limb 1 bit 0", [flip(S, at + 8)]))
    for level, (start, count, height, words) in enumerate(events["merkle"]):
        size = 8 * words + 32 * height
        last = start + (count - 1) * size
        middle = start + rng.randrange(count) * size
        cases.append(("opening", f"opening batch {level} first leaf, word 0", [flip(O, start)]))
        cases.append(("opening", f"opening batch {level} last leaf, last word, top bit", [flip(O, last + 8 * words - 1, 7)]))
        cases.append(("opening", f"opening batch {level} first sibling", [flip(O, start + 8 * words)]))
        cases.append(("opening", f"opening batch {level} last opening, top sibling", [flip(O, last + size - 1, 7)]))
        at = middle + rng.randrange(size)
        cases.append(("opening", f"opening batch {level} random byte {at - start} of the batch", [flip(O, at, rng.randrange(8))]))
    for at in (0, 15, 16, 31):
        cases.append(("public", f"public input byte {at}", [flip("public_input.bin", at)]))
    stream = data[S]
    for table in range(6):  # the announced row counts, scalars 1..6: the padding rows move
        at = 24 * (1 + table)
        rows = int.from_bytes(stream[at : at + 8], "little")
        full = 1 << max(rows - 1, 0).bit_length()
        changes = (("one fewer", rows - 1), ("one more", rows + 1), ("none", 0), ("a full table", full), ("above the cap", 2**32 + 1))
        for label, value in changes:
            if 0 <= value != rows:
                cases.append(("rows", f"table {table} rows {rows} -> {value} ({label})", [("set", S, at, value.to_bytes(8, "little"))]))
    bytecode = data["bytecode.bin"]
    nonzero = next(i for i, b in enumerate(bytecode) if b)
    for label, at in (("byte 0", 0), (f"first nonzero byte {nonzero}", nonzero),
                      ("middle byte", len(bytecode) // 2), ("last byte", len(bytecode) - 1)):
        cases.append(("bytecode", f"bytecode {label}", [flip("bytecode.bin", at)]))
    length = [
        ("stream.bin", "truncate", 24, "last scalar dropped"),
        ("stream.bin", "truncate", 1, "stream cut mid-scalar"),
        ("stream.bin", "truncate", sizes["stream.bin"], "empty stream"),
        ("stream.bin", "append", bytes(24), "zero scalar appended"),
        ("stream.bin", "append", bytes(rng.randrange(256) for _ in range(24)), "random scalar appended"),
        ("stream.bin", "append", bytes(5), "partial scalar appended"),
        ("merkle_openings.bin", "truncate", 32, "last sibling dropped"),
        ("merkle_openings.bin", "truncate", 1, "openings cut by one byte"),
        ("merkle_openings.bin", "truncate", sizes["merkle_openings.bin"], "empty openings"),
        ("merkle_openings.bin", "append", bytes(8), "word appended to the openings"),
        ("merkle_openings.bin", "append", bytes(32), "digest appended to the openings"),
        ("public_input.bin", "truncate", 1, "public input cut by one byte"),
        ("public_input.bin", "append", bytes(1), "byte appended to the public input"),
        ("bytecode.bin", "truncate", 8, "last bytecode word dropped"),
        ("bytecode.bin", "truncate", 3, "bytecode cut mid-word"),
        ("bytecode.bin", "append", bytes(8), "zero bytecode word appended"),
        ("bytecode.bin", "append", bytes(sizes["bytecode.bin"]), "bytecode doubled with zero words"),
        ("bytecode.bin", "truncate", sizes["bytecode.bin"] // 2, "bytecode halved"),
    ]
    for file, operation, argument, label in length:
        cases.append(("length", label, [(operation, file, argument)]))
    return cases


def random_case(events: dict, sizes: dict, data: dict, rng: random.Random):
    S = "stream.bin"
    kind = rng.choices(["flip", "bytes", "run", "scalar", "zero", "swap", "leaf"], [30, 15, 10, 15, 10, 10, 10])[0]
    if kind == "flip":
        file = rng.choices(FILES, [sizes[f] for f in FILES])[0]
        at, bit = rng.randrange(sizes[file]), rng.randrange(8)
        return ("random-flip", f"{file} byte {at} bit {bit}", [flip(file, at, bit)])
    if kind == "bytes":
        file = rng.choices(FILES[1:], [1, 3, 3])[0]
        count = rng.randrange(2, 9)
        edits = [("set", file, rng.randrange(sizes[file]), bytes([rng.randrange(256)])) for _ in range(count)]
        return ("random-bytes", f"{file} {count} random bytes at {sorted(e[2] for e in edits)}", edits)
    if kind == "run":
        file = rng.choices(FILES[2:], [1, 1])[0]
        length = rng.randrange(2, 65)
        at = rng.randrange(sizes[file] - length)
        return ("random-run", f"{file} bytes {at}..{at + length} random", [("set", file, at, rng.randbytes(length))])
    scalars = events["stream_length"]
    if kind == "scalar":
        position = rng.randrange(scalars)
        return ("random-scalar", f"scalar {position} replaced by a random element", [("set", S, 24 * position, rng.randbytes(24))])
    if kind == "zero":
        position = rng.randrange(scalars)
        return ("random-scalar", f"scalar {position} replaced by zero", [("set", S, 24 * position, bytes(24))])
    if kind == "swap":
        bounds = [p for p in events["phase"]] + [("end", scalars)]
        spans = [(name, first, end) for (name, first), (_, end) in zip(bounds, bounds[1:]) if end - first >= 2]
        name, first, end = rng.choice(spans)
        i, j = rng.sample(range(first, end), 2)
        stream = data[S]
        return ("random-swap", f"{name} scalars {i} and {j} swapped",
                [("set", S, 24 * i, stream[24 * j:24 * j + 24]), ("set", S, 24 * j, stream[24 * i:24 * i + 24])])
    start, count, height, words = rng.choice(events["merkle"])
    opening = rng.randrange(count)
    word = rng.randrange(words)
    at = start + opening * (8 * words + 32 * height) + 8 * word
    return ("random-leaf", f"opening at byte {start} #{opening} leaf word {word} replaced", [("set", "merkle_openings.bin", at, rng.randbytes(8))])


def apply(data: dict, edits: list) -> dict:
    """The mutated files, only those an edit touches."""
    out = {}
    for edit in edits:
        file = edit[1]
        buffer = out.setdefault(file, bytearray(data[file]))
        if edit[0] == "flip":
            buffer[edit[2]] ^= edit[3]
        elif edit[0] == "set":
            buffer[edit[2]:edit[2] + len(edit[3])] = edit[3]
        elif edit[0] == "truncate":
            del buffer[len(buffer) - edit[2]:]
        elif edit[0] == "append":
            buffer.extend(edit[2])
    return {file: bytes(buffer) for file, buffer in out.items()}


def describe(edit) -> str:
    if edit[0] == "flip":
        return f"flip {edit[1]} {edit[2]} 0x{edit[3]:02x}"
    if edit[0] == "set":
        return f"set {edit[1]} {edit[2]} {edit[3].hex()}"
    if edit[0] == "truncate":
        return f"truncate {edit[1]} {edit[2]}"
    return f"append {edit[1]} {edit[2].hex()}"


# Running the verifiers --------------------------------------------------------------------------


def limit(gigabytes: int):
    def set_limit():
        cap = gigabytes << 30
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    return set_limit


def run_lean(exe: Path, paths: list, memory: int, timeout: int) -> tuple:
    start = time.monotonic()
    try:
        run = subprocess.run([str(exe), *map(str, paths)], capture_output=True, text=True, timeout=timeout,
                             preexec_fn=limit(memory))
    except subprocess.TimeoutExpired:
        return "timeout", f"no verdict after {timeout} s", time.monotonic() - start
    elapsed = time.monotonic() - start
    message = (run.stdout.strip().splitlines() or [""])[-1]
    if run.returncode == 0 and message == "verification succeeded":
        verdict = "accept"
    elif run.returncode == 1 and message == "verification failed":
        verdict = "reject"
    else:
        verdict = "crash"
        message = f"exit {run.returncode}: {(run.stdout + run.stderr).strip()[-300:]}"
    if "PANIC" in run.stderr:
        message += f" [Lean panic: {run.stderr.strip()[-300:]}]"
    return verdict, message, elapsed


def run_python(tree: Path, paths: list, memory: int, timeout: int) -> tuple:
    start = time.monotonic()
    try:
        run = subprocess.run([sys.executable, "-I", str(tree / "python-verifier" / "verifier.py"), *map(str, paths)],
                             capture_output=True, text=True, timeout=timeout, preexec_fn=limit(memory))
    except subprocess.TimeoutExpired:
        return "timeout", f"no verdict after {timeout} s", time.monotonic() - start
    message = ((run.stdout + run.stderr).strip().splitlines() or [""])[-1]
    verdict = "accept" if run.returncode == 0 and message == "verification succeeded" else "reject"
    if run.returncode not in (0, 1):
        verdict, message = "crash", f"exit {run.returncode}: {(run.stdout + run.stderr).strip()[-300:]}"
    return verdict, message, time.monotonic() - start


def run_rust(exe: Path, cases: list, memory: int) -> list:
    """Every case in one `--batch` process: one verdict line per line of four paths."""
    lines = "".join("\t".join(map(str, c["paths"])) + "\n" for c in cases)
    run = subprocess.run([str(exe), "--batch"], input=lines, capture_output=True, text=True,
                         preexec_fn=limit(memory), check=True)
    verdicts = []
    for line in run.stdout.splitlines():
        head, _, reason = line.partition(" ")
        verdicts.append((head, reason))
    assert len(verdicts) == len(cases), run.stderr
    return verdicts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("fixtures", type=Path, help="directory of fixtures (tests/fixtures/verifier)")
    parser.add_argument("only", nargs="*", help="fixtures to fuzz (default: every one)")
    parser.add_argument("--mutations", type=int, default=250, help="cases per fixture, the honest one included")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--jobs", type=int, default=8, help="Lean (and Python) verifiers run at once")
    parser.add_argument("--python", action="store_true", help="also run the Python verifier on every case")
    parser.add_argument("--lean-exe", type=Path, default=LEAN_EXE)
    parser.add_argument("--rust-exe", type=Path, default=RUST_EXE)
    parser.add_argument("--memory-gb", type=int, default=40, help="address-space limit of every child process")
    parser.add_argument("--timeout", type=int, default=900, help="seconds per Lean or Python run")
    parser.add_argument("--keep", type=Path, help="where to keep the files of disagreeing cases")
    parser.add_argument("--log", type=Path, help="write one line per case here")
    arguments = parser.parse_args()
    tree, fixtures = TREE, arguments.fixtures.resolve()
    for exe in (arguments.lean_exe, arguments.rust_exe):
        if not exe.exists():
            sys.exit(f"{exe} is not built; see the usage in {Path(__file__).name}")
    names = arguments.only or sorted(p.name for p in fixtures.iterdir() if p.is_dir())
    scratch = Path(tempfile.mkdtemp(prefix="fuzz-verifier-"))
    keep = arguments.keep or Path(tempfile.mkdtemp(prefix="fuzz-verifier-divergent-"))
    cases = []
    try:
        for name in names:
            directory = fixtures / name
            data = {file: (directory / file).read_bytes() for file in FILES}
            sizes = {file: len(content) for file, content in data.items()}
            events = instrument(tree, directory)
            print(f"{name}: {events['stream_length']} scalars, phases {events['phase']}, "
                  f"{len(events['root'])} roots, {len(events['nonce'])} nonces, "
                  f"{len(events['merkle'])} opening batches", file=sys.stderr)
            rng = random.Random(arguments.seed * 1_000_003 + zlib.crc32(name.encode()))
            generated = structured_cases(events, sizes, data, rng)[:arguments.mutations]
            while len(generated) < arguments.mutations:
                case = random_case(events, sizes, data, rng)
                # A random edit can leave the proof as it was (a zero scalar zeroed, equal scalars
                # swapped); draw again, so that every random case is a different proof.
                if any(content != data[file] for file, content in apply(data, case[2]).items()):
                    generated.append(case)
            for index, (category, label, edits) in enumerate(generated):
                mutated = apply(data, edits)
                case_dir = scratch / name / str(index)
                case_dir.mkdir(parents=True)
                paths = []
                for file in FILES:
                    if file in mutated:
                        (case_dir / file).write_bytes(mutated[file])
                        paths.append(case_dir / file)
                    else:
                        paths.append(directory / file)
                cases.append({"fixture": name, "index": index, "category": category, "label": label,
                              "edits": edits, "paths": paths, "dir": case_dir})
        print(f"{len(cases)} cases; Rust verifier ...", file=sys.stderr)
        start = time.monotonic()
        for case, (verdict, reason) in zip(cases, run_rust(arguments.rust_exe, cases, arguments.memory_gb)):
            case["rust"] = verdict
            case["rust_reason"] = reason
        rust_time = time.monotonic() - start
        print(f"Rust: {rust_time:.1f} s for {len(cases)} cases; Lean verifier ({arguments.jobs} at once) ...",
              file=sys.stderr)

        done = Counter()

        def lean_job(case):
            case["lean"], case["lean_message"], case["lean_time"] = run_lean(
                arguments.lean_exe, case["paths"], arguments.memory_gb, arguments.timeout)
            done["lean"] += 1
            agree = "ok" if case["lean"] == case["rust"] or {case["lean"], case["rust"]} <= {"reject", "panic", "crash"} else "DIFFER"
            print(f"[{done['lean']}/{len(cases)}] {case['fixture']} #{case['index']} {case['category']}: "
                  f"{case['label']}: Lean {case['lean']} ({case['lean_time']:.1f} s), Rust {case['rust']} "
                  f"{case['rust_reason']} [{agree}]", file=sys.stderr, flush=True)

        def python_job(case):
            case["python"], case["python_message"], case["python_time"] = run_python(
                tree, case["paths"], arguments.memory_gb, arguments.timeout)

        start = time.monotonic()
        with ThreadPoolExecutor(arguments.jobs) as pool:
            # Slowest first: the Lean runs, then the Python ones fill the tail.
            futures = [pool.submit(lean_job, case) for case in cases]
            if arguments.python:
                futures += [pool.submit(python_job, case) for case in cases]
            for future in futures:
                future.result()
        lean_time = time.monotonic() - start

        # Verdicts: a Rust panic or a Lean crash is a rejection, but counted on its own.
        def accepted(verdict):
            return verdict == "accept"

        differ = [c for c in cases if accepted(c["lean"]) != accepted(c["rust"])]
        python_differ = [c for c in cases if arguments.python and accepted(c["python"]) != accepted(c["rust"])]
        table = defaultdict(Counter)
        for case in cases:
            row = table[(case["fixture"], case["category"])]
            row["cases"] += 1
            row["both accept"] += accepted(case["lean"]) and accepted(case["rust"])
            row["both reject"] += not accepted(case["lean"]) and not accepted(case["rust"])
            row["Lean only accepts"] += accepted(case["lean"]) and not accepted(case["rust"])
            row["Rust only accepts"] += accepted(case["rust"]) and not accepted(case["lean"])
            row["Rust panic"] += case["rust"] == "panic"
            row["Lean crash/timeout"] += case["lean"] in ("crash", "timeout")
            if arguments.python:
                row["Python differs"] += accepted(case["python"]) != accepted(case["rust"])
            row["Lean seconds"] += case["lean_time"]
        columns = ["cases", "both accept", "both reject", "Lean only accepts", "Rust only accepts", "Rust panic",
                   "Lean crash/timeout"] + (["Python differs"] if arguments.python else []) + ["Lean seconds"]
        header = ["fixture", "class", *columns]
        rows = [[fixture, category, *(f"{table[(fixture, category)][c]:.0f}" for c in columns)]
                for fixture, category in sorted(table)]
        totals = Counter()
        for row in table.values():
            totals.update(row)
        rows.append(["all", "all", *(f"{totals[c]:.0f}" for c in columns)])
        widths = [max(len(r[i]) for r in [header, *rows]) for i in range(len(header))]
        print()
        for row in [header, ["-" * w for w in widths], *rows]:
            print("  ".join(cell.ljust(w) if i < 2 else cell.rjust(w) for i, (cell, w) in enumerate(zip(row, widths))))
        reasons = Counter(c["rust_reason"] or "accepted" for c in cases)
        print("\nRust verdicts by reason:")
        for reason, count in reasons.most_common():
            print(f"  {count:5}  {reason}")
        accepted_mutations = [c for c in cases if c["category"] != "honest" and accepted(c["lean"]) and accepted(c["rust"])]
        if accepted_mutations:
            print("\nMutations BOTH verifiers accept:")
            for case in accepted_mutations:
                print(f"  {case['fixture']} #{case['index']}: {case['label']}: {'; '.join(map(describe, case['edits']))}")
        print(f"\nRust {rust_time:.1f} s (one process); Lean {totals['Lean seconds']:.0f} s of runs, "
              f"{lean_time:.0f} s wall at {arguments.jobs} jobs")
        if arguments.log:
            with arguments.log.open("w") as log:
                for c in cases:
                    log.write("\t".join([c["fixture"], str(c["index"]), c["category"], c["label"], c["lean"],
                                         f"{c['lean_time']:.1f}", c["rust"], c["rust_reason"],
                                         c.get("python", "-"), c.get("python_message", "-"),
                                         "; ".join(map(describe, c["edits"]))]) + "\n")
        failures = differ + [c for c in python_differ if c not in differ]
        for case in failures:
            target = keep / case["fixture"] / str(case["index"])
            target.mkdir(parents=True, exist_ok=True)
            for path in case["paths"]:
                shutil.copy(path, target / Path(path).name)
            (target / "case.txt").write_text(
                f"fixture {case['fixture']} case {case['index']} ({case['category']}): {case['label']}\n"
                + "".join(describe(e) + "\n" for e in case["edits"])
                + f"Lean {case['lean']}: {case['lean_message']}\nRust {case['rust']}: {case['rust_reason']}\n"
                + (f"Python {case['python']}: {case['python_message']}\n" if arguments.python else ""))
        for case in differ:
            print(f"DIFFER {case['fixture']} #{case['index']} {case['label']}: Lean {case['lean']}, "
                  f"Rust {case['rust']} {case['rust_reason']} (kept in {keep / case['fixture'] / str(case['index'])})")
        for case in python_differ:
            print(f"PYTHON DIFFERS FROM RUST {case['fixture']} #{case['index']} {case['label']}: "
                  f"Python {case['python']} {case['python_message']}, Rust {case['rust']} {case['rust_reason']}")
        print(f"\n{len(differ)} Lean/Rust verdict difference(s) in {len(cases)} cases"
              + (f"; {len(python_differ)} Python/Rust" if arguments.python else ""))
        sys.exit(1 if differ else 0)
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
        if keep != arguments.keep and not any(keep.iterdir()):
            keep.rmdir()


if __name__ == "__main__":
    main()
