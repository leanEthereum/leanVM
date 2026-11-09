"""Differential test of the statement's honest prover against the Lean and the Rust verifier.

For every case directory (scripts/export-prover-traces-rust.sh writes them: a program's bytecode,
its public input, an execution's memory and `trace.txt`, and the Rust prover's proof of it), this

  1. runs `lake exe leanvm-prove` (cli/LeanvmProve.lean: `LeanVM.Prover.prove` with Keccak-256
     and Keccak-f[1600], the statement's prover compiled) on the case, timing it, and sets the
     time beside the Rust prover's (`rust.txt`);
  2. checks that the Lean-made proof is byte-identical to the Rust prover's, and, with
     `--expected <dir>`, to the committed proof `<dir>/<case>/` (`stream.bin`,
     `merkle_phases.bin`, and the wire encoding `proof.wire`, which `leanvm-prove` writes as
     `lean_proof.wire` from `Proof.toBytes`)
     (tests/fixtures/verifier: the same twelve cases, export-verifier-fixtures-rust.sh); reported,
     and required with `--identical` (as the gate runs it);
  3. writes the Lean-made proof as a verifier fixture (bytecode, public input and the proof's files)
     and runs scripts/fuzz-verifier.py on the fixtures: the Lean verifier (`leanvm-verify`) and
     the Rust verifier (`scripts/rust-verifier-cli`) on the honest Lean-made proof and on
     `--mutations` mutations of it, structured and random. With `--identical` and `--expected`,
     when every Lean-made proof is the committed one byte for byte, this step is skipped: those
     are the fixtures the verifier differential (fuzz-verifier.py) already fuzzes.

It fails unless every Lean-made proof is accepted by both verifiers and every mutation is
rejected by both (and the two verifiers agree everywhere), and, with `--identical`, unless every
Lean-made proof is the Rust prover's (and the committed one) byte for byte. The proofs are made
`--jobs` at a time.

Usage (the three executables built first, see formal/check-all.sh):
  python3 -I scripts/prover-diff.py <cases dir> [--mutations 60] [--jobs 4]
      [--identical] [--expected tests/fixtures/verifier] [case ...]
"""

import argparse
import concurrent.futures
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from proofio import limit

ROOT = Path(__file__).resolve().parent.parent
PROVE_EXE = ROOT / ".lake" / "build" / "bin" / "leanvm-prove"
PARTS = ("stream.bin", "merkle_phases.bin", "proof.wire")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("cases", type=Path)
    parser.add_argument("only", nargs="*")
    parser.add_argument("--mutations", type=int, default=60, help="fuzz cases per proof, the honest one included")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--memory-gb", type=int, default=16)
    parser.add_argument("--prove-exe", type=Path, default=PROVE_EXE)
    parser.add_argument("--identical", action="store_true",
                        help="fail unless every Lean-made proof is the Rust prover's byte for byte")
    parser.add_argument("--expected", type=Path,
                        help="committed proofs to compare with too: <dir>/<case>/{" + ",".join(PARTS) + "}")
    arguments = parser.parse_args()
    if not arguments.prove_exe.exists():
        sys.exit(f"{arguments.prove_exe} is not built (lake build leanvm-prove)")
    cases = arguments.cases.resolve()
    names = arguments.only or sorted(p.name for p in cases.iterdir() if (p / "trace.txt").exists())
    fixtures = Path(tempfile.mkdtemp(prefix="prover-diff-"))
    rows = []
    failed = False
    try:
        def prove(name):
            start = time.monotonic()
            run = subprocess.run([str(arguments.prove_exe), str(cases / name)], capture_output=True, text=True,
                                 preexec_fn=limit(arguments.memory_gb, unlimited_stack=True))
            return run, time.monotonic() - start

        with concurrent.futures.ThreadPoolExecutor(max_workers=arguments.jobs) as pool:
            runs = list(pool.map(prove, names))
        for name, (run, seconds) in zip(names, runs):
            directory = cases / name
            if run.returncode != 0:
                print(f"{name}: leanvm-prove failed ({run.returncode}): {run.stdout}{run.stderr}")
                failed = True
                continue
            rust = (directory / "rust.txt").read_text().strip() if (directory / "rust.txt").exists() else "-"
            identical = all(
                (directory / f"lean_{f}").read_bytes() == (directory / f).read_bytes()
                for f in PARTS if (directory / f).exists())
            expected = "-"
            if arguments.expected is not None:
                committed = arguments.expected.resolve() / name
                expected = "yes" if all(
                    (committed / f).exists()
                    and (directory / f"lean_{f}").read_bytes() == (committed / f).read_bytes()
                    for f in PARTS) else "no"
            if arguments.identical and (not identical or expected == "no"):
                print(f"FAIL {name}: the Lean-made proof is not the Rust prover's (identical: "
                      f"{'yes' if identical else 'no'}, committed: {expected})")
                failed = True
            target = fixtures / name
            target.mkdir()
            for f in ("bytecode.bin", "public_input.bin"):
                shutil.copy(directory / f, target / f)
            for f in PARTS:
                shutil.copy(directory / f"lean_{f}", target / f)
            rows.append((name, f"{seconds:.1f}", rust, "yes" if identical else "no", expected))
            print(f"{name}: Lean prover {seconds:.1f} s, Rust prover {rust} s, "
                  f"identical to the Rust proof: {'yes' if identical else 'no'}, "
                  f"to the committed proof: {expected}", flush=True)
        if not rows:
            sys.exit("no proof to test")
        accepted = rejected = honest = 0
        bad = []
        # Lean-made proofs that are all the committed fixtures byte for byte are the very proofs
        # the verifier differential (fuzz-verifier.py on tests/fixtures/verifier) fuzzes: skip.
        fuzzed = not (arguments.identical and arguments.expected is not None and not failed
                      and all(row[4] == "yes" for row in rows))
        if not fuzzed:
            print("\nevery Lean-made proof is the committed fixture byte for byte: not fuzzed again "
                  "(fuzz-verifier.py fuzzes the fixtures)")
        else:
            log = fixtures / "fuzz.log"
            fuzz = subprocess.run([sys.executable, "-I", str(ROOT / "scripts" / "fuzz-verifier.py"), str(fixtures),
                                   "--mutations", str(arguments.mutations), "--jobs", str(arguments.jobs),
                                   "--memory-gb", str(arguments.memory_gb), "--log", str(log)])
            if fuzz.returncode != 0:
                failed = True
            for line in log.read_text().splitlines():
                fields = line.split("\t")
                fixture, index, category, label, lean, _, rust = fields[:7]
                both_accept = lean == "accept" and rust == "accept"
                both_reject = lean != "accept" and rust != "accept"
                if category == "honest":  # each proof's structured and wire forms
                    honest += 1
                    accepted += both_accept
                    if not both_accept:
                        bad.append(f"honest proof of {fixture} not accepted: Lean {lean}, Rust {rust}")
                else:
                    rejected += both_reject
                    if not both_reject:
                        bad.append(f"{fixture} #{index} {label}: Lean {lean}, Rust {rust}")
            print(f"\nLean-made proofs accepted by both verifiers: {accepted} of {honest} "
                  f"({len(rows)} proofs, structured and wire); "
                  f"mutations rejected by both: {rejected}")
        print("\ncase                    Lean prover s  Rust prover s  identical  committed")
        for row in rows:
            print(f"{row[0]:23} {row[1]:>13}  {row[2]:>13}  {row[3]:>9}  {row[4]:>9}")
        for b in bad:
            print("FAIL", b)
        sys.exit(1 if failed or bad or (fuzzed and (honest != 2 * len(rows) or accepted != honest)) else 0)
    finally:
        shutil.rmtree(fixtures, ignore_errors=True)


if __name__ == "__main__":
    main()
