"""Check the pinned Aeneas outcome for every loop shape in tests/loop_borrows.rs.

Run under the heavy lock from this directory after bootstrap. A changed outcome fails loudly,
so a tool upgrade that repairs or newly breaks a shape is noticed.
"""
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

here = Path(__file__).resolve().parent
formal = here.parent
charon = formal / ".tools/aeneas/charon"
generator = formal / ".tools/aeneas-source/src/_build/default/main.exe"
source = here / "tests/loop_borrows.rs"
expected = {
    "rejected_ref_ref": "Internal error, please file an issue",
    "rejected_view": "Internal error, please file an issue",
    "rejected_shared": "Unreachable",
    "rejected_outer": "Internal error, please file an issue",
    "rejected_split_last": "Could not match the contexts",
    "rejected_branch_on_borrow": "Could not match the contexts",
    "rejected_closure_in_loop": "Internal error, please file an issue",
    "rejected_projected_weight": "The input arguments don't have the proper type",
    "rejected_inherited_loop": "Could not find: type_var_id",
}
text = source.read_text()
names = re.findall(r"^pub fn (\w+)", text, re.M)
# Each function's first line, to attribute errors that name only a source span.
starts = sorted((text[:m.start()].count("\n") + 1, m.group(1)) for m in re.finditer(r"^(?:pub )?fn (\w+)", text, re.M))
with tempfile.TemporaryDirectory(prefix="whir-loop-borrows.") as work:
    llbc = Path(work) / "loop_borrows.llbc"
    env = dict(os.environ, RUSTUP_TOOLCHAIN="nightly-2026-09-17")
    subprocess.run([charon, "rustc", "--preset=aeneas", "--dest-file", llbc, "--", source,
                    "--crate-name", "loop_borrows", "--crate-type", "lib", "--edition=2024"],
                   env=env, check=True, capture_output=True)
    run = subprocess.run([generator, "-backend", "lean", "-all-computable", "-no-progress-bar",
                          "-dest", work, llbc], capture_output=True, text=True)
    log = re.sub(r"\x1b\[[0-9;]*m", "", run.stdout + run.stderr)
failures = {}
error = None
for line in log.splitlines():
    if line.startswith("[Error]"):
        error = line.removeprefix("[Error]").strip()
    span = re.match(r"Source: '[^']*loop_borrows\.rs', lines (\d+):", line)
    if span and error and error.startswith("Could not find: type_var_id"):
        owner = [name for start, name in starts if start <= int(span.group(1))][-1]
        failures.setdefault(owner, "Could not find: type_var_id")
    match = re.search(r"Could not translate the body of function 'loop_borrows::(\w+)", line)
    if match:
        failures[match.group(1)] = error
problems = []
for name in names:
    want = expected.get(name)
    got = failures.get(name)
    if want is None and got is not None:
        problems.append(f"{name}: expected translation, got {got!r}")
    elif want is not None and got != want:
        problems.append(f"{name}: expected {want!r}, got {got!r}")
if problems or not names:
    sys.exit("Loop outcomes changed:\n" + "\n".join(problems))
for name in names:
    print(f"{name}: {failures.get(name, 'translated')}")
