"""Run under the documented memory-capped scope after building patched Charon."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

here = Path(__file__).resolve().parent
formal = here.parent
original = formal / ".tools/aeneas/charon"
patched = formal / ".tools/aeneas-source/charon/charon/target/release/charon"
generator = formal / ".tools/aeneas-source/src/_build/default/main.exe"
fixture = here / "tests/array_builtin_mono.rs"
root = "array_builtin_mono::repeat_seed"

with tempfile.TemporaryDirectory(prefix="aeneas-array-reproducer-") as directory:
    work = Path(directory)
    for label, executable in (("before", original), ("after", patched), ("generic", patched)):
        dest = work / label
        dest.mkdir()
        llbc = dest / "arrayrepeat.llbc"
        mode_args = [] if label == "generic" else ["--monomorphize"]
        subprocess.run([str(executable), "rustc", "--preset=aeneas", "--mir", "optimized",
                        *mode_args, "--start-from", root, "--dest-file", str(llbc),
                        "--", "--crate-type", "lib", "--crate-name", "array_builtin_mono",
                        str(fixture)], cwd=formal, check=True)
        result = subprocess.run(["python3", str(here / "check-extracted-root.py"), str(llbc), root],
                                text=True, capture_output=True)
        if label == "before":
            if result.returncode == 0 or "references missing functions" not in result.stderr:
                raise SystemExit("Original compiler did not reproduce the missing array builtin")
            print(result.stderr.strip(), flush=True)
        else:
            if result.returncode:
                raise SystemExit(result.stderr)
            print(result.stdout.strip(), flush=True)
            subprocess.run([str(generator), "-backend", "lean", "-namespace", "ArrayRepeat",
                            "-all-computable", "-abort-on-error", "-no-progress-bar",
                            "-dest", str(dest), str(llbc)], cwd=formal, check=True)
            subprocess.run(["lake", "env", "lean", "--root=" + str(dest), "-o",
                            str(dest / "Arrayrepeat.olean"), str(dest / "Arrayrepeat.lean")],
                           cwd=formal, check=True)
            environment = os.environ.copy()
            environment["LEAN_PATH"] = str(dest)
            subprocess.run(["lake", "env", "lean", "--run",
                            str(here / "tests/array_builtin_mono_check.lean")],
                           cwd=formal, env=environment, check=True)
    excluded = subprocess.run([str(patched), "rustc", "--preset=aeneas", "--mir", "optimized",
                               "--monomorphize", "--start-from", root,
                               "--exclude", "core::array::repeat", "--dest-file",
                               str(work / "excluded.llbc"), "--", "--crate-type", "lib",
                               "--crate-name", "array_builtin_mono", str(fixture)],
                              cwd=formal, text=True, capture_output=True)
    if excluded.returncode == 0 or "array/index synthesis requires a translated function declaration" not in excluded.stderr:
        raise SystemExit("Explicitly excluded array declaration did not fail loudly")
    source = work / "source-smoke.rs"
    source.write_text('include!(' + json.dumps(str(fixture)) + ');\nfn main() { for seed in [0u8,17,255] { assert_eq!(repeat_seed(seed),[seed;3]); } println!("Rust repeat agrees for seeds 0, 17, 255"); }\n')
    executable = work / "source-smoke"
    subprocess.run(["rustc", "+1.97.0", str(source), "-o", str(executable)], check=True)
    subprocess.run([str(executable)], check=True)
    print("Original rejection, repaired kernel theorem and execution, and exclusion guard passed")
