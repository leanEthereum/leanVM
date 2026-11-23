"""`lake-cache.py` on fixtures: what it packs, what it refuses, what it never installs, and a round trip through Lake.

  python3 -I tools/lake-cache-test.py        (needs `lake`, with the toolchain of `formal/lean-toolchain`)
"""
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parent.parent
SCRIPT = FORMAL / "lake-cache.py"
DEP, ART = "0123456789abcdef", "fedcba9876543210.olean"


def lake(ws: Path, cache: Path, *args: str) -> str:
    env = {**os.environ, "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true", "LAKE_CACHE_DIR": str(cache)}
    r = subprocess.run(["lake", *args], cwd=ws, env=env, capture_output=True, text=True)
    check(r.returncode == 0, f"lake {' '.join(args)} failed in {ws}:\n{r.stdout}{r.stderr}")
    return r.stdout + r.stderr


def round_trip(root: Path) -> None:
    """A two-module workspace built, packed, unpacked for a copy at another path: Lake rebuilds nothing."""
    ws = root / "a"
    write(ws / "lakefile.toml", 'name = "toy"\ndefaultTargets = ["Toy"]\n\n[[lean_lib]]\nname = "Toy"\n')
    shutil.copy(FORMAL / "lean-toolchain", ws / "lean-toolchain")
    write(ws / "Toy/A.lean", "def a : Nat := 41\n")
    write(ws / "Toy/B.lean", "import Toy.A\ntheorem b : a + 1 = 42 := by decide\n")
    write(ws / "Toy.lean", "import Toy.B\n")
    lake(ws, root / "cache", "build")
    r = run("pack", ws, root / "a.tar.zst", "--cache", root / "cache")
    check(r.returncode == 0, f"pack failed: {r.stderr}")
    copy = root / "b"
    shutil.copytree(ws, copy, ignore=shutil.ignore_patterns(".lake"))
    r = run("unpack", copy, root / "a.tar.zst", "--cache", root / "other")
    check(r.returncode == 0, f"unpack failed: {r.stderr}")
    out = lake(copy, root / "other", "build")
    check("Built" not in out, f"Lake rebuilt what the cache held:\n{out}")
    lake(copy, root / "other", "build", "--no-build")

    text = (ws / "lakefile.toml").read_text()
    write(ws / "lakefile.toml", text + 'moreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n')
    lake(ws, root / "cache", "build")
    r = run("pack", ws, root / "dev.tar.zst", "--cache", root / "cache")
    check(r.returncode != 0 and "without the kernel" in r.stderr, "a build through moreLeanArgs without the kernel was packed")


def run(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-I", str(SCRIPT), *map(str, args)], capture_output=True, text=True)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def check(ok: bool, what: str) -> None:
    if not ok:
        sys.exit(f"lake-cache-test: {what}")


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        cases(Path(tmp))
    with tempfile.TemporaryDirectory() as tmp:
        round_trip(Path(tmp))
    print("lake-cache-test: ok")


def cases(root: Path) -> None:
    pkg, cache, other, archive = root / "pkg", root / "cache", root / "other", root / "a.tar.zst"
    write(pkg / "lake-manifest.json", json.dumps({"packagesDir": ".lake/packages", "packages": []}))
    trace = {"depHash": DEP, "inputs": [["options", [["-DwarningAsError=true", "1"]]]], "outputs": {"o": [ART]}}
    write(pkg / ".lake/build/lib/lean/A.trace", json.dumps(trace))
    write(pkg / ".lake/build/lib/lean/Cut.trace", '{"depHash": "01')  # cut short by a stopped build
    write(cache / "artifacts/0123456789abcdef.c", os.urandom(1 << 19).hex())  # zstd blocks before the cut one
    write(cache / f"outputs/pkg/{DEP}.json", json.dumps({"data": {"o": [ART], "c": "0123456789abcdef.c"}}))
    write(cache / f"artifacts/{ART}", "olean")
    write(cache / "artifacts/0000000000000000.olean", "not in the build")

    r = run("pack", pkg, archive, "--cache", cache)
    check(r.returncode == 0, f"pack failed: {r.stderr}")
    r = run("unpack", pkg, archive, "--cache", other)
    check(r.returncode == 0, f"unpack failed: {r.stderr}")
    check((other / f"artifacts/{ART}").read_text() == "olean" and (other / f"outputs/pkg/{DEP}.json").is_file(),
          "the build's entry was not carried")
    check(not (other / "artifacts/0000000000000000.olean").exists(), "an output outside the build was packed")

    archive.write_bytes(archive.read_bytes()[:-8])
    r = run("unpack", pkg, archive, "--cache", root / "cut")
    check(r.returncode != 0 and not (root / "cut").exists(), "a cut archive was unpacked")

    bad = io.BytesIO()
    with tarfile.open(fileobj=bad, mode="w") as tar:
        info = tarfile.TarInfo(f"outputs/../{DEP}.json")
        info.size = 2
        tar.addfile(info, io.BytesIO(b"{}"))
    archive.write_bytes(subprocess.run(["zstd", "-q", "-c"], input=bad.getvalue(), capture_output=True).stdout)
    r = run("unpack", pkg, archive, "--cache", root / "bad")
    check(r.returncode != 0 and not (root / "bad").exists(), "a member outside the cache's layout was unpacked")

    trace["inputs"][0][1].append(["-Ddebug.skipKernelTC=true", "2"])
    write(pkg / ".lake/build/lib/lean/B.trace", json.dumps(trace))
    r = run("pack", pkg, root / "b.tar.zst", "--cache", cache)
    check(r.returncode != 0 and "without the kernel" in r.stderr and not (root / "b.tar.zst").exists(),
          "a trace built without the kernel was packed")


if __name__ == "__main__":
    main()
