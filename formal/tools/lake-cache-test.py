"""`lake-cache.py` on a fixture: what it packs, what it refuses, what it never installs.

  python3 -I tools/lake-cache-test.py
"""
import io
import json
import os
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent.parent / "lake-cache.py"
DEP, ART = "0123456789abcdef", "fedcba9876543210.olean"


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
