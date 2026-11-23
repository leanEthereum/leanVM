"""`lake-cache.py` on fixtures and through Lake: what it packs, refuses, never installs, restores and catches.

  python3 -I tools/lake-cache-test.py        (needs `lake`, with the toolchain of `formal/lean-toolchain`, and zstd)
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


def run(*args, env=None) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, "-I", str(SCRIPT), *map(str, args)], capture_output=True, text=True, env=env)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def check(ok: bool, what: str) -> None:
    if not ok:
        sys.exit(f"lake-cache-test: {what}")


def archive_of(path: Path, files: dict[str, bytes]) -> None:
    raw = io.BytesIO()
    with tarfile.open(fileobj=raw, mode="w") as tar:
        for name, data in files.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
    path.write_bytes(subprocess.run(["zstd", "-q", "-c"], input=raw.getvalue(), capture_output=True).stdout)


def fixture(root: Path) -> None:
    pkg, cache, other, archive = root / "pkg", root / "cache", root / "other", root / "a.tar.zst"
    write(pkg / "lake-manifest.json", json.dumps({"packagesDir": ".lake/packages", "packages": []}))
    write(pkg / "lakefile.toml", 'name = "pkg"\n')
    write(pkg / "A.lean", "def a := 1\n")
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
    check((other / f"artifacts/{ART}").read_text() == "olean" and (other / f"outputs/pkg/{DEP}.json").is_file()
          and len(list((other / "manifests").glob("*.json"))) == 1, "the build's entry was not carried")
    check(not (other / "artifacts/0000000000000000.olean").exists(), "an output outside the build was packed")

    # An output Lake hashed to a restored output's name, with other content.
    write(pkg / ".lake/build/lib/lean/B.olean", "another olean")
    write(pkg / ".lake/build/lib/lean/B.olean.hash", ART.split(".")[0])
    r = run("check", pkg, "--cache", other)
    check(r.returncode != 0 and "B.olean" in r.stderr, "an output with a restored output's hash passed the check")
    (pkg / ".lake/build/lib/lean/B.olean").write_text("olean")
    r = run("check", pkg, "--cache", other)
    check(r.returncode == 0, f"the check failed on the restored content: {r.stderr}")

    archive.write_bytes(archive.read_bytes()[:-8])
    r = run("unpack", pkg, archive, "--cache", root / "cut")
    check(r.returncode != 0 and not (root / "cut").exists(), "a cut archive was unpacked")
    archive_of(archive, {"manifest.json": b"{}", f"artifacts/{ART}": b"x", f"outputs/../{DEP}.json": b"{}"})
    r = run("unpack", pkg, archive, "--cache", root / "bad")
    check(r.returncode != 0 and not (root / "bad").exists(), "an archive with a member outside the layout was unpacked")
    archive_of(archive, {f"artifacts/{ART}": b"x"})
    r = run("unpack", pkg, archive, "--cache", root / "bare")
    check(r.returncode != 0 and not (root / "bare").exists(), "an archive without a manifest was unpacked")

    trace["inputs"][0][1].append(["-Ddebug.skipKernelTC=true", "2"])
    write(pkg / ".lake/build/lib/lean/B.trace", json.dumps(trace))
    r = run("pack", pkg, root / "b.tar.zst", "--cache", cache)
    check(r.returncode != 0 and "without the kernel" in r.stderr and not (root / "b.tar.zst").exists(),
          "a trace built without the kernel was packed")


FAKE_GH = r'''import json, os, shutil, sys
d, a = os.environ["FAKE_GH"], sys.argv[1:]
if a[0] == "run":  # run download ID -R REPO -n NAME -D DIR
    shutil.copy(os.path.join(d, a[2], a[a.index("-n") + 1]), os.path.join(a[a.index("-D") + 1], "lean-vm-lake-cache.tar.zst"))
elif "/compare/" in a[1]:
    print(json.dumps({"status": json.load(open(os.path.join(d, "compare.json")))[a[1].split("/compare/")[1].split("...")[0]]}))
elif "/artifacts" in a[1]:
    print(json.dumps({"artifacts": json.load(open(os.path.join(d, "artifacts.json"))).get(a[1].split("/")[-2], [])}))
else:
    print(json.dumps({"workflow_runs": json.load(open(os.path.join(d, "runs.json")))}))
'''


def trust(root: Path) -> None:
    """`get` takes the one run that passes every test, though newer runs each fail one."""
    name = "lean-vm-lake-cache-" + run("digest").stdout.strip()
    good = dict(event="push", head_branch="main", conclusion="success", compare="ahead", artifact=name, expired=False)
    cases = [dict(good, event="pull_request"), dict(good, head_branch="feature"), dict(good, conclusion="failure"),
             dict(good, compare="diverged"), dict(good, expired=True), dict(good, artifact=None),
             dict(good, artifact="lean-vm-lake-cache-0000000000000000"), good]
    fake = root / "gh"
    runs, artifacts, compare = [], {}, {}
    for i, c in enumerate(cases):
        rid, sha = str(100 + i), f"{i:040x}"
        runs.append({"id": rid, "event": c["event"], "head_branch": c["head_branch"], "conclusion": c["conclusion"],
                     "head_sha": sha, "created_at": f"2026-01-01T00:00:{59 - i:02d}Z"})
        compare[sha] = c["compare"]
        if c["artifact"]:
            artifacts[rid] = [{"name": c["artifact"], "expired": c["expired"]}]
            (fake / rid).mkdir(parents=True)
            archive_of(fake / rid / c["artifact"], {"manifest.json": b'{"modules": {}, "artifacts": {}}',
                                                    f"artifacts/{i:016x}.olean": b"x"})
    for f, v in (("runs.json", runs), ("artifacts.json", artifacts), ("compare.json", compare)):
        write(fake / f, json.dumps(v))
    write(fake / "bin/gh", f"#!{sys.executable}\n" + FAKE_GH)
    (fake / "bin/gh").chmod(0o755)
    env = {**os.environ, "FAKE_GH": str(fake), "PATH": f"{fake / 'bin'}:{os.environ['PATH']}"}
    env.pop("GITHUB_ACTIONS", None)
    r = run("get", root, "--cache", root / "cache", env=env)
    got = sorted(p.name for p in (root / "cache" / "artifacts").glob("*"))
    check(r.returncode == 0 and got == [f"{len(cases) - 1:016x}.olean"], f"get took {got}: {r.stderr}")


def lake(ws: Path, cache: Path, *args: str, ok: bool = True) -> str:
    env = {**os.environ, "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true", "LAKE_CACHE_DIR": str(cache)}
    r = subprocess.run(["lake", *args], cwd=ws, env=env, capture_output=True, text=True)
    check(r.returncode == 0 or not ok, f"lake {' '.join(args)} failed in {ws}:\n{r.stdout}{r.stderr}")
    return r.stdout + r.stderr


def round_trip(root: Path) -> None:
    """A two-module workspace built, packed, unpacked for a copy at another path: Lake rebuilds nothing and the check
    passes. A changed source that Lake restores anyway (its entry copied under the changed input hash, as if Lake's
    hash had collided) builds green and fails the check."""
    ws = root / "a"
    write(ws / "lakefile.toml", 'name = "toy"\ndefaultTargets = ["Toy"]\n\n[[lean_lib]]\nname = "Toy"\n')
    shutil.copy(FORMAL / "lean-toolchain", ws / "lean-toolchain")
    write(ws / "Toy/A.lean", "def a : Nat := 41\n")
    write(ws / "Toy/B.lean", "import Toy.A\ntheorem b : a + 1 = 42 := by decide\n")
    write(ws / "Toy.lean", "import Toy.B\n")
    lake(ws, root / "cache", "build")
    r = run("pack", ws, root / "a.tar.zst", "--cache", root / "cache")
    check(r.returncode == 0, f"pack failed: {r.stderr}")
    copy, other = root / "b", root / "other"
    shutil.copytree(ws, copy, ignore=shutil.ignore_patterns(".lake"))
    r = run("unpack", copy, root / "a.tar.zst", "--cache", other)
    check(r.returncode == 0, f"unpack failed: {r.stderr}")
    out = lake(copy, other, "build")
    check("Built" not in out, f"Lake rebuilt what the cache held:\n{out}")
    lake(copy, other, "build", "--no-build")
    r = run("check", copy, "--cache", other)
    check(r.returncode == 0, f"the check failed on an unchanged workspace: {r.stderr}")

    old = json.loads((copy / ".lake/build/lib/lean/Toy/B.trace").read_text())["depHash"]
    (copy / "Toy/B.lean").write_text("import Toy.A\ntheorem b : a + 1 = 43 := by decide\n")
    new = lake(copy, other, "query", "+Toy.B:depHash").strip().splitlines()[-1]
    shutil.copy(other / f"outputs/toy/{old}.json", other / f"outputs/toy/{new}.json")
    (manifest,) = (other / "manifests").glob("*.json")
    data = json.loads(manifest.read_text())
    data["modules"][new] = data["modules"][old]
    manifest.chmod(0o644)
    manifest.write_text(json.dumps(data))
    out = lake(copy, other, "build")
    check("Built Toy.B" not in out, f"the planted entry was not restored:\n{out}")
    r = run("check", copy, "--cache", other)
    check(r.returncode != 0 and "Toy/B.trace" in r.stderr, "a restored module whose source changed passed the check")

    write(ws / "lakefile.toml", (ws / "lakefile.toml").read_text() + 'moreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n')
    lake(ws, root / "cache", "build")
    r = run("pack", ws, root / "dev.tar.zst", "--cache", root / "cache")
    check(r.returncode != 0 and "without the kernel" in r.stderr, "a build through moreLeanArgs without the kernel was packed")


def main() -> None:
    for case in (fixture, trust, round_trip):
        with tempfile.TemporaryDirectory() as tmp:
            case(Path(tmp))
    print("lake-cache-test: ok")


if __name__ == "__main__":
    main()
