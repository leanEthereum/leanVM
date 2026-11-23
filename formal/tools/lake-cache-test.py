"""`lake-cache.py` on fixtures and through Lake: what it packs, refuses, installs, lets Lake restore and catches.

  python3 -I tools/lake-cache-test.py        (needs `lake`, with the toolchain of `formal/lean-toolchain`, and zstd)

The cases that need two modules with one input hash plant an archive's entry under a second input hash, with its
binding, as a collision of Lake's hash would; nothing here computes a collision.
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
    write(pkg / "lean-toolchain", (FORMAL / "lean-toolchain").read_text())
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
    check((other / f"artifacts/{ART}").read_text() == "olean" and len(list((other / "manifests").glob("*.json"))) == 1,
          "the build's entry was not carried")
    check((other / f"held/pkg/{DEP}.json").is_file() and not (other / "outputs").exists(),
          "a local module's entry was installed where Lake reads it")
    check(not (other / "artifacts/0000000000000000.olean").exists(), "an output outside the build was packed")
    write(root / "kept" / f"artifacts/{ART}", "another olean")
    r = run("unpack", pkg, archive, "--cache", root / "kept")
    check(r.returncode != 0, "an output already in the cache with other content was kept")

    archive.write_bytes(archive.read_bytes()[:-8])
    r = run("unpack", pkg, archive, "--cache", root / "cut")
    check(r.returncode != 0 and not (root / "cut").exists(), "a cut archive was unpacked")
    for bad in ({"manifest.json": b"{}", f"outputs/../{DEP}.json": b"{}"}, {f"artifacts/{ART}": b"x"},
                {f"artifacts/{ART}": b"x", "manifest.json": b"{}"}, {"manifest.json": b"{}", "artifacts/x": None}):
        if None in bad.values():  # a member that is not a file
            raw = io.BytesIO()
            with tarfile.open(fileobj=raw, mode="w") as tar:
                tar.addfile(tarfile.TarInfo("manifest.json"), io.BytesIO(b""))
                info = tarfile.TarInfo("artifacts/x")
                info.type = tarfile.SYMTYPE
                tar.addfile(info)
            archive.write_bytes(subprocess.run(["zstd", "-q", "-c"], input=raw.getvalue(), capture_output=True).stdout)
        else:
            archive_of(archive, bad)
        r = run("unpack", pkg, archive, "--cache", root / "bad")
        check(r.returncode != 0 and "Traceback" not in r.stderr and not (root / "bad").exists(),
              f"an archive outside the layout was unpacked: {list(bad)}: {r.stderr}")

    write(pkg / ".lake/build/lib/lean/B.trace", json.dumps(trace))
    r = run("check", pkg, "--cache", other)
    check(r.returncode != 0 and "share an input hash" in r.stderr, "two modules with one input hash passed the check")
    trace["inputs"][0][1].append(["-Ddebug.skipKernelTC=true", "2"])
    write(pkg / ".lake/build/lib/lean/B.trace", json.dumps(trace | {"depHash": "1" * 16}))
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
    good = dict(head_branch="main", compare="ahead", artifact=name, expired=False)
    cases = [dict(good, head_branch="feature"), dict(good, compare="diverged"), dict(good, compare="behind"),
             dict(good, expired=True), dict(good, artifact=None), dict(good, artifact="lean-vm-lake-cache-0000000000000000"),
             good]
    fake = root / "gh"
    runs, artifacts, compare = [], {}, {}
    for i, c in enumerate(cases):
        rid, sha = str(100 + i), f"{i:040x}"
        runs.append({"id": rid, "event": "push", "head_branch": c["head_branch"], "head_sha": sha,
                     "created_at": f"2026-01-01T00:00:{59 - i:02d}Z"})
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


def lake(ws: Path, cache: Path, *args: str) -> subprocess.CompletedProcess:
    env = {**os.environ, "LAKE_ARTIFACT_CACHE": "true", "LAKE_RESTORE_ARTIFACTS": "true", "LAKE_CACHE_DIR": str(cache)}
    return subprocess.run(["lake", *args], cwd=ws, env=env, capture_output=True, text=True)


def built(ws: Path, cache: Path) -> str:
    r = lake(ws, cache, "build")
    check(r.returncode == 0, f"lake build failed in {ws}:\n{r.stdout}{r.stderr}")
    return r.stdout + r.stderr


def plant(ws: Path, cache: Path, module: str, old: str) -> None:
    """The archive's entry and binding for `module` at input hash `old`, also under its present input hash."""
    new = lake(ws, cache, "query", f"+{module}:depHash").stdout.strip().splitlines()[-1]
    src = next(p for d in ("held", "outputs") if (p := cache / d / f"toy/{old}.json").exists())
    shutil.copy(src, cache / f"held/toy/{new}.json")
    (manifest,) = (cache / "manifests").glob("*.json")
    data = json.loads(manifest.read_text())
    data["modules"][f"toy/{new}"] = data["modules"][f"toy/{old}"]
    manifest.chmod(0o644)
    manifest.write_text(json.dumps(data))


def workspace(root: Path, files: dict[str, str]) -> Path:
    for rel, text in {"lakefile.toml": 'name = "toy"\ndefaultTargets = ["Toy"]\n\n[[lean_lib]]\nname = "Toy"\n',
                      "lean-toolchain": (FORMAL / "lean-toolchain").read_text(), **files}.items():
        write(root / rel, text)
    return root


def restored_copy(root: Path, ws: Path) -> tuple[Path, Path]:
    built(ws, root / "cache")
    r = run("pack", ws, root / "a.tar.zst", "--cache", root / "cache")
    check(r.returncode == 0, f"pack failed: {r.stderr}")
    copy, other = root / "b", root / "other"
    shutil.copytree(ws, copy, ignore=shutil.ignore_patterns(".lake"))
    r = run("unpack", copy, root / "a.tar.zst", "--cache", other)
    check(r.returncode == 0, f"unpack failed: {r.stderr}")
    return copy, other


def round_trip(root: Path) -> None:
    """Restored for a copy at another path: Lake rebuilds nothing, and the check passes. An import edited under an
    unchanged module whose entry answers its new input hash: the filter holds the entry, so Lake rebuilds the module
    (and its false theorem fails); with the entry put where Lake reads it, the build is green, and the check and
    `pack` fail."""
    ws = workspace(root / "a", {"Toy/A.lean": "def a : Nat := 41\n", "Toy.lean": "import Toy.B\n",
                                "Toy/B.lean": "import Toy.A\ntheorem b : a + 1 = 42 := by decide\n"})
    copy, other = restored_copy(root, ws)
    check(run("filter", copy, "--cache", other).returncode == 0, "filter failed")
    check("Built" not in built(copy, other), "Lake rebuilt what the cache held")
    r = run("check", copy, "--cache", other)
    check(r.returncode == 0, f"the check failed on an unchanged workspace: {r.stderr}")

    old = json.loads((copy / ".lake/build/lib/lean/Toy/B.trace").read_text())["depHash"]
    (copy / "Toy/A.lean").write_text("def a : Nat := 0\n")
    plant(copy, other, "Toy.B", old)
    check(run("filter", copy, "--cache", other).returncode == 0, "filter failed")
    r = lake(copy, other, "build")
    check(r.returncode != 0 and "Toy.B" in r.stdout + r.stderr, "Lake restored an entry whose import changed")

    for held in (other / "held/toy").glob("*.json"):
        os.replace(held, other / "outputs/toy" / held.name)
    built(copy, other)
    r = run("check", copy, "--cache", other)
    check(r.returncode != 0 and "Toy/B.trace" in r.stderr, "a module restored for a changed import passed the check")
    r = run("pack", copy, root / "c.tar.zst", "--cache", other)
    check(r.returncode != 0 and not (root / "c.tar.zst").exists(), "pack bound a module restored for a changed import")

    write(ws / "lakefile.toml", (ws / "lakefile.toml").read_text() + 'moreLeanArgs = ["-Ddebug.skipKernelTC=true"]\n')
    built(ws, root / "cache")
    r = run("pack", ws, root / "dev.tar.zst", "--cache", root / "cache")
    check(r.returncode != 0 and "without the kernel" in r.stderr, "a build through moreLeanArgs without the kernel was packed")


def private_edit(root: Path) -> None:
    """A proof edited behind the module system leaves its importer's input hash alone; the filter holds the importer's
    entry anyway (its source closure changed), so Lake rebuilds it, and the check passes: savings lost, no false
    failure."""
    ws = workspace(root / "a", {
        "Toy/I.lean": "module\n\npublic def i : Nat := 1\npublic theorem i_pos : 0 < i := by decide\n",
        "Toy/M.lean": "module\n\npublic import Toy.I\n\npublic theorem m : 0 < i + 1 := Nat.succ_pos _\n",
        "Toy.lean": "module\n\npublic import Toy.M\n"})
    copy, other = restored_copy(root, ws)
    old = json.loads((ws / ".lake/build/lib/lean/Toy/M.trace").read_text())["depHash"]
    (copy / "Toy/I.lean").write_text("module\n\npublic def i : Nat := 1\npublic theorem i_pos : 0 < i := Nat.one_pos\n")
    check(lake(copy, other, "query", "+Toy.M:depHash").stdout.strip().splitlines()[-1] == old,
          "the private edit changed the importer's input hash: the case tests nothing")
    check(run("filter", copy, "--cache", other).returncode == 0, "filter failed")
    out = built(copy, other)
    check("Built Toy.M" in out, f"Lake restored an importer whose import's source changed:\n{out}")
    r = run("check", copy, "--cache", other)
    check(r.returncode == 0, f"the check failed after an honest private edit: {r.stderr}")


def main() -> None:
    for case in (fixture, trust, round_trip, private_edit):
        with tempfile.TemporaryDirectory() as tmp:
            case(Path(tmp))
    print("lake-cache-test: ok")


if __name__ == "__main__":
    main()
