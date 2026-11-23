"""Lake's artifact cache, filled from CI's builds of `main`.

  python3 -I lake-cache.py get [DIR]
  python3 -I lake-cache.py pack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py unpack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py digest

Lake's artifact cache (`lake env printenv LAKE_CACHE_DIR`) holds every output by content hash (`artifacts/`) and,
per package, a map from a target's input hash, its trace's `depHash`, to its outputs (`outputs/<package>/<hash>.json`).

`pack` writes the entries of every target the workspace of DIR (a project: `lean_vm`) built or restored, read from the
traces in its packages' build directories: of Mathlib's packages only the compiled objects, as `lake exe cache get`
provides the rest. It refuses any trace that mentions `skipKernelTC`. `unpack` tests the whole archive, then adds its
entries to the cache, each file written whole before it gets its name, never replacing one there.

`get` unpacks the archive `lean.yml` published from the newest successful push or schedule run on `main`, named after
`digest`, the hash of the build tooling and toolchains, which no input hash covers. On any error it warns and restores
nothing: the build is then cold. Run `lake exe cache get` first: `get` asks Lake for its cache directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parent
REPO = "leanEthereum/leanVM"
WORKFLOW = ".github/workflows/lean.yml"
NAME = "lean-vm-lake-cache"
MEMBER = re.compile(r"artifacts/[0-9a-f]{16}(\.\w+)*|outputs/[\w«»-]+/[0-9a-f]{16}\.json")
NO_KERNEL = "skipKernelTC"


def log(message: str) -> None:
    print(f"lake-cache: {message}", file=sys.stderr, flush=True)


def digest() -> str:
    """The build tooling and the toolchains, which no input hash covers."""
    files = [FORMAL / "lake-build.py", FORMAL / "lake-cache.py", *sorted(FORMAL.glob("lean-toolchain")),
             *sorted(FORMAL.glob("*/lean-toolchain"))]
    h = hashlib.sha256()
    for f in files:
        h.update(f.relative_to(FORMAL).as_posix().encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()[:16]


def cache_dir(pkg: Path) -> Path:
    out = subprocess.run(["lake", "env", "printenv", "LAKE_CACHE_DIR"], cwd=pkg, capture_output=True, text=True,
                         check=True).stdout.strip()
    if not out:
        sys.exit("lake-cache: Lake has no cache directory (LAKE_CACHE_DIR is set and empty)")
    return Path(out)


def build_dirs(pkg: Path) -> list[tuple[Path, bool]]:
    """Each package's build directory, and whether `lake exe cache get` provides its modules (Mathlib's)."""
    manifest = json.loads((pkg / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = pkg / manifest.get("packagesDir", ".lake/packages")
    sub = packages / "mathlib" / "lake-manifest.json"
    mathlib = {"mathlib"} | ({p["name"] for p in json.loads(sub.read_text(encoding="utf-8"))["packages"]}
                             if sub.is_file() else set())
    dirs = [(pkg / ".lake" / "build", False)]
    for p in manifest["packages"]:
        root = pkg / p["dir"] if p["type"] == "path" else packages / p["name"]
        dirs.append((root.resolve() / ".lake" / "build", p["name"] in mathlib))
    return dirs


def load(path: Path) -> dict:
    """A trace or a map; `{}` for one cut short (written by a build stopped at its deadline) or of another form."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def strings(value: object):
    if isinstance(value, str):
        yield value
    elif isinstance(value, (dict, list)):
        for v in value.values() if isinstance(value, dict) else value:
            yield from strings(v)


def pack(pkg: Path, archive: Path, cache: Path) -> None:
    scopes = [d for d in (cache / "outputs").iterdir() if d.is_dir()]
    maps, arts, unmapped = set(), set(), 0
    for build, from_mathlib in build_dirs(pkg):
        for trace in (build / "ir" if from_mathlib else build).rglob("*.trace"):
            data = load(trace)
            if any(NO_KERNEL in t for t in strings(data)):
                sys.exit(f"lake-cache: {trace} was built without the kernel: nothing packed")
            dep = data.get("depHash")
            found = [m for s in scopes if isinstance(dep, str) and (m := s / f"{dep}.json").is_file() and load(m)]
            unmapped += not found
            for mapping in found:
                maps.add(mapping.relative_to(cache).as_posix())
                arts.update(a for a in strings(load(mapping)) if (cache / "artifacts" / a).is_file())
    if not maps:
        sys.exit(f"lake-cache: no entry of {cache} is in {pkg}'s build: was LAKE_ARTIFACT_CACHE on?")
    names = sorted(f"artifacts/{a}" for a in arts) + sorted(maps)  # each output before the maps that name it
    with tempfile.NamedTemporaryFile("w", encoding="utf-8") as listing:
        listing.write("\0".join(names) + "\0")
        listing.flush()
        tar = subprocess.Popen(["tar", "-cf", "-", "-C", str(cache), "--null", "-T", listing.name], stdout=subprocess.PIPE)
        zstd = subprocess.Popen(["zstd", "-T0", "-3", "-q", "-f", "-o", str(archive)], stdin=tar.stdout)
        tar.stdout.close()
        if zstd.wait() or tar.wait():
            sys.exit("lake-cache: tar or zstd failed")
    log(f"{len(maps)} targets, {len(arts)} outputs, {archive.stat().st_size / 2**30:.1f} GB packed; "
        f"{unmapped} traces without an entry")


def unpack(archive: Path, cache: Path) -> None:
    if subprocess.run(["zstd", "-tq", str(archive)], check=False).returncode:
        sys.exit(f"lake-cache: {archive} fails zstd's checksum: nothing unpacked")
    added = kept = 0
    zstd = subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE)
    with tarfile.open(fileobj=zstd.stdout, mode="r|") as tar:
        for member in tar:
            if member.isdir():
                continue
            if not (member.isfile() and MEMBER.fullmatch(member.name)):
                sys.exit(f"lake-cache: {archive} holds {member.name!r}, not a cache entry")
            path = cache / member.name
            if path.exists():
                kept += 1
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            src = tar.extractfile(member)
            with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as tmp:
                while chunk := src.read(1 << 20):
                    tmp.write(chunk)
            os.chmod(tmp.name, 0o555 if member.mode & 0o111 else 0o444)  # read-only, as Lake leaves its own
            os.replace(tmp.name, path)
            added += 1
    if zstd.wait():
        sys.exit(f"lake-cache: {archive} is not a whole zstd archive")
    log(f"{added} files added to {cache}, {kept} already there")


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=True).stdout


def get(pkg: Path) -> None:
    name = f"{NAME}-{digest()}"
    try:
        runs = sorted((r for event in ("push", "schedule") for r in json.loads(gh(
            "api", f"repos/{REPO}/actions/workflows/{Path(WORKFLOW).name}/runs"
                   f"?event={event}&branch=main&status=success&per_page=50"))["workflow_runs"]),
            key=lambda r: r["created_at"], reverse=True)
    except (subprocess.CalledProcessError, KeyError, json.JSONDecodeError) as e:
        runs = []
        log(f"cannot list main's runs: {e}")
    for run in runs:
        try:
            # `head_branch` alone could be a tag named `main`: the commit must be on the branch.
            if not (run["event"] in ("push", "schedule") and run["head_branch"] == "main"
                    and run["conclusion"] == "success"
                    and any(not a["expired"] for a in json.loads(gh(
                        "api", f"repos/{REPO}/actions/runs/{run['id']}/artifacts?name={name}"))["artifacts"])
                    and json.loads(gh("api", f"repos/{REPO}/compare/{run['head_sha']}...refs/heads/main"))[
                        "status"] in ("identical", "ahead")):
                continue
            with tempfile.TemporaryDirectory() as tmp:
                gh("run", "download", str(run["id"]), "-R", REPO, "-n", name, "-D", tmp)
                log(f"{name} from run {run['id']} ({run['event']} of main at {run['head_sha'][:10]})")
                unpack(Path(tmp) / f"{NAME}.tar.zst", cache_dir(pkg))
            return
        except (subprocess.CalledProcessError, KeyError, json.JSONDecodeError, SystemExit) as e:
            log(f"run {run.get('id')}: {e}: skipped")
    log(f"no successful run of main has {name}: nothing restored")
    if os.environ.get("GITHUB_ACTIONS"):
        print(f"::warning::no Lake cache {name} restored: a cold build", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("get").add_argument("dir", nargs="?", type=Path, default=FORMAL / "lean_vm")
    sub.add_parser("digest")
    for cmd in ("pack", "unpack"):
        p = sub.add_parser(cmd)
        p.add_argument("dir", type=Path)
        p.add_argument("archive", type=Path)
        p.add_argument("--cache", type=Path, help="the cache directory (default: Lake's for DIR)")
    opts = parser.parse_args()
    if opts.cmd == "get":
        get(opts.dir.resolve())
    elif opts.cmd == "digest":
        print(digest())
    else:
        cache = opts.cache.resolve() if opts.cache else cache_dir(opts.dir.resolve())
        if opts.cmd == "pack":
            pack(opts.dir.resolve(), opts.archive.resolve(), cache)
        else:
            unpack(opts.archive.resolve(), cache)


if __name__ == "__main__":
    main()
