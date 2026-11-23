"""Lake's artifact cache, filled from CI's trusted builds.

  python3 -I lake-cache.py get [DIR] [--run ID | --tag TAG]
  python3 -I lake-cache.py pack DIR ARCHIVE
  python3 -I lake-cache.py unpack DIR ARCHIVE

Lake keeps what it builds in its artifact cache (`lake env printenv LAKE_CACHE_DIR`: `LAKE_CACHE_DIR`, or the
toolchain's directory): every output by its content's hash (`artifacts/`), and, per package, a map from a target's
input hash to its outputs (`outputs/<package>/<hash>.json`). The input hash is the one in the target's trace
(`depHash`): its source, its imports' outputs, its options and the toolchain. With `LAKE_ARTIFACT_CACHE` on
(`lake-build.py` turns it on outside CI; `lean.yml` turns it on), Lake restores a target whose input hash the cache
maps, and builds every other one.

`pack` writes the entries of every target the workspace of DIR (a project: `lean_vm`) built or restored, read from the
traces in its packages' build directories: of Mathlib's packages only the compiled objects, as `lake exe cache get`
provides the rest. It refuses a trace of a module built without the kernel (`debug.skipKernelTC`: `lake-build.py
--dev` builds into another directory, so none should be there). `unpack` adds an archive's entries to DIR's cache,
each file written whole before it gets its name, never replacing one there.

`get` unpacks the archive of a trusted run of `lean.yml`: by default the newest run on `main` that has one, or the run
`--run` names, or the release asset of `--tag`. `lean.yml` uploads an archive only from the events a writer starts (a
push to `main` or of a tag, the nightly schedule, a dispatch), never from a pull request, and `get` accepts no other
run's, so no pull request can put an entry into a build that `get` fills. Run `lake exe cache get` first: `get` asks
Lake for its cache directory, which loads the workspace.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

REPO = os.environ.get("GITHUB_REPOSITORY", "leanEthereum/leanVM")
WORKFLOW = ".github/workflows/lean.yml"
NAME = "lean-vm-lake-cache"  # the artifact, and the release assets' prefix
TRUSTED = ("push", "schedule", "workflow_dispatch")
MEMBER = re.compile(r"artifacts/[0-9a-f]{16}(\.[\w.]+)?|outputs/[^/]+/[0-9a-f]{16}\.json")


def log(message: str) -> None:
    print(f"lake-cache: {message}", file=sys.stderr, flush=True)


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


def pack(pkg: Path, archive: Path) -> None:
    cache = cache_dir(pkg)
    scopes = [d for d in (cache / "outputs").iterdir() if d.is_dir()]
    maps, arts, unmapped = set(), set(), 0
    for build, from_mathlib in build_dirs(pkg):
        traces = (build / "ir" if from_mathlib else build).rglob("*.trace")
        for trace in traces:
            text = trace.read_text(encoding="utf-8")
            if "skipKernelTC" in text:
                sys.exit(f"lake-cache: {trace} was built without the kernel: nothing packed")
            dep = json.loads(text)["depHash"]
            found = [s / f"{dep}.json" for s in scopes if (s / f"{dep}.json").is_file()]
            unmapped += not found
            for mapping in found:
                maps.add(mapping.relative_to(cache).as_posix())
                arts.update(a for a in strings(json.loads(mapping.read_text(encoding="utf-8")))
                            if (cache / "artifacts" / a).is_file())
    if not maps:
        sys.exit(f"lake-cache: no entry of {cache} is in {pkg}'s build: was LAKE_ARTIFACT_CACHE on?")
    names = sorted(f"artifacts/{a}" for a in arts) + sorted(maps)  # each output before the maps that name it
    size = sum((cache / n).stat().st_size for n in names)
    with tempfile.NamedTemporaryFile("w", encoding="utf-8") as listing:
        listing.write("\0".join(names) + "\0")
        listing.flush()
        tar = subprocess.Popen(["tar", "-cf", "-", "-C", str(cache), "--null", "-T", listing.name], stdout=subprocess.PIPE)
        subprocess.run(["zstd", "-T0", "-3", "-q", "-f", "-o", str(archive)], stdin=tar.stdout, check=True)
        if tar.wait():
            sys.exit("lake-cache: tar failed")
    log(f"{len(maps)} targets, {len(arts)} outputs ({size / 2**30:.1f} GB; {archive.stat().st_size / 2**30:.1f} GB "
        f"packed), from {cache}; {unmapped} traces without an entry")


def strings(value: object):
    if isinstance(value, str):
        yield value
    elif isinstance(value, dict):
        for v in value.values():
            yield from strings(v)
    elif isinstance(value, list):
        for v in value:
            yield from strings(v)


def unpack(pkg: Path, archive: Path) -> None:
    cache = cache_dir(pkg)
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


def trusted_run(run: dict) -> bool:
    return (run["event"] in TRUSTED and run["path"] == WORKFLOW
            and run["head_repository"]["full_name"] == run["repository"]["full_name"] == REPO)


def get(pkg: Path, run_id: str | None, tag: str | None) -> None:
    with tempfile.TemporaryDirectory() as tmp:
        if tag:
            gh("release", "download", tag, "-R", REPO, "-p", f"{NAME}.tar.zst.*", "-D", tmp)
            archive = Path(tmp) / f"{NAME}.tar.zst"
            with archive.open("wb") as out:
                for part in sorted(Path(tmp).glob(f"{NAME}.tar.zst.*")):
                    out.write(part.read_bytes())
                    part.unlink()
            source = f"release {tag}"
        else:
            if run_id:
                runs = [json.loads(gh("api", f"repos/{REPO}/actions/runs/{run_id}"))]
                if not trusted_run(runs[0]):
                    sys.exit(f"lake-cache: run {run_id} is a {runs[0]['event']} run: only {', '.join(TRUSTED)} runs "
                             f"of {REPO}'s {WORKFLOW} are trusted")
            else:
                listed = json.loads(gh("api", f"repos/{REPO}/actions/workflows/{Path(WORKFLOW).name}/runs"
                                              "?branch=main&per_page=50"))["workflow_runs"]
                runs = [r for r in listed if trusted_run(r) and r["head_branch"] == "main"]
            run = next((r for r in runs if any(not a["expired"] for a in json.loads(
                gh("api", f"repos/{REPO}/actions/runs/{r['id']}/artifacts?name={NAME}"))["artifacts"])), None)
            if run is None:
                log("no trusted run has an archive: nothing restored")
                return
            gh("run", "download", str(run["id"]), "-R", REPO, "-n", NAME, "-D", tmp)
            archive = Path(tmp) / f"{NAME}.tar.zst"
            source = f"run {run['id']} ({run['event']} of {run['head_branch']} at {run['head_sha'][:10]}, {run['created_at']})"
        log(f"from {source}")
        unpack(pkg, archive)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("get")
    p.add_argument("dir", nargs="?", type=Path, default=Path(__file__).resolve().parent / "lean_vm")
    source = p.add_mutually_exclusive_group()
    source.add_argument("--run", help="a run of lean.yml started by a push, the schedule or a dispatch")
    source.add_argument("--tag", help="a release whose assets hold an archive")
    for cmd in ("pack", "unpack"):
        p = sub.add_parser(cmd)
        p.add_argument("dir", type=Path)
        p.add_argument("archive", type=Path)
    opts = parser.parse_args()
    if opts.cmd == "get":
        get(opts.dir.resolve(), opts.run, opts.tag)
    elif opts.cmd == "pack":
        pack(opts.dir.resolve(), opts.archive.resolve())
    else:
        unpack(opts.dir.resolve(), opts.archive.resolve())


if __name__ == "__main__":
    main()
