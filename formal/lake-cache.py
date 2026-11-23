"""Lake's artifact cache, filled from CI's builds of `main`, and bound to its sources by SHA-256.

  python3 -I lake-cache.py get [DIR] [--cache CACHE]
  python3 -I lake-cache.py pack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py unpack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py check DIR [--cache CACHE]
  python3 -I lake-cache.py digest

Lake's artifact cache (`lake env printenv LAKE_CACHE_DIR`) holds every output by content hash (`artifacts/`) and,
per package, a map from a target's input hash, its trace's `depHash`, to its outputs (`outputs/<package>/<hash>.json`).
Lake's hashes are 64 bits and not collision resistant, so an archive also carries `manifest.json`: the SHA-256 of
each local module's source under its `depHash`, and of each output under its name.

`pack` writes the entries of every target the workspace of DIR (a project: `lean_vm`) built or restored, read from the
traces in its packages' build directories (of Mathlib's packages only the compiled objects, as `lake exe cache get`
provides the rest), and the manifest. It refuses any trace that mentions `skipKernelTC`. `unpack` reads the whole
archive and checks every member's name before it installs anything; it installs each file whole under its name, never
replacing one, and keeps the manifest under `manifests/`. `check`, after a build, fails unless every local module
whose `depHash` a restored manifest names has that manifest's source, and every output Lake hashed (its `.hash` file)
to the name of a restored output has that output's content: a source or an output Lake confuses with another
fails here.

`get` unpacks the archive `lean.yml` published from the newest successful push or schedule run on `main`, named after
`digest`, the SHA-256 of the build tooling, lakefiles, manifests and toolchains. On any error it warns and restores
nothing: the build is then cold. Run `lake exe cache get` first: `get` asks Lake for its cache directory.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile
import tomllib
from pathlib import Path

FORMAL = Path(__file__).resolve().parent
REPO = "leanEthereum/leanVM"
WORKFLOW = ".github/workflows/lean.yml"
NAME = "lean-vm-lake-cache"
MANIFEST = "manifest.json"
MEMBER = re.compile(r"artifacts/[0-9a-f]{16}(\.\w+)*|outputs/[\w-]+/[0-9a-f]{16}\.json|manifest\.json")
NO_KERNEL = "skipKernelTC"


def log(message: str) -> None:
    print(f"lake-cache: {message}", file=sys.stderr, flush=True)


def sha256(path: Path) -> str:
    with path.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()


def digest() -> str:
    """What enters Lake's input hashes as text it never hashes as a file: tooling, lakefiles, manifests, toolchains."""
    files = sorted({FORMAL / "lake-build.py", FORMAL / "lake-cache.py",
                    *(f for pat in ("lakefile.*", "lake-manifest.json", "lean-toolchain")
                      for f in [*FORMAL.glob(pat), *FORMAL.glob(f"*/{pat}")])})
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


def packages(pkg: Path) -> list[tuple[Path, str]]:
    """Each package's directory, and its kind: `local` (this workspace and its path dependencies, whose sources the
    manifest binds), `mathlib` (what `lake exe cache get` provides) or `git` (pinned by the manifests in `digest`)."""
    manifest = json.loads((pkg / "lake-manifest.json").read_text(encoding="utf-8"))
    deps = pkg / manifest.get("packagesDir", ".lake/packages")
    sub = deps / "mathlib" / "lake-manifest.json"
    mathlib = {"mathlib"} | ({p["name"] for p in json.loads(sub.read_text(encoding="utf-8"))["packages"]}
                             if sub.is_file() else set())
    out = [(pkg, "local")]
    for p in manifest["packages"]:
        if p["type"] == "path":
            out.append(((pkg / p["dir"]).resolve(), "local"))
        else:
            out.append((deps / p["name"], "mathlib" if p["name"] in mathlib else "git"))
    return out


@functools.cache
def src_dirs(pkg: Path) -> frozenset[str]:
    config = tomllib.loads((pkg / "lakefile.toml").read_text(encoding="utf-8"))
    return frozenset({"."} | {t.get("srcDir", ".") for kind in ("lean_lib", "lean_exe") for t in config.get(kind, [])})


def source(pkg: Path, trace: Path) -> Path | None:
    """The source of the module whose trace is `trace` in package `pkg`, if exactly one of its source directories has it."""
    rel = trace.relative_to(pkg / ".lake" / "build" / "lib" / "lean").with_suffix(".lean")
    found = [pkg / d / rel for d in src_dirs(pkg) if (pkg / d / rel).is_file()]
    return found[0] if len(found) == 1 else None


def module_traces(pkg: Path):
    for root, kind in packages(pkg):
        if kind == "local":
            for trace in (root / ".lake" / "build" / "lib" / "lean").rglob("*.trace"):
                yield root, trace


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
    if not (cache / "outputs").is_dir():
        sys.exit(f"lake-cache: {cache} has no outputs: was LAKE_ARTIFACT_CACHE on?")
    scopes = [d for d in (cache / "outputs").iterdir() if d.is_dir()]
    unbound = {trace: root for root, trace in module_traces(pkg)}
    maps, arts, modules, unmapped = set(), set(), {}, 0
    for root, kind in packages(pkg):
        build = root / ".lake" / "build"
        for trace in (build / "ir" if kind == "mathlib" else build).rglob("*.trace"):
            data = load(trace)
            if any(NO_KERNEL in t for t in strings(data)):
                sys.exit(f"lake-cache: {trace} was built without the kernel: nothing packed")
            dep = data.get("depHash")
            found = [m for s in scopes if isinstance(dep, str) and (m := s / f"{dep}.json").is_file() and load(m)]
            if found and trace in unbound:  # a local module: bound to its source, or left out
                src = source(unbound[trace], trace)
                if src is None:
                    found = []
                else:
                    modules[dep] = sha256(src)
            unmapped += not found
            for mapping in found:
                maps.add(mapping.relative_to(cache).as_posix())
                arts.update(a for a in strings(load(mapping)) if (cache / "artifacts" / a).is_file())
    if not maps:
        sys.exit(f"lake-cache: no entry of {cache} is in {pkg}'s build: was LAKE_ARTIFACT_CACHE on?")
    manifest = json.dumps({"digest": digest(), "modules": modules,
                           "artifacts": {a: sha256(cache / "artifacts" / a) for a in sorted(arts)}}).encode()
    zstd = subprocess.Popen(["zstd", "-T0", "-3", "-q", "-f", "-o", str(archive)], stdin=subprocess.PIPE)
    with tarfile.open(fileobj=zstd.stdin, mode="w|") as tar:
        info = tarfile.TarInfo(MANIFEST)
        info.size = len(manifest)
        tar.addfile(info, io.BytesIO(manifest))
        for name in sorted(f"artifacts/{a}" for a in arts) + sorted(maps):  # outputs before the maps that name them
            tar.add(cache / name, arcname=name)
    zstd.stdin.close()
    if zstd.wait():
        sys.exit("lake-cache: zstd failed")
    log(f"{len(maps)} targets ({len(modules)} local modules bound), {len(arts)} outputs, "
        f"{archive.stat().st_size / 2**30:.1f} GB packed; {unmapped} traces without an entry")


def members(archive: Path):
    zstd = subprocess.Popen(["zstd", "-dcq", str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=zstd.stdout, mode="r|") as tar:
            for member in tar:
                yield tar, member
    finally:
        zstd.stdout.close()
        zstd.wait()


def unpack(archive: Path, cache: Path) -> None:
    if subprocess.run(["zstd", "-tq", str(archive)], check=False).returncode:
        sys.exit(f"lake-cache: {archive} fails zstd's checksum: nothing unpacked")
    names = [m.name for _, m in members(archive) if not m.isdir()]
    bad = [n for _, m in members(archive) if not m.isdir() and not (m.isfile() and MEMBER.fullmatch(n := m.name))]
    if bad or names.count(MANIFEST) != 1:
        sys.exit(f"lake-cache: {archive} holds {bad[:3] or 'no single manifest'}: nothing unpacked")
    added = kept = 0
    for tar, member in members(archive):
        if member.isdir():
            continue
        data = tar.extractfile(member)
        if member.name == MANIFEST:
            content = data.read()
            path = cache / "manifests" / f"{hashlib.sha256(content).hexdigest()[:16]}.json"
            data = io.BytesIO(content)
        else:
            path = cache / member.name
        if path.exists():
            kept += 1
            continue
        path.parent.mkdir(parents=True, exist_ok=True)
        tmp = tempfile.NamedTemporaryFile(dir=path.parent, delete=False)
        try:
            with tmp:
                while chunk := data.read(1 << 20):
                    tmp.write(chunk)
            os.chmod(tmp.name, 0o555 if member.mode & 0o111 else 0o444)  # read-only, as Lake leaves its own
            os.replace(tmp.name, path)
        finally:
            if os.path.exists(tmp.name):
                os.unlink(tmp.name)
        added += 1
    log(f"{added} files added to {cache}, {kept} already there")


def check(pkg: Path, cache: Path) -> None:
    modules: dict[str, str] = {}
    outputs: dict[str, dict[str, str]] = {}
    for path in sorted((cache / "manifests").glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            for dep, sha in data["modules"].items():
                if modules.setdefault(dep, sha) != sha:
                    sys.exit(f"lake-cache: two restored manifests bind {dep} to different sources")
            for name, sha in data["artifacts"].items():
                outputs.setdefault(name.split(".")[0], {})[name] = sha
        except (OSError, ValueError, KeyError, AttributeError) as e:
            sys.exit(f"lake-cache: restored manifest {path} is unreadable: {e}")
    failed = []
    for root, trace in module_traces(pkg):
        dep = load(trace).get("depHash")
        if dep in modules:
            src = source(root, trace)
            if src is None or sha256(src) != modules[dep]:
                failed.append(f"{trace}: its source is not the one its cache entry was built from")
    for root, _ in packages(pkg):
        for marker in (root / ".lake" / "build").rglob("*.hash"):
            out = marker.with_suffix("")
            named = outputs.get(marker.read_text(encoding="utf-8").strip())
            if not named or not out.is_file():
                continue
            ino = (out.stat().st_dev, out.stat().st_ino)
            restored = any((a := cache / "artifacts" / n).is_file() and (a.stat().st_dev, a.stat().st_ino) == ino
                           for n in named)  # a hard link to the restored output itself
            if not restored and sha256(out) not in named.values():
                failed.append(f"{out}: Lake took it for a restored output with other content")
    if failed:
        sys.exit("lake-cache: check failed:\n  " + "\n  ".join(failed))
    log(f"{len(modules)} restored local modules and {sum(map(len, outputs.values()))} outputs bound: ok")


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=True).stdout


def get(pkg: Path, cache: Path | None) -> None:
    name = f"{NAME}-{digest()}"
    try:
        runs = sorted((r for event in ("push", "schedule") for r in json.loads(gh(
            "api", f"repos/{REPO}/actions/workflows/{Path(WORKFLOW).name}/runs"
                   f"?event={event}&branch=main&status=success&per_page=50"))["workflow_runs"]),
            key=lambda r: r["created_at"], reverse=True)
    except (subprocess.CalledProcessError, KeyError, ValueError) as e:
        runs = []
        log(f"cannot list main's runs: {e}")
    for run in runs:
        try:
            # `head_branch` alone could be a tag named `main`: the commit must be on the branch.
            if not (run["event"] in ("push", "schedule") and run["head_branch"] == "main"
                    and run["conclusion"] == "success"
                    and any(not a["expired"] and a["name"] == name for a in json.loads(gh(
                        "api", f"repos/{REPO}/actions/runs/{run['id']}/artifacts?name={name}"))["artifacts"])
                    and json.loads(gh("api", f"repos/{REPO}/compare/{run['head_sha']}...refs/heads/main"))[
                        "status"] in ("identical", "ahead")):
                continue
            with tempfile.TemporaryDirectory() as tmp:
                gh("run", "download", str(run["id"]), "-R", REPO, "-n", name, "-D", tmp)
                log(f"{name} from run {run['id']} ({run['event']} of main at {run['head_sha'][:10]})")
                unpack(Path(tmp) / f"{NAME}.tar.zst", cache or cache_dir(pkg))
            return
        except (subprocess.CalledProcessError, KeyError, ValueError, SystemExit) as e:
            log(f"run {run.get('id')}: {e}: skipped")
    log(f"no successful run of main has {name}: nothing restored")
    if os.environ.get("GITHUB_ACTIONS"):
        print(f"::warning::no Lake cache {name} restored: a cold build", flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    sub.add_parser("digest")
    for cmd in ("get", "pack", "unpack", "check"):
        p = sub.add_parser(cmd)
        p.add_argument("dir", type=Path, **({"nargs": "?", "default": FORMAL / "lean_vm"} if cmd == "get" else {}))
        if cmd in ("pack", "unpack"):
            p.add_argument("archive", type=Path)
        p.add_argument("--cache", type=Path, help="the cache directory (default: Lake's for DIR)")
    opts = parser.parse_args()
    if opts.cmd == "digest":
        print(digest())
        return
    pkg = opts.dir.resolve()
    if opts.cmd == "get":
        get(pkg, opts.cache.resolve() if opts.cache else None)
        return
    cache = opts.cache.resolve() if opts.cache else cache_dir(pkg)
    if opts.cmd == "pack":
        pack(pkg, opts.archive.resolve(), cache)
    elif opts.cmd == "unpack":
        unpack(opts.archive.resolve(), cache)
    else:
        check(pkg, cache)


if __name__ == "__main__":
    main()
