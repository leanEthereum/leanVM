"""Lake's artifact cache, filled from CI's builds of `main`, restored only where SHA-256 shows the same input.

  python3 -I lake-cache.py get [DIR] [--cache CACHE]
  python3 -I lake-cache.py pack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py unpack DIR ARCHIVE [--cache CACHE]
  python3 -I lake-cache.py filter DIR [--cache CACHE]
  python3 -I lake-cache.py check DIR [--cache CACHE]
  python3 -I lake-cache.py digest
  python3 -I lake-cache.py artifact-name

Lake's artifact cache (`lake env printenv LAKE_CACHE_DIR`) holds every output by content hash (`artifacts/`) and,
per package, a map from a target's input hash, its trace's `depHash`, to its outputs (`outputs/<package>/<hash>.json`).
Lake's hashes are 64 bits and not collision resistant, so this script does not let Lake restore a module of the
workspace's own packages (`local`: this project and its path dependencies) on that hash alone. Each local module has
a strong key: the SHA-256 of `digest`, its name, its source, and its local imports' strong keys (imports as Lean
parses them), so it covers the module's whole local input. The other packages are pinned by the manifests `digest`
covers.

`pack` runs `check`, then writes the entries of every target the workspace of DIR (a project: `lean_vm`) built or
restored: each local module's map bound in `manifest.json` to its name and strong key, every output's SHA-256, and
of the other packages every target (of Mathlib's only the compiled objects, as `lake exe cache get` provides the
rest). It leaves out the local packages' other targets (objects, executables, libraries) and any local module whose
build was stopped (an output missing from the build directory), whose local closure has a source newer than its
trace, or one of whose local imports it leaves out, and fails on a local module whose source it cannot find exactly
once, on an output in the store that is not the file Lake built under its name (the store keeps the first file
written under a name), or on a trace that mentions `skipKernelTC`. `unpack` refuses a manifest of another `digest`,
checks every member's name, and every output against the manifest's SHA-256 (a file already in the cache too),
before installing anything; it installs each file whole under its name, puts every map of a local package under
`held/`, where Lake does not read it, and keeps the manifest under `manifests/`, last. `filter` moves a held map
into `outputs/` (marking it under `active/`) only while its module's strong key in the workspace is the one bound to
it, and back otherwise. `check`, after a build, fails if a target restored from a marked map is not a local module
bound to its name and present strong key, or two traces of a local package share an input hash. `lake- build.py`
runs `filter` before and `check` after every build. No module may read a file at elaboration time, which no input
hash covers: `lean.yml`'s statement job greps for the usual spellings.

`get` unpacks the archive `lean.yml` published from the newest successful push or schedule run on branch `main` whose
commit is in `main`'s history, named after `digest`, the SHA-256 of what enters Lake's input hashes without being a
source: the build tooling, lakefiles, `lake-manifest.json` files and toolchains. On any error it warns and restores
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
ARTIFACT = re.compile(r"[0-9a-f]{16}(\.\w+)*")
MEMBER = re.compile(rf"artifacts/{ARTIFACT.pattern}|outputs/[\w-]+/[0-9a-f]{{16}}\.json|manifest\.json")
NO_KERNEL = "skipKernelTC"


def log(message: str) -> None:
    print(f"lake-cache: {message}", file=sys.stderr, flush=True)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def digest() -> str:
    files = sorted({FORMAL / "lake-build.py", FORMAL / "lake-cache.py",
                    *(f for pat in ("lakefile.*", "lake-manifest.json", "lean-toolchain")
                      for f in [*FORMAL.glob(pat), *FORMAL.glob(f"*/{pat}")])})
    return sha256(b"".join(f.relative_to(FORMAL).as_posix().encode() + b"\0" + f.read_bytes() + b"\0"
                           for f in files))


def artifact_name() -> str:
    """The archive's name, as `lean.yml` publishes it and `get` looks for it."""
    return f"{NAME}-{digest()[:16]}"


def cache_dir(pkg: Path) -> Path:
    out = subprocess.run(["lake", "env", "printenv", "LAKE_CACHE_DIR"], cwd=pkg, capture_output=True, text=True,
                         check=True).stdout.strip()
    if not out:
        sys.exit("lake-cache: Lake has no cache directory (LAKE_CACHE_DIR is set and empty)")
    return Path(out)


def packages(pkg: Path) -> list[tuple[Path, str]]:
    """Each package's directory and kind: `local`, `mathlib` (what `lake exe cache get` provides) or `git`."""
    manifest = json.loads((pkg / "lake-manifest.json").read_text(encoding="utf-8"))
    deps = pkg / manifest.get("packagesDir", ".lake/packages")
    sub = deps / "mathlib" / "lake-manifest.json"
    mathlib = {"mathlib"} | ({p["name"] for p in json.loads(sub.read_text(encoding="utf-8"))["packages"]}
                             if sub.is_file() else set())
    return [(pkg, "local")] + [((pkg / p["dir"]).resolve(), "local") if p["type"] == "path" else
                               (deps / p["name"], "mathlib" if p["name"] in mathlib else "git")
                               for p in manifest["packages"]]


@functools.cache
def config(pkg: Path) -> dict:
    return tomllib.loads((pkg / "lakefile.toml").read_text(encoding="utf-8"))


class Keys:
    """The strong keys of a workspace's local modules, as its sources stand now. A module whose source is not found
    exactly once in its packages' source directories, or whose imports Lean cannot parse, has none: its entry is never
    restored (closed failure)."""

    def __init__(self, pkg: Path):
        local = [root for root, kind in packages(pkg) if kind == "local"]
        if lean := [root for root in local if (root / "lakefile.lean").exists()]:
            sys.exit(f"lake-cache: {lean[0]} has a lakefile.lean: source directories are read from lakefile.toml only")
        self.dirs = [root / d for root in local for d in {"."} | {
            t.get("srcDir", ".") for k in ("lean_lib", "lean_exe") for t in config(root).get(k, [])}]
        self.pkg, self.prefix, self.keys, self.sources = pkg, [digest(), config(pkg)["name"]], {}, {}
        self.deps: dict[str, list[str] | None] = {}

    def source(self, module: str) -> Path | None:
        """The module's local source, if exactly one local source directory has it."""
        if module not in self.sources:
            rel = Path(*module.split(".")).with_suffix(".lean")
            found = {(d / rel).resolve() for d in self.dirs if (d / rel).is_file()}
            self.sources[module] = found.pop() if len(found) == 1 else None
        return self.sources[module]

    def imports(self, files: list[Path]) -> dict[Path, list[str] | None]:
        out = {}
        for i in range(0, len(files), 1000):
            batch = files[i:i + 1000]
            r = subprocess.run(["lean", "--deps-json", *map(str, batch)], cwd=self.pkg, capture_output=True, text=True)
            parsed = json.loads(r.stdout)["imports"] if r.returncode == 0 else [{}] * len(batch)
            for f, p in zip(batch, parsed):
                ok = "result" in p and not p.get("errors")
                out[f] = [imp["module"] for imp in p["result"]["imports"]] if ok else None
        return out

    def of(self, modules) -> dict[str, str | None]:
        todo, srcs, deps = set(modules), {}, self.deps
        while todo:
            for m in todo:
                srcs[m] = self.source(m)
            files = [s for m in todo if (s := srcs[m]) is not None]
            parsed = self.imports(files)
            for m in todo:
                deps[m] = parsed.get(srcs[m]) if srcs[m] else None
            todo = {i for m in todo for i in deps[m] or [] if i not in srcs and self.source(i)}
        for m in srcs:
            self.key(m, srcs, deps)
        return {m: self.keys[m] for m in modules}

    def key(self, m: str, srcs: dict, deps: dict) -> str | None:
        if m not in self.keys:
            if srcs[m] is None or deps[m] is None:
                self.keys[m] = None
            else:
                local = sorted(i for i in set(deps[m]) if srcs.get(i))
                subs = [self.key(i, srcs, deps) for i in local]
                self.keys[m] = None if None in subs else sha256(json.dumps(
                    [*self.prefix, m, sha256(srcs[m].read_bytes()), list(zip(local, subs)),
                     sorted(set(deps[m]) - set(local))]).encode())
        return self.keys[m]


def module_name(root: Path, trace: Path) -> str:
    return ".".join(trace.relative_to(root / ".lake/build/lib/lean").with_suffix("").parts)


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


def bindings(cache: Path) -> dict[str, tuple[str, str] | None]:
    """`scope/depHash` to (module, strong key) over the restored manifests of this tooling (`digest`); `None` where two
    disagree. `filter` holds every marked map they do not bind."""
    out: dict[str, tuple[str, str] | None] = {}
    current = digest()
    for path in sorted((cache / "manifests").glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
            if data["digest"] != current:
                continue
            for ref, b in data["modules"].items():
                b = (b["module"], b["key"])
                out[ref] = b if out.get(ref, b) == b else None
        except (OSError, ValueError, KeyError, TypeError) as e:
            sys.exit(f"lake-cache: restored manifest {path} is unreadable: {e}")
    return out


def check(pkg: Path, cache: Path) -> None:
    bound = bindings(cache)
    restored, failed = {}, []
    for root in (root for root, kind in packages(pkg) if kind == "local"):
        scope, seen, build = config(root)["name"], {}, root / ".lake" / "build"
        for trace in build.rglob("*.trace"):
            data = load(trace)
            if not isinstance(dep := data.get("depHash"), str):
                continue
            if dep in seen:  # within a run, Lake would restore one's outputs as the other's
                failed.append(f"{trace} and {seen[dep]} share an input hash")
            seen[dep] = trace
            ref = f"{scope}/{dep}"
            if data.get("synthetic") and (cache / "active" / ref).exists():  # restored from an archive's map
                if not trace.is_relative_to(build / "lib" / "lean"):
                    failed.append(f"{trace}: restored from an archive, which binds only modules")
                else:
                    restored[trace] = (module_name(root, trace), bound.get(ref))
    keys = Keys(pkg).of({m for m, _ in restored.values()})
    for trace, (m, b) in restored.items():
        if b != (m, keys[m]):
            failed.append(f"{trace}: restored, but not bound to {m} as its sources stand")
    if failed:
        sys.exit("lake-cache: check failed:\n  " + "\n  ".join(failed))
    log(f"{len(restored)} modules restored from archives, bound to their sources: ok")


def filter_maps(pkg: Path, cache: Path) -> None:
    """An archive's map goes where Lake reads it, marked under `active/`, while its binding matches the module's
    present strong key, and back under `held/` otherwise. A map Lake wrote here itself is never marked or moved."""
    bound = bindings(cache)
    marks = {m.relative_to(cache / "active").as_posix() for m in (cache / "active").rglob("*") if m.is_file()}
    keys = Keys(pkg).of({b[0] for b in bound.values() if b})
    active = 0
    for ref in set(bound) | marks:
        b, mark = bound.get(ref), cache / "active" / ref
        held, live = cache / "held" / f"{ref}.json", cache / "outputs" / f"{ref}.json"
        if b and keys[b[0]] == b[1]:
            if held.exists() and not live.exists():  # marked first: a move cut short is redone next time
                mark.parent.mkdir(parents=True, exist_ok=True)
                mark.touch()
                live.parent.mkdir(parents=True, exist_ok=True)
                os.replace(held, live)
            active += mark.exists()
        elif mark.exists():
            if live.exists():
                if held.exists():
                    live.unlink()
                else:
                    held.parent.mkdir(parents=True, exist_ok=True)
                    os.replace(live, held)
            mark.unlink()
    log(f"{active} of {len(bound)} archived modules' maps match their sources")


def built_as(build: Path, module: str, artifact: str, cache: Path) -> bool:
    """Whether the build directory holds the file Lake built under `artifact` for `module`: `False` if it is missing
    (a build stopped before it wrote it), and failure if it differs (the store keeps the first file written under a
    name) or is an `.ltar`, which `check` would not see restored."""
    rel, ext = Path(*module.split(".")), artifact.partition(".")[2]
    built = build / ("ir" if ext in ("c", "bc") else "lib/lean") / f"{rel}.{ext}"
    stored = cache / "artifacts" / artifact
    if ext == "ltar" or built.is_file() and sha256(built.read_bytes()) != sha256(stored.read_bytes()):
        sys.exit(f"lake-cache: {artifact}, which the entry of {module} names, is not {built}: nothing packed")
    return built.is_file()


def pack(pkg: Path, archive: Path, cache: Path) -> None:
    check(pkg, cache)
    keys = Keys(pkg)
    maps, arts, local_maps, local_entries = set(), set(), {}, {}
    local_scopes = {config(root)["name"] for root, kind in packages(pkg) if kind == "local"}
    for root, kind in packages(pkg):
        build = root / ".lake" / "build"
        scope = config(root)["name"] if kind == "local" else root.name
        for trace in (build / {"local": "lib/lean", "mathlib": "ir"}.get(kind, "")).rglob("*.trace"):
            data = load(trace)
            if any(NO_KERNEL in t for t in strings(data)):
                sys.exit(f"lake-cache: {trace} was built without the kernel: nothing packed")
            mapping = cache / "outputs" / scope / f"{data.get('depHash')}.json"
            if not isinstance(data.get("depHash"), str) or not mapping.is_file():
                continue
            named = [a for a in strings(load(mapping).get("data")) if ARTIFACT.fullmatch(a)]
            if missing := [a for a in named if not (cache / "artifacts" / a).is_file()]:
                if kind == "local":
                    sys.exit(f"lake-cache: {mapping} names {missing[0]}, which the store lacks: nothing packed")
                continue
            if kind == "local":
                module = module_name(root, trace)
                if not all([built_as(build, module, a, cache) for a in named]):
                    continue  # a build stopped before writing it: not packed
                local_maps[f"{scope}/{data['depHash']}"] = module
                local_entries[module] = (mapping.relative_to(cache).as_posix(), named, trace.stat().st_mtime)
                continue
            maps.add(mapping.relative_to(cache).as_posix())
            arts.update(named)
    bound = keys.of(set(local_maps.values()))
    if unbound := sorted(m for m in local_maps.values() if bound[m] is None):
        sys.exit(f"lake-cache: no single source, or no readable imports, for {unbound[:5]}: nothing packed")
    newest: dict[str, float] = {}

    def latest(m: str) -> float:  # the newest source in m's local closure
        if m not in newest:
            newest[m] = max([keys.source(m).stat().st_mtime,
                             *(latest(i) for i in keys.deps[m] if keys.source(i))])
        return newest[m]

    # A module is packed only with every local import packed, and built after every source of its closure: else
    # its outputs are not those of the closure its key binds.
    packed = {m for m, (_, _, built_at) in local_entries.items() if latest(m) <= built_at}
    while drop := {m for m in packed if any(keys.source(i) and i not in packed for i in keys.deps[m])}:
        packed -= drop
    local_maps = {r: m for r, m in local_maps.items() if m in packed}
    for m in packed:
        maps.add(local_entries[m][0])
        arts.update(local_entries[m][1])
    if not maps and not local_entries:
        sys.exit(f"lake-cache: no entry of {cache} is in {pkg}'s build: was LAKE_ARTIFACT_CACHE on?")
    manifest = json.dumps({
        "digest": digest(), "local": sorted(local_scopes),
        "modules": {r: {"module": m, "key": bound[m]} for r, m in local_maps.items()},
        "artifacts": {a: sha256((cache / "artifacts" / a).read_bytes()) for a in sorted(arts)}}).encode()
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
    log(f"{len(maps)} targets ({len(local_maps)} local modules bound), {len(arts)} outputs, "
        f"{archive.stat().st_size / 2**30:.1f} GB packed")


def members(archive: Path):
    zstd = subprocess.Popen(["zstd", "-dcq", str(archive)], stdout=subprocess.PIPE)
    try:
        with tarfile.open(fileobj=zstd.stdout, mode="r|") as tar:
            for member in tar:
                if not member.isdir():
                    yield tar, member
    finally:
        zstd.stdout.close()
        zstd.wait()


def unpack(archive: Path, cache: Path) -> None:
    if subprocess.run(["zstd", "-tq", str(archive)], check=False).returncode:
        sys.exit(f"lake-cache: {archive} fails zstd's checksum: nothing unpacked")
    manifest, raw, first = {}, b"", True
    try:
        for tar, member in members(archive):  # everything checked before anything is installed
            if not (member.isfile() and MEMBER.fullmatch(member.name)) or (member.name == MANIFEST) != first:
                raise ValueError(f"{member.name!r} is outside the layout, or the manifest is not first and once")
            content = tar.extractfile(member).read()
            if first:
                raw, manifest, first = content, json.loads(content), False
                if manifest["digest"] != digest():
                    raise ValueError("its manifest is for another tooling")
                local = set(manifest["local"])
            elif member.name.startswith("artifacts/"):
                path, want = cache / member.name, manifest["artifacts"].get(member.name[10:])
                if sha256(content) != want or path.exists() and sha256(path.read_bytes()) != want:
                    raise ValueError(f"{member.name} is not the manifest's")
    except (ValueError, KeyError, TypeError, AttributeError, tarfile.TarError) as e:
        sys.exit(f"lake-cache: {archive}: {e}: nothing unpacked")
    if first:
        sys.exit(f"lake-cache: {archive} is empty")
    added = 0
    for tar, member in members(archive):
        if member.name == MANIFEST:
            continue
        if member.name.startswith("outputs/"):  # a local module's map is held until `filter` binds it
            path = cache / ("held" if member.name.split("/")[1] in local else "outputs") / member.name[8:]
        else:
            path = cache / member.name
        mode = 0o644 if member.name.startswith("outputs/") else 0o555 if member.mode & 0o111 else 0o444
        added += install(path, tar.extractfile(member).read(), mode)
    install(cache / "manifests" / f"{sha256(raw)[:16]}.json", raw, 0o444)  # last: until then, nothing is bound
    log(f"{added} files added to {cache}")


def install(path: Path, content: bytes, mode: int) -> bool:
    """`content` at `path` unless a file is there, written whole under another name first."""
    if path.exists():
        return False
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = tempfile.NamedTemporaryFile(dir=path.parent, delete=False)
    try:
        with tmp:
            tmp.write(content)
        os.chmod(tmp.name, mode)
        os.replace(tmp.name, path)
    finally:
        if os.path.exists(tmp.name):
            os.unlink(tmp.name)
    return True


def gh(*args: str) -> str:
    return subprocess.run(["gh", *args], capture_output=True, text=True, check=True).stdout


def get(pkg: Path, cache: Path | None) -> None:
    name = artifact_name()
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
            if not (run["event"] in ("push", "schedule") and run["head_repository"]["full_name"] == REPO
                    and run["head_branch"] == "main"
                    and any(not a["expired"] and a["name"] == name for a in json.loads(gh(
                        "api", f"repos/{REPO}/actions/runs/{run['id']}/artifacts?name={name}"))["artifacts"])
                    and gh("api", f"repos/{REPO}/compare/{run['head_sha']}...refs/heads/main",
                           "--jq", ".status").strip() in ("identical", "ahead")):
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
    sub.add_parser("artifact-name")
    for cmd in ("get", "pack", "unpack", "filter", "check"):
        p = sub.add_parser(cmd)
        p.add_argument("dir", type=Path, **({"nargs": "?", "default": FORMAL / "lean_vm"} if cmd == "get" else {}))
        if cmd in ("pack", "unpack"):
            p.add_argument("archive", type=Path)
        p.add_argument("--cache", type=Path, help="the cache directory (default: Lake's for DIR)")
    opts = parser.parse_args()
    if opts.cmd in ("digest", "artifact-name"):
        print(digest() if opts.cmd == "digest" else artifact_name())
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
    elif opts.cmd == "filter":
        filter_maps(pkg, cache)
    else:
        check(pkg, cache)


if __name__ == "__main__":
    main()
