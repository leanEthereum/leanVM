#!/usr/bin/env python3
"""Every built module checked again by the kernel, one process per module (`KernelCheck.lean`).

  python3 -I tools/kernel-check.py DIR [PROJECT ...] [--jobs N] [--mem GB] [--all] [--deadline EPOCH] [--allow-stale]

From the workspace `DIR` (its `lake env`, after its build), each module built in the `PROJECT`s (default: `DIR` and
every package its manifest requires by path) is replayed by the kernel into the environment of its imports, its
private part included, as the toolchain's `leanchecker` does. This is the guard against a declaration added without
the kernel (`debug.skipKernelTC`, or meta code adding it), which `#print axioms` cannot see and `escape-scan.py` only
reads the sources for. `leanchecker` itself checks every module under a name at once, in one process, and on lean_vm's
root crashes or exhausts the machine's memory.

The modules are the `.olean`s in each project's `.lake/build/lib/lean`, each named by its trace with its source. A
project whose `lakefile.lean` exists (which Lake would read instead of `lakefile.toml`) or whose `lakefile.toml` moves
its build directory fails the run, and so does an `.olean` whose trace or source is missing, unless `--allow-stale`:
Lake resolves an import to a source, so a module whose source is gone is imported by no module built after it.

Each module runs in its own process (`KernelCheck.lean` cannot free one module's environment before the next), capped
at `LEAN_VMEM_KB` of virtual memory (default 40 GB), aborting on a panic, at most `--jobs` at once (default: the cores)
and within `--mem` (default: the machine's available memory less 4 GB), each counted at its build's peak anonymous
memory from the `lake-build.tsv` tables (`lake-build.py`) plus 1 GB; the slowest builds go first, and a module waits
until the modules before it are admitted. A process that dies of a signal is run again once (the kernel's sporadic
crash that `lake-build.py` also retries); a module the kernel rejects fails the run, and nothing more is started.

A module that passes is recorded in `DIR/.lake/kernel-check.tsv` under its trace's dependency hash (which Lake computes
over its source, its options, the toolchain and every artifact of its imports that it reads), the SHA-256 of its
`.olean` parts and of this script and `KernelCheck.lean`: a module whose entry matches is not checked again. `--all`
checks every module all the same, replacing an entry when its module passes and removing it when it fails, so an
interrupted `--all` run leaves the record no smaller. With `--deadline` (seconds since the epoch), no module starts
after it, and the run fails with exit code 2 if any is left unchecked: what passed stays recorded, so the next run
goes on from there. The record and the build are only as trustworthy as whoever wrote them: in CI, `main`'s run,
which restores only what `main` saved, is the gate, and a pull request's run is advisory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import resource
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from typing import IO

GB = 1 << 30
TOOLS = Path(__file__).resolve().parent
DEFAULT_NEED = 2 * GB  # a module without a build record
EXTRA = 1 * GB  # the imports' environment beside the build's anonymous memory
RECORD = "kernel-check.tsv"
PARTS = (".olean", ".olean.server", ".olean.private")


def log(message: str) -> None:
    print(f"kernel-check: {message}", file=sys.stderr, flush=True)


def sha256(path: Path) -> str:
    with path.open("rb") as file:
        return hashlib.file_digest(file, "sha256").hexdigest()


def read_tables(paths: list[Path]) -> dict[str, tuple[float, float]]:
    """Each module's recorded CPU seconds and peak anonymous memory (bytes), later tables over earlier ones."""
    table = {}
    for path in paths:
        if path.exists():
            for line in path.read_text(encoding="utf-8").splitlines():
                fields = line.split("\t")
                if len(fields) == 5 and not line.startswith("#"):
                    table[fields[0]] = (float(fields[2]), float(fields[4]) * (1 << 20))
    return table


def path_packages(work: Path) -> list[Path]:
    """The workspace and the packages its manifest requires by path."""
    manifest = json.loads((work / "lake-manifest.json").read_text(encoding="utf-8"))
    return [work, *((work / p["dir"]).resolve() for p in manifest.get("packages", []) if p.get("type") == "path")]


def config_errors(project: Path) -> list[str]:
    """What in the project's Lake configuration would put modules where this script does not look."""
    if (project / "lakefile.lean").exists():
        return [f"{project}/lakefile.lean exists: Lake reads it instead of lakefile.toml"]
    if not (project / "lakefile.toml").exists():
        return [f"{project} has no lakefile.toml"]
    config = tomllib.loads((project / "lakefile.toml").read_text(encoding="utf-8"))
    return [f"{project}/lakefile.toml sets {key}" for key in ("buildDir", "leanLibDir") if key in config]


def modules(project: Path) -> tuple[dict[str, tuple[Path, str]], list[str]]:
    """The project's built modules, each with its `.olean` and its trace's dependency hash, and the `.olean`s whose
    trace or source is missing."""
    lib = project / ".lake" / "build" / "lib" / "lean"
    found, stale = {}, []
    for olean in sorted(lib.rglob("*.olean")):
        name = ".".join(olean.relative_to(lib).with_suffix("").parts)
        trace = olean.with_suffix(".trace")
        data = json.loads(trace.read_text(encoding="utf-8")) if trace.exists() else {}
        sources = [i[0] for i in data.get("inputs", []) if isinstance(i, list) and i and isinstance(i[0], str)
                   and i[0].endswith(".lean") and os.path.isabs(i[0])]
        if not sources or not all(Path(s).exists() for s in sources) or "depHash" not in data:
            stale.append(name)
            continue
        found[name] = (olean, str(data["depHash"]))
    return found, stale


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("dir", type=Path)
    parser.add_argument("projects", type=Path, nargs="*")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    parser.add_argument("--mem", type=float)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--deadline", type=float, default=float("inf"))
    parser.add_argument("--allow-stale", action="store_true")
    args = parser.parse_args()
    work = args.dir.resolve()
    projects = [p.resolve() for p in args.projects] or path_packages(work)
    errors = [e for p in projects for e in config_errors(p)]
    if errors:
        for error in errors:
            log(error)
        return 1
    if args.mem is not None:
        budget = int(args.mem * GB)
    else:
        with open("/proc/meminfo", encoding="utf-8") as file:
            info = {line.split(":")[0]: int(line.split()[1]) * 1024 for line in file}
        budget = info["MemAvailable"] - 4 * GB
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=work, check=True, capture_output=True,
                               text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=lean_path, LEAN_ABORT_ON_PANIC="1")
    vmem = int(os.environ.get("LEAN_VMEM_KB", "40000000")) * 1024

    found, stale = {}, []
    for project in projects:
        more, gone = modules(project)
        found.update(more)
        stale += gone
    if stale:
        log(f"{len(stale)} .oleans without a trace or a source: {' '.join(stale[:10])}{' ...' if len(stale) > 10 else ''}")
        if not args.allow_stale:
            log("refusing to skip them (--allow-stale skips them)")
            return 1
    if not found:
        log(f"no built module in {', '.join(map(str, projects))}")
        return 1
    tool = hashlib.sha256(b"".join((TOOLS / f).read_bytes() for f in ("KernelCheck.lean", "kernel-check.py")))
    tool_hash = tool.hexdigest()[:16]

    def key_of(name: str) -> str:
        olean, dep = found[name]
        parts = (olean.with_name(olean.stem + suffix) for suffix in PARTS)
        return ":".join([dep, *(sha256(p) for p in parts if p.exists()), tool_hash])

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        keys = dict(zip(found, pool.map(key_of, found)))

    record_path = work / ".lake" / RECORD
    record: dict[str, str] = {}
    if record_path.exists():
        for line in record_path.read_text(encoding="utf-8").splitlines():
            name, _, key = line.partition("\t")
            record[name] = key
    # An entry stays while it matches its module's build, or names a module outside these projects.
    entries = {name: key for name, key in record.items() if keys.get(name, key) == key}
    todo = [name for name in found if args.all or entries.get(name) != keys[name]]
    skipped = len(found) - len(todo)
    tables = read_tables([*(p / "lake-build.tsv" for p in projects), work / "lake-build.tsv",
                          *(p / ".lake" / "lake-build.tsv" for p in projects), work / ".lake" / "lake-build.tsv"])
    todo.sort(key=lambda m: -tables.get(m, (0.0, 0.0))[0])

    def need(name: str) -> int:
        return min(budget, int(tables[name][1]) + EXTRA if name in tables else DEFAULT_NEED)

    def limit() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (vmem, vmem))

    def save() -> None:
        record_path.write_text("".join(f"{n}\t{k}\n" for n, k in sorted(entries.items())), encoding="utf-8")

    log(f"{len(todo)} modules to check, {skipped} unchanged since they passed, {len(stale)} stale skipped; "
        f"{args.jobs} jobs within {budget / GB:.1f} GB")
    record_path.parent.mkdir(parents=True, exist_ok=True)
    save()
    out = record_path.open("a", encoding="utf-8")
    running: dict[int, tuple[str, subprocess.Popen, IO[bytes], int]] = {}
    queue = [(m, 0) for m in todo]
    used, cpu, done, failed = 0, 0.0, 0, []
    start = time.monotonic()
    while queue or running:
        while queue and not failed and time.time() < args.deadline and len(running) < args.jobs and \
                (not running or used + need(queue[0][0]) <= budget):
            name, attempt = queue.pop(0)
            log_file = tempfile.TemporaryFile()
            proc = subprocess.Popen(["lean", "--run", str(TOOLS / "KernelCheck.lean"), name], cwd=work, env=env,
                                    stdout=log_file, stderr=subprocess.STDOUT, preexec_fn=limit)
            running[proc.pid] = (name, proc, log_file, attempt)
            used += need(name)
        if not running:
            break
        pid, status, usage = os.wait4(-1, 0)
        if pid not in running:
            continue
        name, proc, log_file, attempt = running.pop(pid)
        proc.returncode = os.waitstatus_to_exitcode(status)  # reaped here, not by `subprocess`
        used -= need(name)
        cpu += usage.ru_utime + usage.ru_stime
        log_file.seek(0)
        output = log_file.read().decode(errors="replace")
        log_file.close()
        code = proc.returncode
        if code == 0 and f"ok {name}" in output:
            done += 1
            entries[name] = keys[name]
            out.write(f"{name}\t{keys[name]}\n")  # kept if the run is killed; rewritten below
            out.flush()
            if done % 500 == 0:
                log(f"{done}/{len(todo)} checked, {time.monotonic() - start:.0f} s")
        elif code < 0 and attempt == 0:
            log(f"{name}: killed by {signal.Signals(-code).name}, run again")
            queue.insert(0, (name, 1))
        else:
            log(f"{name} failed ({code}):\n{output[:20000]}")
            failed.append(name)
            if entries.pop(name, None) is not None:  # at once, so that a killed run keeps no entry for it
                out.close()
                save()
                out = record_path.open("a", encoding="utf-8")
    out.close()
    save()
    log(f"{done} modules checked in {time.monotonic() - start:.0f} s, {cpu / 3600:.2f} CPU-h; {skipped} unchanged")
    if failed:
        log(f"failed: {' '.join(failed)}")
        return 1
    if queue:
        log(f"{len(queue)} modules left unchecked at the deadline, the {len(entries)} recorded kept: "
            f"run again to check the rest")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
