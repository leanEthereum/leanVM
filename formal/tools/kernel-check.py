#!/usr/bin/env python3
"""Every built module checked again by the kernel, one process per module (`KernelCheck.lean`).

  python3 -I tools/kernel-check.py DIR [PROJECT ...] [--jobs N] [--mem GB] [--all] [--deadline EPOCH]

From the workspace `DIR` (its `lake env`, after its build), each module of the `PROJECT`s (default: `DIR`) that has an
`.olean`, a trace and a source is replayed by the kernel into the environment of its imports, its private part
included, as the toolchain's `leanchecker` does. This is the guard against a declaration added without the kernel
(`debug.skipKernelTC`, or meta code adding it), which `#print axioms` cannot see and `escape-scan.py` only reads the
sources for. `leanchecker` itself checks every module under a name at once, in one process, and on lean_vm's root
crashes or exhausts the machine's memory.

Each module runs in its own process (`KernelCheck.lean` cannot free one module's environment before the next), capped
at `LEAN_VMEM_KB` of virtual memory (default 40 GB), at most `--jobs` at once (default: the cores) and within `--mem`
(default: the machine's available memory less 4 GB), each counted at its build's peak anonymous memory from the
`lake-build.tsv` tables (`lake-build.py`) plus 1 GB; the slowest builds go first, and a module waits until the
modules before it are admitted. A process that dies of a signal is run again once (the kernel's sporadic crash that
`lake-build.py` also retries); a module the kernel rejects fails the run, and nothing more is started.

A module that passes is recorded in `DIR/.lake/kernel-check.tsv` with its trace's dependency hash and its `.olean`s'
hashes, which Lake computes over its source, its options, the toolchain and every artifact of its imports that it
reads: a module whose record matches is not checked again (`--all` checks it all the same), and a run keeps only the
entries that match. With `--deadline` (seconds since the epoch), no module starts after it, and the run fails with exit
code 2 if any is left unchecked: what passed stays recorded, so the next run goes on from there. CI's lean_vm job
saves the record on every run, and a pull request's build too when its check ran out of time, so that a rerun only
checks.
"""

from __future__ import annotations

import argparse
import json
import os
import resource
import signal
import subprocess
import sys
import tempfile
import time
import tomllib
from pathlib import Path
from typing import IO

GB = 1 << 30
TOOLS = Path(__file__).resolve().parent
DEFAULT_NEED = 2 * GB  # a module without a build record
EXTRA = 1 * GB  # the imports' environment beside the build's anonymous memory
RECORD = "kernel-check.tsv"


def log(message: str) -> None:
    print(f"kernel-check: {message}", file=sys.stderr, flush=True)


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


def source_dirs(project: Path) -> list[Path]:
    """The source directories of the project's libraries and executables (`srcDir`)."""
    config = tomllib.loads((project / "lakefile.toml").read_text(encoding="utf-8"))
    targets = config.get("lean_lib", []) + config.get("lean_exe", [])
    return sorted({(project / t.get("srcDir", ".")).resolve() for t in targets} or {project})


def modules(project: Path) -> tuple[dict[str, str | None], int]:
    """The project's built modules with a source, each with its key (`None` without a trace), and how many built
    modules have no source any more."""
    lib = project / ".lake" / "build" / "lib" / "lean"
    roots = source_dirs(project)
    found, stale = {}, 0
    for olean in lib.rglob("*.olean"):
        rel = olean.relative_to(lib).with_suffix("")
        if not any((root / rel).with_suffix(".lean").exists() for root in roots):
            stale += 1
            continue
        name = ".".join(rel.parts)
        trace = olean.with_suffix(".trace")
        if trace.exists():
            data = json.loads(trace.read_text(encoding="utf-8"))
            found[name] = f"{data.get('depHash')}:{','.join(data.get('outputs', {}).get('o', []))}"
        else:
            found[name] = None
    return found, stale


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("dir", type=Path)
    parser.add_argument("projects", type=Path, nargs="*")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    parser.add_argument("--mem", type=float)
    parser.add_argument("--all", action="store_true")
    parser.add_argument("--deadline", type=float, default=float("inf"))
    args = parser.parse_args()
    work = args.dir.resolve()
    projects = [p.resolve() for p in args.projects] or [work]
    if args.mem is not None:
        budget = int(args.mem * GB)
    else:
        with open("/proc/meminfo", encoding="utf-8") as file:
            info = {line.split(":")[0]: int(line.split()[1]) * 1024 for line in file}
        budget = info["MemAvailable"] - 4 * GB
    lean_path = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=work, check=True, capture_output=True,
                               text=True).stdout.strip()
    env = dict(os.environ, LEAN_PATH=lean_path)
    vmem = int(os.environ.get("LEAN_VMEM_KB", "40000000")) * 1024

    record_path = work / ".lake" / RECORD
    record = {}
    if record_path.exists() and not args.all:
        for line in record_path.read_text(encoding="utf-8").splitlines():
            name, _, key = line.partition("\t")
            record[name] = key
    todo, keys, kept, stale = [], {}, [], 0
    for project in projects:
        found, gone = modules(project)
        stale += gone
        for name, key in found.items():
            if key is not None and record.get(name) == key:
                kept.append(f"{name}\t{key}\n")
            else:
                todo.append(name)
                keys[name] = key
    skipped = len(kept)
    seen = set(keys) | {line.partition("\t")[0] for line in kept}
    kept += [f"{name}\t{key}\n" for name, key in record.items() if name not in seen]  # another project's
    if not todo and not skipped:
        log(f"no built module in {', '.join(map(str, projects))}")
        return 1
    tables = read_tables([*(p / "lake-build.tsv" for p in projects), work / "lake-build.tsv",
                          *(p / ".lake" / "lake-build.tsv" for p in projects), work / ".lake" / "lake-build.tsv"])
    todo.sort(key=lambda m: -tables.get(m, (0.0, 0.0))[0])

    def need(name: str) -> int:
        return min(budget, int(tables[name][1]) + EXTRA if name in tables else DEFAULT_NEED)

    def limit() -> None:
        resource.setrlimit(resource.RLIMIT_AS, (vmem, vmem))

    log(f"{len(todo)} modules to check, {skipped} unchanged since they passed, {stale} stale skipped; "
        f"{args.jobs} jobs within {budget / GB:.1f} GB")
    record_path.parent.mkdir(parents=True, exist_ok=True)
    record_path.write_text("".join(kept), encoding="utf-8")
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
            if keys[name] is not None:
                out.write(f"{name}\t{keys[name]}\n")
                out.flush()
            if done % 500 == 0:
                log(f"{done}/{len(todo)} checked, {time.monotonic() - start:.0f} s")
        elif code < 0 and attempt == 0:
            log(f"{name}: killed by {signal.Signals(-code).name}, run again")
            queue.insert(0, (name, 1))
        else:
            log(f"{name} failed ({code}):\n{output[:20000]}")
            failed.append(name)
    out.close()
    log(f"{done} modules checked in {time.monotonic() - start:.0f} s, {cpu / 3600:.2f} CPU-h; {skipped} unchanged")
    if failed:
        log(f"failed: {' '.join(failed)}")
        return 1
    if queue:
        log(f"{len(queue)} modules left unchecked at the deadline, the {done + skipped} that passed recorded: "
            f"run again to check the rest")
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
