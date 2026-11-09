"""Build a Lake package's targets in one `lake build`, its modules admitted by memory.

  python3 -I lake-build.py DIR [TARGET ...] [--jobs N] [--mem GB] [--cap GB] [--no-scope] [--seed] [--dev]

Lake has no job limit, and a parallel build of lean_vm's generated kernel-checked families runs more of them at once than
a machine holds. Lake still decides what is built, with which options, and writes every trace: it runs `lean` and
`leanir` from a sysroot whose two binaries are this script (`LEAN_SYSROOT`, `LAKE_OVERRIDE_LEAN`), and the script runs
the real ones unchanged, with Lake's arguments and environment, once it admits the module. Lake's thread pool
(`LEAN_NUM_THREADS`) only bounds how many modules wait for admission; the `lean`s get the caller's value back.

Admission: at most `--jobs` modules at once (default: the cores), within `--mem` (default: the machine's memory less
4 GB) counting each running module's estimate (or its current anonymous memory, if larger) and once the largest
file-backed memory among them: the `.olean`s a `lean` maps are shared. A module that alone exceeds it runs alone.
Among the waiting modules the longest path to the end of the build goes first, the module's own time included. The
first that cannot be admitted holds its memory back, so a large module is not starved. The estimates are the peak
anonymous memory from `DIR/.lake/lake-build.tsv`, which every run updates with each module's wall time, CPU time,
peak RSS and peak anonymous memory, over `DIR/lake-build.tsv` (the heavy modules, committed, which `--seed`
rewrites); an unknown module is taken at 2 GB.

The run is a systemd scope capped at `--cap` (default: the machine's memory less 1 GB, without `OOMPolicy=stop`): a
module killed by the kernel there is run again, alone. After the first module that fails nothing more is admitted
and the run fails; otherwise `lake build --no-build` must find the targets up to date, and a plain `lake build` of
them, which replays the warnings, ends the run.

`--dev` is for development only, never for a gate or CI: it builds from `DIR/.lake/lakefile.dev.toml`, written from
`DIR/lakefile.toml` with `buildDir = ".lake/build-dev"` and `debug.skipKernelTC` set on the package's libraries other
than its test driver. Elaboration still runs (tactics, `simp`, `omega`, the elaborator's `decide`, warnings as
errors), but the kernel checks nothing: a false `decide +kernel` is accepted, and `#print axioms` does not show it.
The option is in Lake's traces and the build directory is separate, so a dev `.olean` never satisfies the real build.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import shutil
import signal
import socket
import socketserver
import subprocess
import sys
import tempfile
import threading
import time
import tomllib
from pathlib import Path

GB = 1 << 30
MB = 1 << 20
DEFAULT_NEED = 2 * GB  # an unknown module's anonymous memory
DEFAULT_WALL = 5.0  # an unknown module's time, for the priorities
TABLE = "lake-build.tsv"
HEADER = "# module\twall s\tcpu s\tpeak rss MB\tpeak anon MB\n"
ENV = ("LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN", "LEAN_NUM_THREADS")  # what the run changes for Lake
IMPORT = re.compile(r"(?:(?:public|private)\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.«»']+)")


def log(message: str) -> None:
    print(f"lake-build: {message}", file=sys.stderr, flush=True)


def hms(seconds: float) -> str:
    return f"{int(seconds) // 3600}h{int(seconds) % 3600 // 60:02d}m{int(seconds) % 60:02d}s"


# The wrapper: `lean` and `leanir` of the sysroot Lake runs.


def wrap(tool: str, args: list[str]) -> None:
    real = os.path.join(os.environ["LAKE_BUILD_BIN"], tool)
    env = {k: v for k, v in os.environ.items() if not k.startswith("LAKE_BUILD_")}
    for key, value in json.loads(os.environ["LAKE_BUILD_ENV"]).items():
        if value is None:
            env.pop(key, None)
        else:
            env[key] = value
    setup = args[args.index("--setup") + 1] if tool == "lean" and "--setup" in args else args[0] if tool == "leanir" and args else None
    if setup is None:  # `lean --githash` and the like
        os.execve(real, [real, *args], env)
    with open(setup, encoding="utf-8") as file:
        name = json.load(file)["name"] + ("" if tool == "lean" else f":{tool}")
    with socket.socket(socket.AF_UNIX) as conn:
        conn.connect(os.environ["LAKE_BUILD_SOCK"])
        stream = conn.makefile("rw", encoding="utf-8")

        def say(line: str) -> None:
            stream.write(line + "\n")
            stream.flush()

        alone = False
        while True:
            say(f"want {int(alone)} {name}")
            if stream.readline().strip() != "go":
                print(f"lake-build: {name} not started: an earlier module failed", file=sys.stderr)
                sys.exit(1)
            with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
                start = time.monotonic()
                child = subprocess.Popen([real, *args], env=env, stdout=out, stderr=err)
                say(f"pid {child.pid}")
                _, status, usage = os.wait4(child.pid, 0)
                child.returncode = code = os.waitstatus_to_exitcode(status)
                say(f"done {code} {time.monotonic() - start:.3f} {usage.ru_utime + usage.ru_stime:.3f} {usage.ru_maxrss}")
                if code == -signal.SIGKILL and not alone:  # most likely the scope's memory cap: once more, alone
                    alone = True
                    continue
                for source, sink in ((out, sys.stdout.buffer), (err, sys.stderr.buffer)):
                    source.seek(0)
                    shutil.copyfileobj(source, sink)
                    sink.flush()
            sys.exit(code if code >= 0 else 128 - code)


# The estimates and the priorities.


def read_table(path: Path) -> dict[str, list[float]]:
    table = {}
    if path.exists():
        for line in path.read_text(encoding="utf-8").splitlines():
            fields = line.split("\t")
            if len(fields) == 5 and not line.startswith("#"):
                table[fields[0]] = [float(x) for x in fields[1:]]
    return table


def write_table(path: Path, table: dict[str, list[float]]) -> None:
    rows = (f"{m}\t{w:.1f}\t{c:.1f}\t{r:.0f}\t{a:.0f}\n" for m, (w, c, r, a) in sorted(table.items()))
    path.write_text(HEADER + "".join(rows), encoding="utf-8")


def seed_rows(table: dict[str, list[float]]) -> dict[str, list[float]]:
    """The heavy modules, rounded so that a rewrite changes few lines: 3 GB of anonymous memory or a minute."""
    return {m: [round(w, -1), round(c, -1), round(r, -2), round(a, -2)] for m, (w, c, r, a) in table.items() if a >= 3000 or w >= 60}


def header_imports(path: Path) -> list[str]:
    """The modules a file's header imports."""
    found, comment = [], False
    with path.open(encoding="utf-8", errors="replace") as file:
        for line in file:
            text = line.strip()
            if comment:
                comment = "-/" not in text
                continue
            if text.startswith("/-"):
                comment = "-/" not in text[2:]
                continue
            if not text or text.startswith("--") or text in ("module", "prelude"):
                continue
            match = IMPORT.match(text)
            if not match:
                break
            found.append(match.group(1))
    return found


def priorities(pkg: Path, table: dict[str, list[float]]) -> dict[str, float]:
    """Each module's longest path to the end of the build, its own time included, over the package's import graph."""
    files = {}
    for root, dirs, names in os.walk(pkg):
        dirs[:] = [d for d in dirs if not d.startswith(".") and d not in ("target", "node_modules")]
        for name in names:
            if name.endswith(".lean"):
                path = Path(root) / name
                files[path.relative_to(pkg).with_suffix("").parts] = header_imports(path)
    known = {m for imports in files.values() for m in imports} | set(table)
    importers: dict[str, list[str]] = {}
    for parts, imports in files.items():
        name = next((n for n in (".".join(parts[i:]) for i in range(len(parts))) if n in known), ".".join(parts))
        for imported in imports:
            importers.setdefault(imported, []).append(name)

    def wall(module: str) -> float:
        return table[module][0] if module in table else DEFAULT_WALL

    tail: dict[str, float] = {}

    def length(module: str) -> float:
        if module not in tail:
            tail[module] = wall(module)  # a cycle of guessed names ends here
            tail[module] = wall(module) + max((length(i) for i in importers.get(module, ())), default=0.0)
        return tail[module]

    sys.setrecursionlimit(100000)
    for module in list(importers):
        length(module)
    return tail


# The scheduler.


def meminfo(key: str) -> int:
    with open("/proc/meminfo", encoding="ascii") as file:
        for line in file:
            if line.startswith(key + ":"):
                return int(line.split()[1]) * 1024
    return 0


def proc_status(pid: int) -> tuple[int, int]:
    """A process's resident anonymous and file-backed memory, in bytes."""
    anon = file_backed = 0
    try:
        with open(f"/proc/{pid}/status", encoding="ascii") as file:
            for line in file:
                if line.startswith("RssAnon:"):
                    anon = int(line.split()[1]) * 1024
                elif line.startswith("RssFile:"):
                    file_backed = int(line.split()[1]) * 1024
    except OSError:
        pass
    return anon, file_backed


def cgroup_file(name: str) -> Path | None:
    try:
        line = Path("/proc/self/cgroup").read_text(encoding="ascii").splitlines()[0]
    except (OSError, IndexError):
        return None
    path = Path("/sys/fs/cgroup") / line.split("::", 1)[-1].lstrip("/") / name
    return path if line.startswith("0::") and path.exists() else None


def cpu_ticks() -> tuple[int, int]:
    with open("/proc/stat", encoding="ascii") as file:
        fields = [int(x) for x in file.readline().split()[1:]]
    return sum(fields) - fields[3] - fields[4], sum(fields)


class Run:
    def __init__(self, name: str, need: int, ticket: int, alone: bool) -> None:
        self.name, self.need, self.ticket, self.alone = name, need, ticket, alone
        self.pid = self.anon = self.peak = self.file = 0


class Scheduler:
    def __init__(self, slots: int, budget: int, table: dict[str, list[float]], tail: dict[str, float]) -> None:
        self.slots, self.budget, self.table, self.tail = slots, budget, table, tail
        self.cv = threading.Condition()
        self.waiting: dict[int, tuple[float, int]] = {}  # ticket -> (priority, need)
        self.running: dict[int, Run] = {}
        self.tickets = 0
        self.failed: list[str] = []
        self.killed: list[str] = []
        self.done = 0
        self.busy = self.cpu = 0.0  # module-seconds, CPU seconds
        self.peak_committed = self.peak_anon = self.peak_used = 0
        self.stop = threading.Event()

    def need(self, name: str, alone: bool) -> int:
        if alone:
            return self.budget
        if name in self.table:
            return int(self.table[name][3] * MB * 1.15) + 256 * MB
        return DEFAULT_NEED

    def priority(self, name: str) -> float:
        return self.tail.get(name, self.table[name][0] if name in self.table else DEFAULT_WALL)

    def committed(self) -> int:
        """The running modules' estimates, or their anonymous memory if larger, and the largest mapping of files."""
        runs = self.running.values()
        return sum(max(r.need, r.anon) for r in runs) + max((r.file for r in runs), default=0)

    def choose(self) -> int | None:
        """The ticket to admit now: the first by priority that fits, after the memory held back for the first that does not."""
        if len(self.running) >= self.slots:
            return None
        used, available, held = self.committed(), meminfo("MemAvailable"), 0
        for ticket, (_, need) in sorted(self.waiting.items(), key=lambda item: -item[1][0]):
            if not self.running or (used + held + need <= self.budget and need + GB <= available):
                return ticket
            held = held or need
        return None

    def admit(self, name: str, alone: bool) -> Run | None:
        with self.cv:
            ticket = self.tickets
            self.tickets += 1
            self.waiting[ticket] = (float("inf") if alone else self.priority(name), self.need(name, alone))
            try:
                while not self.failed:
                    if self.choose() == ticket:
                        run = self.running[ticket] = Run(name, self.waiting[ticket][1], ticket, alone)
                        return run
                    self.cv.wait(1.0)
                return None
            finally:
                del self.waiting[ticket]
                self.cv.notify_all()

    def release(self, run: Run, reply: list[str] | None) -> None:
        with self.cv:
            self.running.pop(run.ticket, None)
            self.cv.notify_all()
            if reply is None:
                return
            code, wall, cpu, maxrss = int(reply[1]), float(reply[2]), float(reply[3]), int(reply[4])
            self.busy += wall
            self.cpu += cpu
            if code == 0:
                self.done += 1
                self.table[run.name] = [wall, cpu, maxrss / 1024, max(run.peak, run.anon) / MB]
            elif code == -signal.SIGKILL and not run.alone:
                self.killed.append(run.name)
            else:
                self.failed.append(run.name)

    def poll(self) -> None:
        """Every half second: the running modules' memory, the peaks, and a line of progress every two minutes."""
        last = time.monotonic()
        while not self.stop.wait(0.5):
            with self.cv:
                for run in self.running.values():
                    if run.pid:
                        run.anon, run.file = proc_status(run.pid)
                        run.peak = max(run.peak, run.anon)
                self.peak_committed = max(self.peak_committed, self.committed())
                self.peak_anon = max(self.peak_anon, sum(r.anon for r in self.running.values()))
                self.peak_used = max(self.peak_used, meminfo("MemTotal") - meminfo("MemAvailable"))
                self.cv.notify_all()
                if time.monotonic() - last >= 120:
                    last = time.monotonic()
                    log(f"{self.done} built, {len(self.running)} running, {len(self.waiting)} waiting, "
                        f"{self.committed() / GB:.1f} of {self.budget / GB:.1f} GB committed")


def serve(scheduler: Scheduler, path: str) -> socketserver.UnixStreamServer:
    class Handler(socketserver.StreamRequestHandler):
        def handle(self) -> None:
            run, reply = None, None
            try:
                for line in self.rfile:
                    words = line.decode().split()
                    if words[0] == "want":
                        run, reply = scheduler.admit(words[2], words[1] == "1"), None
                        self.wfile.write(b"go\n" if run else b"stop\n")
                        self.wfile.flush()
                        if run is None:
                            return
                    elif words[0] == "pid" and run:
                        run.pid = int(words[1])
                    elif words[0] == "done" and run:
                        reply = words
                        scheduler.release(run, reply)
                        run = None
            finally:
                if run:  # the wrapper is gone without a word
                    scheduler.release(run, None)

    class Server(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
        daemon_threads = True

    server = Server(path, Handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server


# The run.


def in_scope(cap: int, budget: int) -> None:
    """Run this script again, with the budget set, in a systemd scope capped at `cap` bytes, if one can be made."""
    if os.environ.get("LAKE_BUILD_SCOPED") or not shutil.which("systemd-run"):
        return
    base = ["systemd-run", "--scope", "--quiet", "--collect", "--no-ask-password", "-p", f"MemoryMax={cap}", "-p", "OOMPolicy=continue"]
    for command in (base, [*base, "--user"]):
        if subprocess.run([*command, "true"], capture_output=True, check=False).returncode == 0:
            os.environ["LAKE_BUILD_SCOPED"] = "1"
            argv = [os.path.abspath(sys.argv[0]), *sys.argv[1:], "--mem", str(budget / GB)]
            os.execvp(command[0], [*command, "--", sys.executable, "-I", *argv])
    log("no systemd scope can be made here; the memory budget is the only guard")


def fake_sysroot(real: Path, into: Path) -> None:
    """A sysroot like `real` whose `lean` and `leanir` are this script."""
    (into / "bin").mkdir(parents=True)
    for entry in real.iterdir():
        if entry.name != "bin":
            (into / entry.name).symlink_to(entry)
    for entry in (real / "bin").iterdir():
        target = into / "bin" / entry.name
        if entry.name in ("lean", "leanir"):
            script = shlex.join([sys.executable, "-I", os.path.abspath(__file__), "--wrap", entry.name])
            target.write_text(f'#!/bin/sh\nexec {script} "$@"\n', encoding="utf-8")
            target.chmod(0o755)
        else:
            target.symlink_to(entry)


def dev_config(pkg: Path) -> Path:
    """`DIR/.lake/lakefile.dev.toml`: `DIR/lakefile.toml` with its own build directory and the kernel skipped on the
    libraries other than the test driver."""
    text = (pkg / "lakefile.toml").read_text(encoding="utf-8")
    config = tomllib.loads(text)
    if "buildDir" in config:
        sys.exit("lake-build: --dev: lakefile.toml already sets buildDir")
    skip = [lib["name"] for lib in config.get("lean_lib", []) if lib["name"] != config.get("testDriver")]
    for lib in config.get("lean_lib", []):
        if lib["name"] in skip and "leanOptions" in lib:
            sys.exit(f"lake-build: --dev: library {lib['name']} already sets leanOptions")
    lines, out, lib = text.splitlines(), [], None
    for i, line in enumerate(lines):
        if i == next(j for j, l in enumerate(lines) if l.startswith("[")):
            out += ['buildDir = ".lake/build-dev"  # lake-build.py --dev: kernel unchecked, never mixed with the real build', ""]
        out.append(line)
        if line.strip() == "[[lean_lib]]":
            lib = True
        elif line.startswith("["):
            lib = None
        elif lib and (m := re.fullmatch(r'name\s*=\s*"([^"]+)"\s*', line)) and m[1] in skip:
            out.append("leanOptions = {debug.skipKernelTC = true}")  # a dotted key, unquoted
    target = pkg / ".lake" / "lakefile.dev.toml"
    target.parent.mkdir(exist_ok=True)
    target.write_text("\n".join(out) + "\n", encoding="utf-8")
    return target


def main() -> None:
    if len(sys.argv) > 2 and sys.argv[1] == "--wrap":
        wrap(sys.argv[2], sys.argv[3:])
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("dir", type=Path, help="the Lake package")
    parser.add_argument("targets", nargs="*", help="what to build (default: the default targets)")
    parser.add_argument("--jobs", type=int, default=len(os.sched_getaffinity(0)), help="modules at once (default: the cores)")
    parser.add_argument("--mem", type=float, help="memory budget in GB (default: the machine's less 4)")
    parser.add_argument("--cap", type=float, help="the scope's memory cap in GB (default: the machine's less 1)")
    parser.add_argument("--no-scope", action="store_true", help="no systemd scope")
    parser.add_argument("--seed", action="store_true", help=f"rewrite DIR/{TABLE} from the run's table")
    parser.add_argument("--dev", action="store_true", help="development only: skip the kernel, in .lake/build-dev")
    opts = parser.parse_args()
    if opts.dev and opts.seed:
        sys.exit("lake-build: --seed records the real build, not a --dev one")
    total = meminfo("MemTotal")
    if limit := cgroup_file("memory.max"):
        text = limit.read_text(encoding="ascii").strip()
        total = min(total, int(text)) if text.isdigit() else total
    budget = int(opts.mem * GB) if opts.mem else max(total - 4 * GB, 2 * GB)
    if not opts.no_scope:
        in_scope(int(opts.cap * GB) if opts.cap else total - GB, budget)
    pkg = opts.dir.resolve()
    lake = ["lake", "-f", str(dev_config(pkg))] if opts.dev else ["lake"]
    if opts.dev:
        log("--dev: the kernel checks nothing; development only, never a gate")
    # A dev run's modules are lighter: its records stay apart, so they never understate the real build's.
    local, seed = pkg / ".lake" / ("lake-build-dev.tsv" if opts.dev else TABLE), pkg / TABLE
    table = {**read_table(seed), **read_table(local)}
    scheduler = Scheduler(opts.jobs, budget, table, priorities(pkg, table))
    real = Path(subprocess.run(["lean", "--print-prefix"], cwd=pkg, capture_output=True, text=True, check=True).stdout.strip())
    work = Path(tempfile.mkdtemp(prefix="lake-build-"))
    try:
        fake_sysroot(Path(os.environ.get("LEAN_SYSROOT") or real), work / "sysroot")
        server = serve(scheduler, str(work / "socket"))
        threading.Thread(target=scheduler.poll, daemon=True).start()
        env = {
            **os.environ,
            "LAKE_BUILD_ENV": json.dumps({k: os.environ.get(k) for k in ENV}),
            "LAKE_BUILD_SOCK": str(work / "socket"),
            "LAKE_BUILD_BIN": str(Path(os.environ.get("LEAN_SYSROOT") or real) / "bin"),
            "LEAN_SYSROOT": str(work / "sysroot"),
            "LAKE_OVERRIDE_LEAN": "true",
            "LEAN_NUM_THREADS": str(4 * opts.jobs),  # Lake's pool: the modules waiting for admission, and Lake's own work
        }
        log(f"{pkg.name}: {opts.jobs} at once within {budget / GB:.1f} GB, {len(table)} modules' records")
        start, ticks = time.monotonic(), cpu_ticks()
        code = subprocess.run([*lake, "build", "-q", *opts.targets], cwd=pkg, env=env, check=False).returncode
        elapsed, (busy1, all1) = time.monotonic() - start, cpu_ticks()
        server.shutdown()
        scheduler.stop.set()
    finally:
        shutil.rmtree(work, ignore_errors=True)
    local.parent.mkdir(exist_ok=True)
    write_table(local, scheduler.table)
    if opts.seed:
        write_table(seed, seed_rows(scheduler.table))
    peak = cgroup_file("memory.peak")
    log(f"{scheduler.done} modules in {hms(elapsed)}, {scheduler.cpu / 3600:.2f} CPU-h; "
        f"{scheduler.busy / max(elapsed, 1):.1f} of {opts.jobs} running on average, the machine's CPU "
        f"{100 * (busy1 - ticks[0]) / max(all1 - ticks[1], 1):.0f}% busy; peak memory: {scheduler.peak_committed / GB:.1f} GB "
        f"committed, {scheduler.peak_anon / GB:.1f} GB anonymous in the modules, {scheduler.peak_used / GB:.1f} GB used on the machine"
        + (f", {int(peak.read_text()) / GB:.1f} GB in the scope" if peak else ""))
    if scheduler.killed:
        log(f"killed and run again alone: {', '.join(scheduler.killed)}")
    if scheduler.failed or code:
        sys.exit(f"lake-build: failed: {', '.join(scheduler.failed) or f'lake build exited with {code}'}")
    if subprocess.run([*lake, "build", "--no-build", "-q", *opts.targets], cwd=pkg, check=False).returncode:
        sys.exit("lake-build: Lake finds the targets out of date after the run")
    sys.exit(subprocess.run([*lake, "build", *opts.targets], cwd=pkg, check=False).returncode)


if __name__ == "__main__":
    main()
