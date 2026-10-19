"""Build the default targets a few modules at a time.

Lake has no job limit, and a parallel build of the generated kernel-checked families runs more of them at once than a
16 GB runner holds. Lake builds the dependencies of a module it is asked for in parallel too, so a call may only name
modules whose out-of-date imports are already built. Each pass takes the out-of-date modules from `lake build --no-build`,
levels them by their imports among themselves, and builds them level by level, WIDTH modules per `lake build`.
Lake reports only some of them, so a module with no `.olean` and every importer of an out-of-date module count too. Passes repeat until none is left; a plain `lake build` ends it.
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
WIDTH = int(os.environ.get("WIDTH", "2"))
BUILDING = re.compile(r"✖ .*Building (\S+)")
IMPORT = re.compile(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(\S+)")


def lake(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(["lake", *args], cwd=ROOT, capture_output=True, text=True, check=False)


def out_of_date() -> list[str]:
    result = lake("build", "--no-build")
    found = (BUILDING.search(line) for line in (result.stdout + result.stderr).splitlines())
    return list(dict.fromkeys(m.group(1) for m in found if m))


def modules() -> dict[str, list[str]]:
    """Every module of the package, with its imports among them."""
    paths = {}
    for base, root in ((ROOT, "LeanVM"), (ROOT / "tests", "LeanVMTests")):
        for path in [base / f"{root}.lean", *(base / root).rglob("*.lean")]:
            if path.exists():
                paths[".".join(path.relative_to(base).with_suffix("").parts)] = path
    result = {}
    for name, path in paths.items():
        matches = [IMPORT.match(line) for line in path.read_text(encoding="utf-8").splitlines()]
        result[name] = [m.group(1) for m in matches if m and m.group(1) in paths and m.group(1) != name]
    return result


def stale(deps: dict[str, list[str]]) -> list[str]:
    """The modules Lake reports, those with no `.olean`, and everything importing one of them."""
    libdir = ROOT / ".lake" / "build" / "lib" / "lean"
    stale = {m for m in out_of_date() if m in deps} | {m for m in deps if not (libdir / (m.replace(".", "/") + ".olean")).exists()}
    importers: dict[str, list[str]] = {}
    for module, imported in deps.items():
        for dep in imported:
            importers.setdefault(dep, []).append(module)
    stack = list(stale)
    while stack:
        for importer in importers.get(stack.pop(), []):
            if importer not in stale:
                stale.add(importer)
                stack.append(importer)
    return sorted(stale)


def levels(pending: list[str], imports: dict[str, list[str]]) -> list[list[str]]:
    """The pending modules by level: one more than the highest level among their pending imports."""
    pending_set = set(pending)
    level: dict[str, int] = {}

    def depth(module: str) -> int:
        if module not in level:
            level[module] = 0
            level[module] = 1 + max((depth(d) for d in imports[module] if d in pending_set), default=0)
        return level[module]

    for module in pending:
        depth(module)
    return [[m for m in pending if level[m] == n] for n in range(1, max(level.values()) + 1)]


def main() -> None:
    sys.setrecursionlimit(100000)
    imports = modules()
    previous: list[str] = []
    for number in range(1, 5000):
        pending = stale(imports)
        if not pending:
            break
        if pending == previous:
            sys.exit(f"no progress on {len(pending)} modules, first {pending[0]}")
        previous = pending
        print(f"pass {number}: {len(pending)} modules", flush=True)
        for group in levels(pending, imports):
            for start in range(0, len(group), WIDTH):
                if subprocess.run(["lake", "build", "-q", *group[start : start + WIDTH]], cwd=ROOT, check=False).returncode:
                    sys.exit(1)
    sys.exit(subprocess.run(["lake", "build"], cwd=ROOT, check=False).returncode)


if __name__ == "__main__":
    main()
