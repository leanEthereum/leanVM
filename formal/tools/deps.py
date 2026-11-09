#!/usr/bin/env python3
"""What an edit rebuilds, from the import graph of the six projects and the recorded build times.

  python3 -I tools/deps.py cone MODULE|FILE ...   what changing these modules' interface rebuilds
  python3 -I tools/deps.py slow [N]               the N slowest modules, and what rebuilds them
  python3 -I tools/deps.py path [MODULE]          the longest chain of a full build (of MODULE)

Times are the last builds' (`*/.lake/lake-build.tsv`, written by `lake-build.py`, which records
every module it builds, the dependencies' included); a module without one counts as 0 s.

A module is rebuilt when a module it imports, directly or not, changes what it exports: in the
module system (`module` files) that is a declaration's statement, an exposed definition's body or
the set of declarations, not a proof, a comment or a private declaration; a file outside the
module system rebuilds on any change of its imports. `cone` lists both: the modules rebuilt when
the interface changes, and, of them, those rebuilt on any edit.
"""
import os
import re
import sys
from collections import defaultdict
from functools import lru_cache

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECTS = ["Statement", "common", "lean_xmss", "lean_sphincs", "lean_da", "lean_vm"]
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)")


def module_name(project, path):
    """`Statement/X.lean` is `Statement.X`; elsewhere a module is named from its project's
    source directory (`tests/` for the tests, `cli/` for the executables)."""
    rel = os.path.relpath(path, ROOT if project == "Statement" else os.path.join(ROOT, project))
    rel = rel[:-len(".lean")]
    for src in ("tests/", "cli/"):
        if rel.startswith(src):
            rel = rel[len(src):]
    return rel.replace("/", ".")


def read_graph():
    imports, files, legacy = {}, {}, set()
    for project in PROJECTS:
        for top, dirs, names in os.walk(os.path.join(ROOT, project)):
            dirs[:] = [d for d in dirs if d not in (".lake", "scripts", "fixtures")]
            for name in names:
                if not name.endswith(".lean"):
                    continue
                path = os.path.join(top, name)
                mod = module_name(project, path)
                found, is_module = [], False
                with open(path, encoding="utf-8") as f:
                    for line in f:
                        s = line.strip()
                        if s == "module":
                            is_module = True
                        m = IMPORT.match(s)
                        if m:
                            found.append(m.group(1))
                        elif s and not s.startswith(("--", "/-", "module", "prelude")) and found:
                            break
                imports[mod], files[mod] = found, os.path.relpath(path, ROOT)
                if not is_module:
                    legacy.add(mod)
    imports = {m: [i for i in ii if i in imports] for m, ii in imports.items()}
    return imports, files, legacy


def read_times():
    times = {}
    for project in PROJECTS:
        path = os.path.join(ROOT, project, ".lake", "lake-build.tsv")
        if os.path.exists(path):
            with open(path) as f:
                for line in f:
                    if not line.startswith("#"):
                        row = line.rstrip("\n").split("\t")
                        times.setdefault(row[0], (float(row[1]), float(row[2])))
    return times


def main():
    sys.setrecursionlimit(100000)
    imports, files, legacy = read_graph()
    times = read_times()
    wall = lambda m: times.get(m, (0.0, 0.0))[0]
    cpu = lambda m: times.get(m, (0.0, 0.0))[1]
    importers = defaultdict(set)
    for m, ii in imports.items():
        for i in ii:
            importers[i].add(m)

    def cone(mods):
        seen, todo = set(), list(mods)
        while todo:
            for n in importers[todo.pop()]:
                if n not in seen:
                    seen.add(n)
                    todo.append(n)
        return seen

    @lru_cache(None)
    def tail(m):  # the longest chain from m to the end of the build
        return wall(m) + max((tail(n) for n in importers[m]), default=0.0)

    @lru_cache(None)
    def head(m):  # the longest chain of m's imports, m included
        return wall(m) + max((head(i) for i in imports[m]), default=0.0)

    def resolve(arg):
        if arg in imports:
            return arg
        path = os.path.relpath(os.path.abspath(arg), ROOT)
        for m, f in files.items():
            if f == path:
                return m
        sys.exit(f"deps: no module {arg}")

    hm = lambda s: f"{s / 3600:.2f} CPU-h" if s >= 360 else f"{s / 60:.1f} CPU-min"
    args = sys.argv[1:]
    if not args or args[0] not in ("cone", "slow", "path"):
        sys.exit(__doc__)
    if args[0] == "cone":
        mods = [resolve(a) for a in args[1:]]
        down = cone(mods)
        crit = max(tail(m) for m in mods)
        print(f"an interface change of {', '.join(mods)} rebuilds {len(down)} modules, "
              f"{hm(sum(cpu(m) for m in down))}, at least {crit / 60:.1f} min on enough cores")
        m = max(mods, key=tail)
        print("its longest chain:")
        while m:
            if wall(m) >= 10:
                print(f"  {wall(m):7.0f} s  {m}")
            m = max(importers[m], key=tail) if importers[m] else None
        any_edit = sorted(m for m in down if m in legacy)
        print(f"any edit rebuilds {len(any_edit)} of them (outside the module system), "
              f"{hm(sum(cpu(m) for m in any_edit))}")
        for m in sorted(down, key=lambda m: -cpu(m))[:15]:
            print(f"  {cpu(m):7.0f} s  {m}")
    elif args[0] == "slow":
        n = int(args[1]) if len(args) > 1 else 20
        for m in sorted(imports, key=lambda m: -cpu(m))[:n]:
            ups = set()
            todo = list(imports[m])
            while todo:
                i = todo.pop()
                if i not in ups:
                    ups.add(i)
                    todo.extend(imports[i])
            print(f"{cpu(m):7.0f} s  {m}: rebuilt by {len(ups)} modules' changes")
    else:
        m = resolve(args[1]) if len(args) > 1 else max(imports, key=head)
        print(f"the longest chain of {m}: {head(m) / 60:.1f} min")
        while m:
            if wall(m) >= 10:
                print(f"  {wall(m):7.0f} s  {m}")
            m = max(imports[m], key=head) if imports[m] else None


if __name__ == "__main__":
    main()
