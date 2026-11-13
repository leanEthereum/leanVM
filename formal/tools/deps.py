#!/usr/bin/env python3
"""What an edit rebuilds, from the import graph of the six projects and the recorded build times.

  python3 -I tools/deps.py cone MODULE|FILE ...   what changing these modules' interface rebuilds
  python3 -I tools/deps.py slow [N]               the N slowest modules, and what rebuilds them
  python3 -I tools/deps.py path [MODULE]          the longest chain of a full build (of MODULE)

Times are the last builds' (`*/.lake/lake-build.tsv`, written by `lake-build.py`, which records
every module it builds, the dependencies' included); a module without one counts as 0 s.

Lake's rule (`Lake/Build/Module.lean`, `ModuleImportInfo.addImport`): a `module` file's trace holds,
for each of its imports, that module's public olean and those of the modules it imports with
`public import`, transitively (its public closure); a `meta import` brings in everything below it, and
`import all` the module's private part and its own imports' closures. A file outside the module
system sees everything below it, private parts included. So a module rebuilds when a module it sees
changes what it exports (a statement, an exposed body, a declaration added or removed, its list of
imports), and a private `import` is a firewall: what imports the importer does not see behind it.
A proof, a comment or a private declaration changes nothing a `module` file exports, and rebuilds
only the files outside the module system that see it (and `import all` importers). `cone` lists
both, and the rebuilt modules by family; `tools/firewall-canary.py` checks the rule against Lake.
"""
import os
import re
import sys
from collections import defaultdict
from functools import lru_cache

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROJECTS = ["Statement", "common", "lean_xmss", "lean_sphincs", "lean_da", "lean_vm"]
IMPORT = re.compile(r"^(public\s+)?(meta\s+)?import\s+(all\s+)?(\S+)")


def module_name(project, path):
    """`Statement/X.lean` is `Statement.X`; elsewhere a module is named from its project's
    source directory (`tests/` for the tests, `cli/` for the executables)."""
    rel = os.path.relpath(path, ROOT if project == "Statement" else os.path.join(ROOT, project))
    rel = rel[:-len(".lean")]
    for src in ("tests/", "cli/"):
        if rel.startswith(src):
            rel = rel[len(src):]
    return rel.replace("/", ".")


def read_graph(root=None):
    """Each module's imports as `(module, public, meta, all)`, its file, and the files outside the
    module system (whose imports all count as public)."""
    root = root or ROOT
    edges, files, legacy = {}, {}, set()
    for project in PROJECTS:
        for top, dirs, names in os.walk(os.path.join(root, project)):
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
                            found.append((m.group(4), bool(m.group(1)), bool(m.group(2)), bool(m.group(3))))
                        elif s and not s.startswith(("--", "/-", "module", "prelude")) and found:
                            break
                edges[mod], files[mod] = found, os.path.relpath(path, root)
                if not is_module:
                    legacy.add(mod)
    edges = {m: [(i, p or m in legacy, me, a) for i, p, me, a in ii if i in edges] for m, ii in edges.items()}
    return edges, files, legacy


class Graph:
    def __init__(self, edges, legacy):
        self.edges, self.legacy = edges, legacy
        self.imports = {m: [e[0] for e in ii] for m, ii in edges.items()}
        self.importers = defaultdict(set)
        for m, ii in self.imports.items():
            for i in ii:
                self.importers[i].add(m)

    def below(self, srcs):
        """Every module that imports one of `srcs`, directly or not."""
        seen, todo = set(srcs), list(srcs)
        while todo:
            for n in self.importers[todo.pop()]:
                if n not in seen:
                    seen.add(n)
                    todo.append(n)
        return seen

    def public_holders(self, srcs, allx):
        """The modules whose public closure holds one of `srcs`: `srcs`, and what imports one of
        them publicly, or with `public meta import` anything in `allx`."""
        out, todo = set(srcs), list(srcs)
        for m, ii in self.edges.items():
            if m not in out and any(p and me and i in allx for i, p, me, _ in ii):
                out.add(m)
                todo.append(m)
        while todo:
            x = todo.pop()
            for n in self.importers[x]:
                if n not in out and any(i == x and p and not me for i, p, me, _ in self.edges[n]):
                    out.add(n)
                    todo.append(n)
        return out

    def cone(self, srcs, any_edit=False):
        """What an interface change of `srcs` rebuilds (with `any_edit`, a change of anything in
        them: a proof, a private declaration), by Lake's rule."""
        srcs = set(srcs)
        full = self.below(srcs)  # whose full closure holds a source
        pub = self.public_holders(srcs, full)
        # whose `import all` closure holds a source
        alls, changed = set(srcs), True
        while changed:
            changed = False
            for m, ii in self.edges.items():
                if m not in alls and any((a and i in alls) or (me and i in full) or (not a and not me and i in pub)
                                         for i, _, me, a in ii):
                    alls.add(m)
                    changed = True
        out = set()
        for z, ii in self.edges.items():
            if z in srcs:
                continue
            if z in self.legacy:
                if z in full:
                    out.add(z)
            elif any((a and i in alls) or (not any_edit and ((me and i in full) or (not a and not me and i in pub)))
                     for i, _, me, a in ii):
                out.add(z)
        return out

    def sees(self, m):
        """The modules whose interface change rebuilds `m`."""
        full, pub, alls = 0, 1, 2
        if m in self.legacy:
            start = [(i, full) for i in self.imports[m]]
        else:
            start = [(i, alls if a else full if me else pub) for i, _, me, a in self.edges[m]]
        seen, todo = set(start), list(start)
        while todo:
            x, mode = todo.pop()
            for i, p, me, a in self.edges[x]:
                if mode == full or (mode == pub and p and me) or (mode == alls and me and not a):
                    nxt = (i, full)
                elif mode == alls:
                    nxt = (i, alls if a else pub)
                elif mode == pub and p:
                    nxt = (i, pub)
                else:
                    continue
                if nxt not in seen:
                    seen.add(nxt)
                    todo.append(nxt)
        return {x for x, _ in seen}


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


def family(m):
    """`LeanVM.Guest.B2C.Cplw.C24_0_0` is `LeanVM.Guest.B2C.Cplw`: a module's directory."""
    parts = m.split(".")
    return ".".join(parts[:-1]) or m


def main():
    sys.setrecursionlimit(100000)
    edges, files, legacy = read_graph()
    g = Graph(edges, legacy)
    times = read_times()
    wall = lambda m: times.get(m, (0.0, 0.0))[0]
    cpu = lambda m: times.get(m, (0.0, 0.0))[1]

    def resolve(arg):
        if arg in edges:
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
        down = g.cone(mods)
        rebuilt = down | set(mods)

        @lru_cache(None)
        def tail(m):  # the longest chain from m to the end of the rebuild
            return wall(m) + max((tail(n) for n in g.importers[m] if n in rebuilt), default=0.0)

        crit = max(tail(m) for m in mods)
        print(f"an interface change of {', '.join(mods)} rebuilds {len(down)} modules, "
              f"{hm(sum(cpu(m) for m in down))}, at least {crit / 60:.1f} min on enough cores")
        print("its longest chain:")
        m = max(mods, key=tail)
        while m:
            if wall(m) >= 10:
                print(f"  {wall(m):7.0f} s  {m}")
            nxt = [n for n in g.importers[m] if n in rebuilt]
            m = max(nxt, key=tail) if nxt else None
        fams = defaultdict(lambda: [0, 0.0])
        for m in down:
            fams[family(m)][0] += 1
            fams[family(m)][1] += cpu(m)
        print("by family:")
        for f, (n, t) in sorted(fams.items(), key=lambda kv: -kv[1][1])[:12]:
            print(f"  {t:7.0f} s  {n:5d}  {f}")
        any_edit = sorted(g.cone(mods, any_edit=True))
        print(f"any edit rebuilds {len(any_edit)} of them (outside the module system, or `import all`), "
              f"{hm(sum(cpu(m) for m in any_edit))}")
        for m in sorted(down, key=lambda m: -cpu(m))[:15]:
            print(f"  {cpu(m):7.0f} s  {m}")
    elif args[0] == "slow":
        n = int(args[1]) if len(args) > 1 else 20
        for m in sorted(edges, key=lambda m: -cpu(m))[:n]:
            print(f"{cpu(m):7.0f} s  {m}: rebuilt by {len(g.sees(m))} modules' changes")
    else:
        @lru_cache(None)
        def head(m):  # the longest chain of m's imports, m included
            return wall(m) + max((head(i) for i in g.imports[m]), default=0.0)

        m = resolve(args[1]) if len(args) > 1 else max(edges, key=head)
        print(f"the longest chain of {m}: {head(m) / 60:.1f} min")
        while m:
            if wall(m) >= 10:
                print(f"  {wall(m):7.0f} s  {m}")
            m = max(g.imports[m], key=head) if g.imports[m] else None


if __name__ == "__main__":
    main()
