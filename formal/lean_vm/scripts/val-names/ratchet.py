#!/usr/bin/env python3
"""No new raw value number or statement position in a hand-written proof.

    python3 -I scripts/val-names/ratchet.py [--write]

Counts, per hand-written Lean file of `lean_vm` (tracked, outside comments), the raw value numbers
(`.n 28`, `V.n 28`, `.n (23 + k)`) and the statement positions of two digits or more (`.drop 765`,
`.take 31`, `.getD 615`) it spells, and fails when a file's count is above its row in
`scripts/val-names/ratchet.tsv`, or a file not there spells one: name them (`val%`, `valf%`, `pos%`,
`span%`, `scripts/val-names/rewrite.py`), and when a count is below its row, so the rows stay exact:
`--write` rewrites them from the tree after a conversion lowers them, never to admit a new numeral. Exempt: the core
route's contracts (`Guest/CoreMode/Sig/`, which `sigc.py` keeps as written) and the hand files a
generator copies or rewraps (`EXEMPT`), which stay numeric. Run from `lean_vm`.
"""
import os, re, subprocess, sys

BASE = os.path.join("scripts", "val-names", "ratchet.tsv")
EXEMPT_DIRS = ("LeanVM/Guest/Data/", "LeanVM/Guest/CoreMode/Sig/")
# copied into generated files (`genplacedE.py`) or holding a generated region (`whir-queries`), and
# the generated whole files that are committed
EXEMPT = {
    "LeanVM/Guest/B1/Opening/QueriesPlacedD0.lean", "LeanVM/Guest/B1/Opening/QueriesPlacedD1.lean",
    "LeanVM/Guest/B1/Opening/QueriesPlacedD2.lean", "LeanVM/Guest/B1/Opening/QueriesFns.lean",
    "LeanVM/Guest/B1/Opening/QueriesT.lean", "LeanVM/Guest/B1/Opening/Witness.lean",
    "LeanVM/Guest/B1/Opening/Interface.lean", "LeanVM/Guest/B1/Bits/QueryWindowsT.lean",
    "LeanVM/Guest/B1/Bits/QueryWindowsBody0.lean", "LeanVM/Guest/B1/Bits/QueryWindowsBody1.lean",
    "LeanVM/Protocol/ToArkLib/Whir/AffineCombinerDeployedTable.lean",
    "tests/LeanVMTests/Guest/Programs.lean",
}
VAL = re.compile(r'(?<![\w.\'])(?:V\.n|\.n)\s+\(?\s*\d')
POS = re.compile(r'(?<![\w\'])\.(?:drop|take|getD)\s+\d{2,}(?![\w.])')


def strip(t):
    """The text without comments and strings (`--`, `/- … -/` nested, `"…"`)."""
    out, i, n, depth = [], 0, len(t), 0
    while i < n:
        if t.startswith("/-", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if t.startswith("/-", j): depth, j = depth + 1, j + 2
                elif t.startswith("-/", j): depth, j = depth - 1, j + 2
                else: j += 1
            out.append(" "); i = j
        elif t.startswith("--", i):
            j = t.find("\n", i)
            i = n if j < 0 else j
        elif t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == "\\" else 1
            out.append('""'); i = j + 1
        else:
            out.append(t[i]); i += 1
    return "".join(out)


def counts():
    files = subprocess.run(["git", "ls-files", "LeanVM/*.lean", "tests/*.lean"], check=True,
                           capture_output=True, text=True).stdout.split()
    out = {}
    for f in files:
        if f.startswith(EXEMPT_DIRS) or f in EXEMPT:
            continue
        t = strip(open(f, encoding="utf-8").read())
        v, p = len(VAL.findall(t)), len(POS.findall(t))
        if v or p:
            out[f] = (v, p)
    return out


def main():
    now = counts()
    if "--write" in sys.argv:
        with open(BASE, "w", encoding="utf-8") as h:
            h.write("# file\traw value numbers\tpositions (scripts/val-names/ratchet.py --write; never raised by hand)\n")
            for f in sorted(now):
                h.write(f"{f}\t{now[f][0]}\t{now[f][1]}\n")
        print(f"ratchet: {sum(v for v, _ in now.values())} value numbers, {sum(p for _, p in now.values())} positions in {len(now)} files")
        return 0
    base = {}
    for l in open(BASE, encoding="utf-8"):
        if l.startswith("#") or not l.strip(): continue
        f, v, p = l.rstrip("\n").split("\t")
        base[f] = (int(v), int(p))
    bad, low = [], 0
    for f, (v, p) in sorted(now.items()):
        bv, bp = base.get(f, (0, 0))
        if v > bv or p > bp:
            bad.append(f"{f}: {v} raw value numbers (at most {bv}), {p} positions (at most {bp})")
        elif (v, p) != (bv, bp):
            low += 1
    low += sum(1 for f in base if f not in now)
    if bad:
        print("ratchet: new raw numerals; name them (val%, pos%, span%: scripts/val-names/rewrite.py):\n  " + "\n  ".join(bad), file=sys.stderr)
        return 1
    if low:
        print(f"ratchet: {low} files below their row; lower the rows: scripts/val-names/ratchet.py --write", file=sys.stderr)
        return 1
    print(f"ratchet: no new raw numeral ({sum(v for v, _ in now.values())} value numbers, {sum(p for _, p in now.values())} positions in {len(now)} files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
