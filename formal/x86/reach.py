#!/usr/bin/env python3
"""What the x86 proofs have to cover: the functions reachable from the entry point in a binary that `build.sh` wrote.

Usage: reach.py BINARY [--entry SYMBOL] [--assume NAME ...] [--list CRATE ...] [--why NAME]

It follows direct calls and jumps, functions whose address the code takes, and function pointers in the data the code
reads (vtables), stopping at the assumed functions (the pool's machinery by default) and at the dynamic library's
(PLT). It prints the reachable code by crate, the library functions reached, the indirect calls, and the functions of
the crates `--list` names (by default the standard library's).
"""

import argparse
import bisect
import collections
import re
import subprocess

ASSUMED = ["stable_parallel::dispatch", "stable_parallel::num_threads"]
STD = ["std", "core", "alloc", "hashbrown", "std_detect", "compiler_builtins"]


def run(*cmd):
    return subprocess.run(cmd, check=True, capture_output=True, text=True).stdout


def functions(binary):
    """Function start -> (end, mangled name, demangled name)."""
    rows = [l.split(maxsplit=3) for l in run("nm", "-S", "--defined-only", binary).splitlines()]
    rows = [r for r in rows if len(r) == 4 and r[2] in "tTwW" and int(r[1], 16) > 0]
    pretty = subprocess.run(
        ["c++filt"], input="\n".join(r[3] for r in rows), check=True, capture_output=True, text=True
    ).stdout.splitlines()
    return {int(r[0], 16): (int(r[0], 16) + int(r[1], 16), r[3], p) for r, p in zip(rows, pretty)}


def sections(binary):
    """(start, bytes) of each allocated data section, for reading function pointers."""
    out = []
    current = None
    for line in run("objdump", "-s", "-j", ".rodata", "-j", ".data.rel.ro", "-j", ".data", binary).splitlines():
        if line.startswith("Contents of section"):
            current = None
            continue
        m = re.match(r"^ ([0-9a-f]+) ((?:[0-9a-f]{2,8} ){1,4})", line)
        if not m:
            continue
        addr, data = int(m.group(1), 16), bytes.fromhex(m.group(2).replace(" ", ""))
        if current and current[0] + len(current[1]) == addr:
            current[1].extend(data)
        else:
            current = (addr, bytearray(data))
            out.append(current)
    return out


def word_at(data, addr):
    for start, blob in data:
        if start <= addr and addr + 8 <= start + len(blob):
            return int.from_bytes(blob[addr - start : addr - start + 8], "little")
    return None


def plain(name):
    """A demangled name without its crates' disambiguators and its hash."""
    return re.sub(r"::h[0-9a-f]{16}$", "", re.sub(r"\[[0-9a-f]{6,16}\]", "", name))


def crate(name):
    """The first path's crate: `core` for `<[u8] as core::cmp::PartialEq>::eq`."""
    m = re.search(r"([a-z_][a-z0-9_]*)::", name)
    return m.group(1) if m else "?"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("binary")
    ap.add_argument("--entry", default="leanvm_fv_prove")
    ap.add_argument("--assume", nargs="*", default=ASSUMED, help="demangled names without their hash, a trailing * for a prefix")
    ap.add_argument("--list", nargs="*", default=STD, help="crates whose reachable functions to list")
    ap.add_argument("--why", help="print a call path from the entry to a function or library symbol by that name")
    args = ap.parse_args()

    funcs = functions(args.binary)
    starts = sorted(funcs)
    funcs = {f: (end, raw, plain(pretty)) for f, (end, raw, pretty) in funcs.items()}
    by_name = lambda f: funcs[f][2]
    data = sections(args.binary)

    def owner(addr):
        i = bisect.bisect_right(starts, addr) - 1
        return starts[i] if i >= 0 and addr < funcs[starts[i]][0] else None

    # Per function: its instructions, the functions and PLT stubs it reaches, its indirect calls, the data it reads.
    insns = collections.Counter()
    edges = collections.defaultdict(set)
    plt = collections.defaultdict(set)
    indirect = collections.Counter()
    loops = collections.Counter()  # backward jumps within the function: each a loop to give an invariant
    op_at = {}  # the mnemonic at each address, to tell a loop from a jump back to a shared abort
    mnemonics = collections.defaultdict(set)
    refs = collections.defaultdict(set)
    current = None
    for line in run("objdump", "-d", "--no-show-raw-insn", "-M", "intel", args.binary).splitlines():
        m = re.match(r"^([0-9a-f]+) <(.*)>:$", line)
        if m:
            current = int(m.group(1), 16) if int(m.group(1), 16) in funcs else None
            if m.group(2).endswith("@plt"):
                current = None
            continue
        m = re.match(r"^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if not m or current is None:
            continue
        op, operands = m.group(2), m.group(3)
        insns[current] += 1
        mnemonics[current].add(op)
        op_at[int(m.group(1), 16)] = op
        if op.startswith("j"):
            back = re.match(r"^([0-9a-f]+) <", operands)
            target = int(back.group(1), 16) if back else None
            if target is not None and current <= target < int(m.group(1), 16) and op_at.get(target) != "ud2":
                loops[current] += 1
        if op.startswith(("call", "j")):
            t = re.match(r"^([0-9a-f]+) <([^>]*)>", operands)
            lib = re.search(r"<([\w.]+)@(?:plt|GLIBC[\w.]*)>", operands)  # through the PLT or the GOT
            if lib:
                plt[current].add(lib.group(1))
            elif t:
                if int(t.group(1), 16) in funcs and int(t.group(1), 16) != current:
                    edges[current].add(int(t.group(1), 16))
            elif op.startswith("call") or ("QWORD PTR" in operands and "*8" not in operands):
                indirect[current] += 1  # a call, or a tail call through memory; `jmp [reg*8+table]` is a switch
        # Any address the instruction names: a function's (taken) or data (read).
        for a in re.findall(r"(?:0x|# )([0-9a-f]{5,})", operands):
            a = int(a, 16)
            if a in funcs and a != current:
                edges[current].add(a)
            elif owner(a) is None:
                refs[current].add(a)

    def is_assumed(name):
        return any(name == a or a.endswith("*") and name.startswith(a[:-1]) for a in args.assume)

    assumed = {f for f in funcs if is_assumed(by_name(f))}
    entry = [f for f in funcs if funcs[f][1] == args.entry or by_name(f) == args.entry]
    if not entry:
        raise SystemExit(f"no function {args.entry}")
    def table_functions(a, out, depth):
        """The functions a table at `a` points to: a vtable (a drop function or null, size, align, then methods), or
        an array of such pointers, following pointers to other tables one level down."""
        for k in range(64):
            w = word_at(data, a + 8 * k)
            if w is None:
                return
            if w in funcs:
                out.add(w)
            elif depth < 1 and word_at(data, w) is not None:
                table_functions(w, out, depth + 1)
            elif not (k == 0 and w == 0 or k in (1, 2) and w < 1 << 32):
                return

    parent = {f: None for f in entry}
    todo = collections.deque(entry)
    while todo:
        f = todo.popleft()
        if f in assumed:
            continue
        nexts = set(edges[f])
        for a in refs[f]:
            table_functions(a, nexts, 0)
        for g in sorted(nexts - parent.keys()):
            parent[g] = f
            todo.append(g)
    seen = set(parent)

    if args.why:
        hits = [f for f in seen if args.why in by_name(f)] or [f for f in seen - assumed if args.why in plt[f]]
        if not hits:
            raise SystemExit(f"nothing reachable matches {args.why}")
        path, f = [], min(hits, key=lambda f: len(by_name(f)))
        while f is not None:
            path.append(by_name(f)[:160])
            f = parent[f]
        print("\n  -> ".join(reversed(path)) + (f"\n  -> {args.why}" if args.why not in path[0] else ""))
        return

    proved = seen - assumed
    per_crate = collections.Counter()
    for f in proved:
        per_crate[crate(funcs[f][2])] += insns[f]
    total = sum(per_crate.values())
    assumed_reached = ", ".join(sorted(by_name(f) for f in seen & assumed)) or "none"
    print(f"entry {args.entry}: {len(proved)} functions, {total} instructions to prove; assumed: {assumed_reached}")
    print(
        f"loops {sum(loops[f] for f in proved)}, indirect calls {sum(indirect[f] for f in proved)}, "
        f"distinct mnemonics {len(set().union(*(mnemonics[f] for f in proved)))}"
    )
    print("\n## instructions by crate")
    for c, n in per_crate.most_common():
        print(f"{n:8} {c}")
    print("\n## dynamic library functions reached")
    print(" ".join(sorted({s for f in proved for s in plt[f]})) or "none")
    print("\n## indirect calls (sites per function)")
    for f in sorted(proved, key=lambda f: -indirect[f]):
        if indirect[f]:
            print(f"{indirect[f]:4} {by_name(f)[:150]}")
    print(f"\n## functions of {', '.join(args.list)}")
    for f in sorted(proved, key=lambda f: -insns[f]):
        if crate(funcs[f][2]) in args.list:
            print(f"{insns[f]:6} {by_name(f)[:150]}")


if __name__ == "__main__":
    main()
