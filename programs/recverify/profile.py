"""Fold `recverify-host` profiles with the guest's debug info. Needs binutils' `addr2line` and `nm` (any target).

`python3 profile.py <elf with debuginfo> <PROFILE file> inner|outer [top]`: steps per function, charged to the innermost inlined frame (`inner`) or to the symbol the pc sits in (`outer`).

`python3 profile.py <elf with debuginfo> <PROFILE file> classes`: steps split into field arithmetic (any inlined frame in `primitives::field`, or the products inlined into `flock::lincheck::outer_product`), soft float (`compiler_builtins` float and `libm`), and the rest (plumbing).

`python3 profile.py <elf with debuginfo> <PROFILE_CALLS file> calls [depth] [min_percent]`: the dynamic call tree below `guest_main`, steps inclusive of callees. Edges are per caller and callee, merged over contexts.

`python3 profile.py <elf built with --cfg recguest_count> <PROFILE_CALLS file> ops`: the field operations and compressions per verifier stage, that build keeping each a call.
"""

import collections
import re
import subprocess
import sys
from pathlib import Path

elf, path, mode = sys.argv[1], sys.argv[2], sys.argv[3]


def short(name):
    while True:
        stripped = re.sub(r"<[^<>]*>", "", name)
        if stripped == name:
            return name[:150]
        name = stripped


def frames_of(pcs):
    """Per pc, its inlined frames' function names, innermost first."""
    out = subprocess.run(
        ["addr2line", "-a", "-f", "-i", "-C", "-e", elf],
        input="\n".join(hex(pc) for pc in pcs),
        capture_output=True,
        text=True,
        check=True,
    ).stdout.splitlines()
    frames = collections.defaultdict(list)
    current, offset = None, 0
    for line in out:
        if re.fullmatch(r"0x[0-9a-f]+", line):
            current, offset = int(line, 16), 0
            continue
        if offset % 2 == 0:
            frames[current].append(line)
        offset += 1
    return frames


def symbol_table(raw=False):
    symbols = {}
    for line in subprocess.run(["nm", "-C", elf], capture_output=True, text=True, check=True).stdout.splitlines():
        parts = line.split(" ", 2)
        if len(parts) == 3 and parts[1] in "tT" and not parts[2].startswith(("$", ".L")):
            symbols.setdefault(int(parts[0], 16), parts[2] if raw else short(parts[2]))
    return symbols


OPS = [
    ("E mul", "F192>::mul_unreduced"),
    ("E mul", "F192 as core::ops::arith::MulAssign>::mul_assign"),
    ("ExK", "F192>::mul_base_unreduced"),
    ("E sq", "F192>::square"),
    ("E inv", "F192>::inv"),
    ("K mul", "F64 as core::ops::arith::Mul>::mul"),
    ("K sq", "F64>::square"),
    ("K inv", "F64>::inv"),
    ("BLAKE2s", "hash::compress"),
]

if mode == "ops":
    # The counting build (`--cfg recguest_count`) keeps every field operation a call: count them per stage.
    raw = symbol_table(raw=True)
    names = symbol_table()
    op_of = {pc: label for pc, s in raw.items() for label, key in OPS if key in s}
    table = collections.defaultdict(collections.Counter)
    for line in Path(path).read_text().splitlines():
        if line.startswith("stage "):
            _, stage, substage, callee, calls = line.split()
            op = op_of.get(int(callee, 16))
            if op:
                for key in (
                    "TOTAL",
                    names.get(int(stage, 16), stage),
                    "  " + names.get(int(stage, 16), stage) + " / " + names.get(int(substage, 16), substage),
                ):
                    table[key][op] += int(calls)
    labels = list(dict.fromkeys(label for label, _ in OPS))
    print("| stage | " + " | ".join(labels) + " |")
    print("|---|" + "---:|" * len(labels))
    for key in sorted(table, key=lambda k: (k != "TOTAL", -sum(table[k].values()))):
        if key.startswith("  ") and sum(table[key].values()) < 0.01 * sum(table["TOTAL"].values()):
            continue
        print(f"| {key} | " + " | ".join(f"{table[key][label]:,}" for label in labels) + " |")
    sys.exit()

if mode == "calls":
    depth = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    min_percent = float(sys.argv[5]) if len(sys.argv) > 5 else 1.0
    lines = Path(path).read_text().splitlines()
    total = int(lines[0].split()[1])
    children = collections.defaultdict(list)
    for line in lines[1:]:
        if line and not line.startswith("stage "):
            caller, callee, inclusive, calls = line.split()
            children[int(caller, 16)].append((int(inclusive), int(calls), int(callee, 16)))
    symbols = symbol_table()
    name = lambda pc: symbols.get(pc, hex(pc))
    root = next(pc for pc, s in symbols.items() if s.endswith("guest_main"))
    print(f"total {total} steps")

    def walk(pc, level, seen):
        for inclusive, calls, callee in sorted(children[pc], reverse=True):
            if 100 * inclusive / total < min_percent or callee in seen:
                continue
            print(f"{inclusive:>14} {100 * inclusive / total:6.2f}%  {'  ' * level}{name(callee)} ({calls} calls)")
            if level + 1 < depth:
                walk(callee, level + 1, seen | {callee})

    walk(root, 0, {root})
    sys.exit()

top = int(sys.argv[4]) if len(sys.argv) > 4 else 40
counts, tables = {}, {}
for line in Path(path).read_text().splitlines():
    pc, n, table = line.split()
    counts[int(pc, 16)] = int(n)
    tables[int(pc, 16)] = table
frames = frames_of(sorted(counts))
total = sum(counts.values())
by = collections.Counter()
rows = collections.defaultdict(collections.Counter)
for pc, n in counts.items():
    fs = frames.get(pc) or ["??"]
    if mode == "inner":
        key = short(fs[0])
    elif mode == "outer":
        key = short(fs[-1])
    elif any("primitives::field::" in f or "lincheck::outer_product" in f for f in fs):
        key = "field arithmetic"
    elif any("compiler_builtins::float" in f or "libm" in f for f in fs):
        key = "soft float"
    else:
        key = "plumbing"
    by[key] += n
    rows[key][tables[pc]] += n

print(f"total {total} steps")
for key, n in by.most_common(top):
    print(f"{n:>14} {100 * n / total:6.2f}%  {key}")
if mode == "classes":
    for key in by:
        print(f"{key}: " + ", ".join(f"{table} {n}" for table, n in sorted(rows[key].items())))
