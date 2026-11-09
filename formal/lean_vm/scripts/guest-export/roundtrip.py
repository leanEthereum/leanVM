"""Check the exported Lean bytecode against leanVM's own disassembly of the deployed guest.

Usage: python3 -I roundtrip.py <lean_vm dir> <disasm.txt>, the dump from
`DBG_DISASM=<disasm.txt> guest-export <lean_vm dir> --check`.

Parses `Statement/Data/Bytecode*.lean` (the function table and every chunk), reassembles the
padded program, renders it in `lean_compiler::disassemble`'s format (g-powers of `K`,
`x^64 = x^4 + x^3 + x + 1`) and compares line by line with the `DBG_DISASM` dump the Rust
`compile_guest` wrote, function boundaries included. Independent of the exporter's own code.
"""

import re
import sys
from pathlib import Path

data, disasm = Path(sys.argv[1]), Path(sys.argv[2])
bc = data / "../Statement/Data"

chunks = {}
fns = []
for path in sorted(bc.glob("Bytecode*.lean")):
    text = path.read_text()
    for m in re.finditer(r"def (f\d+c\d+) : List OffsetInstruction := \[\n(.*?)\]\n", text, re.S):
        chunks[m.group(1)] = [l.strip().rstrip(",") for l in m.group(2).splitlines() if l.strip()]
    for m in re.finditer(r'def f(\d+) : CompiledFunction :=\n  ⟨"([A-Za-z0-9_]+)", (\d+), (\d+), \[([^\]]*)\]⟩', text):
        fns.append((int(m.group(1)), m.group(2), int(m.group(3)), int(m.group(4)),
                    [c.strip() for c in m.group(5).split(",") if c.strip()]))
table = (bc / "Bytecode.lean").read_text()
log_size = int(re.search(r"def logSize : ℕ := (\d+)", table).group(1))
code_len = int(re.search(r"def codeLen : ℕ := (\d+)", table).group(1))
order = re.findall(r"f(\d+)", re.search(r"def functions : List CompiledFunction := \[(.*?)\]", table, re.S).group(1))
fns.sort()
assert [str(i) for i, *_ in fns] == order, "function table order"

prog = []
for i, name, entry, length, cs in fns:
    assert entry == len(prog), (name, entry, len(prog))
    code = [op for c in cs for op in chunks[c]]
    assert len(code) == length, (name, len(code), length)
    assert all(len(chunks[c]) == 2048 for c in cs[:-1]), name
    prog.extend(code)
assert len(prog) == code_len
prog.extend([".set 0 0 0"] * ((1 << log_size) - code_len))

# g-powers of K, as the disassembler indexes them.
gmap = {}
acc = 1
for j in range(len(prog) + 512):
    gmap.setdefault(acc, j)
    carry = acc >> 63
    acc = ((acc << 1) & (2**64 - 1)) ^ (0x1B * carry)


def kfmt(c0, c1):
    if c1 == 0:
        return f"g^{gmap[c0]}" if c0 in gmap else f"0x{c0:016x}"
    return f"0x{c1:016x}{c0:016x}"


def render(op):
    t = op.split()
    k = t[0]
    n = lambda s: int(s)
    if k == ".set":
        return f"SET    fp[{t[1]}] = {kfmt(n(t[2]), n(t[3]))}"
    if k == ".xor":
        return f"XOR    fp[{t[3]}] = fp[{t[1]}] ^ fp[{t[2]}]"
    if k == ".mul":
        return f"MUL    fp[{t[3]}] = fp[{t[1]}] * fp[{t[2]}]"
    if k == ".deref":
        mode = t[4].lstrip(".")
        src = {"cell": f"fp[{t[3]}]", "pc": "g²·pc", "fp": "fp"}[mode]
        return f"DEREF  *(fp[{t[1]}]·g^{t[2]}) = {src}  [{mode.capitalize()}]"
    if k == ".jump":
        return f"JUMP   if fp[{t[1]}]≠0: pc=fp[{t[2]}], fp=fp[{t[3]}]"
    if k == ".keccak":
        m0, m1, m2, m3, tail, b8, cap, out = t[1:9]
        lay = lambda b: {"true": "odd", "false": "even"}[b]
        cells = {".one": 1, ".two": 2, ".all": 13}[t[11]]
        return (f"KECCAK fp[{out}..+{cells}] {lay(t[10])} = keccak_f(fp[{m0}],fp[{m1}],fp[{m2}],fp[{m3}], "
                f"tail=fp[{tail}..+4], b8=fp[{b8}], cap=fp[{cap}..+4]) {lay(t[9])}")
    raise ValueError(op)


rust_fns, rust_ops = [], []
for line in disasm.read_text().splitlines():
    if line.startswith("# fn "):
        m = re.match(r"# fn +(\d+)\.\.(\d+) +(\S+)", line)
        rust_fns.append((m.group(3), int(m.group(1)), int(m.group(2)) - int(m.group(1))))
    else:
        pc, ins = line.strip().split("  ", 1)
        assert int(pc.replace(",", "")) == len(rust_ops)
        rust_ops.append(ins)
assert rust_fns == [(name, entry, length) for _, name, entry, length, _ in fns], "function ranges"
assert len(rust_ops) == len(prog), (len(rust_ops), len(prog))
bad = [(pc, r, render(op)) for pc, (r, op) in enumerate(zip(rust_ops, prog)) if r != render(op)]
for b in bad[:10]:
    print("MISMATCH", *b)
counts = {}
for op in prog:
    counts[op.split()[0]] = counts.get(op.split()[0], 0) + 1
print(f"{len(fns)} functions, codeLen {code_len}, 2^{log_size} slots, {len(bad)} mismatches; {counts}")
sys.exit(1 if bad else 0)
