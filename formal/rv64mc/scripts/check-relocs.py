#!/usr/bin/env python3
"""Checks that the guest's relocations (linked with `--emit-relocs`) pair every address computation exactly:
`python3 -I check-relocs.py ELF`. Uses riscv64-unknown-elf-readelf and -objdump.

- Every `auipc` in `.text` carries exactly one relocation: `R_RISCV_CALL_PLT` (a call, the `jalr` after it) or
  `R_RISCV_PCREL_HI20` (an address, completed by the `R_RISCV_PCREL_LO12_I/S` users that name its label), except a
  call from a function to its own entry, which the assembler resolves (a fixed offset within the function).
- A call's `jalr` reads the `auipc`'s register, and the pair computes the relocation's target.
- Each `PCREL_LO12` user reads the register its `auipc` wrote and, with it, computes the target of that `auipc`'s
  `HI20`.
- No other relocation lands in `.text`, and none is a relaxation (`R_RISCV_RELAX`, `R_RISCV_ALIGN`).
- Every `R_RISCV_64` in a data section holds its target.
"""

import collections
import re
import struct
import subprocess
import sys

elf = sys.argv[1]


def run(*args):
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout


def sext(v, bits):
    return v - (1 << bits) if v >> (bits - 1) & 1 else v


relocs = collections.defaultdict(list)  # section -> [(offset, type, symvalue, addend)]
section = None
for line in run("riscv64-unknown-elf-readelf", "-r", "-W", elf).splitlines():
    m = re.match(r"Relocation section '\.rela(\S+)'", line)
    if m:
        section = m.group(1)
        continue
    m = re.match(r"^([0-9a-f]{16})\s+[0-9a-f]+\s+(R_RISCV_\w+)\s+([0-9a-f]+)\s+(.*?)\s*([+-])\s*([0-9a-f]+)$", line)
    if m:
        addend = int(m.group(6), 16) * (1 if m.group(5) == "+" else -1)
        relocs[section].append((int(m.group(1), 16), m.group(2), int(m.group(3), 16), addend, m.group(4)))

words = {}  # text address -> instruction word
for line in run("riscv64-unknown-elf-objdump", "-d", "-j", ".text", elf).splitlines():
    m = re.match(r"^\s+([0-9a-f]+):\s+([0-9a-f]{8})\s", line)
    if m:
        words[int(m.group(1), 16)] = int(m.group(2), 16)

errors = []
types = collections.Counter(t for rs in relocs.values() for _, t, _, _, _ in rs)
for t in ("R_RISCV_RELAX", "R_RISCV_ALIGN"):
    if types[t]:
        errors.append(f"{types[t]} {t}: the link relaxed")

text = {off: (t, s, a, n) for off, t, s, a, n in relocs[".text"]}
if len(text) != len(relocs[".text"]):
    errors.append("two relocations at one .text address")
auipcs = {a: w for a, w in words.items() if w & 0x7F == 0x17}
rd = lambda w: w >> 7 & 31
rs1 = lambda w: w >> 15 & 31
funcs = []  # (start, end) of each sized function symbol
for line in run("riscv64-unknown-elf-readelf", "-s", "-W", elf).splitlines():
    f = line.split()
    if len(f) >= 8 and f[3] == "FUNC" and int(f[2], 0) > 0:
        funcs.append((int(f[1], 16), int(f[1], 16) + int(f[2], 0)))
own = lambda a: next(((s, e) for s, e in funcs if s <= a < e), None)
hi_target = {}
self_calls = 0
for a, w in auipcs.items():
    j = words.get(a + 4, 0)
    if a not in text and j & 0x707F == 0x67 and rs1(j) == rd(w):
        target = a + sext(w & 0xFFFFF000, 32) + sext(j >> 20, 12)
        if own(a) is not None and own(a)[0] == target:
            self_calls += 1
            continue
    if a not in text or text[a][0] not in ("R_RISCV_CALL_PLT", "R_RISCV_PCREL_HI20"):
        errors.append(f"auipc at {a:#x} without a CALL_PLT or PCREL_HI20 relocation")
        continue
    t, s, add, _ = text[a]
    target = s + add
    base = a + sext(w & 0xFFFFF000, 32)
    if t == "R_RISCV_CALL_PLT":
        j = words.get(a + 4, 0)
        if j & 0x707F != 0x67 or rs1(j) != rd(w) or base + sext(j >> 20, 12) != target:
            errors.append(f"call at {a:#x}: the jalr after it does not reach {target:#x}")
    else:
        hi_target[a] = (target, base, rd(w))
users = collections.Counter()
for off, (t, s, add, name) in text.items():
    if t in ("R_RISCV_CALL_PLT", "R_RISCV_PCREL_HI20"):
        if off not in auipcs:
            errors.append(f"{t} at {off:#x} is not on an auipc")
        continue
    if t not in ("R_RISCV_PCREL_LO12_I", "R_RISCV_PCREL_LO12_S"):
        errors.append(f"unexpected {t} at {off:#x}")
        continue
    if s not in hi_target:
        errors.append(f"{t} at {off:#x} names {s:#x}, which has no PCREL_HI20")
        continue
    target, base, reg = hi_target[s]
    w = words[off]
    imm = sext(w >> 20, 12) if t.endswith("_I") else sext((w >> 25) << 5 | (w >> 7 & 31), 12)
    if rs1(w) != reg or base + imm != target:
        errors.append(f"{t} at {off:#x} does not complete {s:#x} to {target:#x}")
    users[s] += 1
for a in hi_target:
    if users[a] == 0:
        errors.append(f"PCREL_HI20 at {a:#x} has no user")

data = open(elf, "rb").read()
sections = {}
for line in run("riscv64-unknown-elf-readelf", "-S", "-W", elf).splitlines():
    m = re.match(r"^\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
    if m:
        sections[m.group(1)] = (int(m.group(2), 16), int(m.group(3), 16))
for sec, rs in relocs.items():
    if sec == ".text":
        continue
    addr, off = sections[sec]
    for o, t, s, add, _ in rs:
        if t != "R_RISCV_64":
            errors.append(f"unexpected {t} in {sec}")
        elif struct.unpack_from("<Q", data, off + o - addr)[0] != (s + add) % 2**64:
            errors.append(f"R_RISCV_64 at {o:#x} does not hold its target")

print(f"{len(auipcs)} auipc: {types['R_RISCV_CALL_PLT']} calls, {self_calls} self-calls without relocation, {len(hi_target)} addresses with "
      f"{sum(users.values())} lo12 users ({sum(1 for n in users.values() if n > 1)} with several); "
      f"{sum(len(rs) for s, rs in relocs.items() if s != '.text')} absolute data words")
if errors:
    print("\n".join(errors[:50]))
    sys.exit(f"{len(errors)} errors")
