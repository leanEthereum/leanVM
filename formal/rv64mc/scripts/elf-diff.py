#!/usr/bin/env python3
"""Per-function diff of two RV64 ELFs: `python3 -I elf-diff.py OLD.elf NEW.elf [-v]`.

Each text symbol of either ELF is one of: unchanged (same bytes at the same address), moved (same bytes, another
address), changed, added, removed. The same comparison is made a second time modulo addresses: every PC-relative or
absolute reference (`jal`, branches, `auipc` and the instruction that completes it) is replaced by the symbol it
reaches, or by its section when no symbol covers it, so a function whose only difference is where things are counts
as same-modulo-addresses. Standard library only; the ELF is parsed by hand.
"""

import difflib
import struct
import sys
from collections import Counter


def read_elf(path):
    data = open(path, "rb").read()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        sys.exit(f"{path}: not a 64-bit little-endian ELF")
    e_shoff, = struct.unpack_from("<Q", data, 0x28)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 0x3A)
    sections = []
    for i in range(e_shnum):
        name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
            "<IIQQQQIIQQ", data, e_shoff + i * e_shentsize)
        sections.append(dict(name=name, type=typ, flags=flags, addr=addr, off=off, size=size, link=link,
                             entsize=entsize))
    shstr = sections[e_shstrndx]

    def cstr(sec, at):
        start = sec["off"] + at
        return data[start:data.index(b"\0", start)].decode()

    for sec in sections:
        sec["name"] = cstr(shstr, sec["name"])
    symtab = next(s for s in sections if s["type"] == 2)
    strtab = sections[symtab["link"]]
    symbols = []
    for i in range(symtab["size"] // 24):
        name, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", data, symtab["off"] + i * 24)
        if shndx == 0 or shndx >= 0xFF00:
            continue
        symbols.append(dict(name=cstr(strtab, name), type=info & 0xF, shndx=shndx, value=value, size=size))
    return data, sections, symbols


def text_functions(data, sections, symbols):
    """Text symbols as functions: name -> (address, bytes). A symbol without a size runs to the next one."""
    out = {}
    for shndx, sec in enumerate(sections):
        if not (sec["flags"] & 0x4) or sec["type"] != 1:  # SHF_EXECINSTR, PROGBITS
            continue
        syms = sorted({(s["value"], s["name"], s["size"]) for s in symbols
                       if s["shndx"] == shndx and s["type"] in (0, 2) and not s["name"].startswith((".L", "$"))
                       and s["name"]})
        starts = sorted({v for v, _, _ in syms})
        end_of_sec = sec["addr"] + sec["size"]
        for value, name, size in syms:
            if size == 0:
                later = [v for v in starts if v > value]
                size = (later[0] if later else end_of_sec) - value
            if size == 0:
                continue
            body = data[sec["off"] + value - sec["addr"]:sec["off"] + value - sec["addr"] + size]
            key, n = name, 1
            while key in out:
                n += 1
                key = f"{name}#{n}"
            out[key] = (value, body)
    return out


def locator(sections, symbols):
    """Maps an address to a position-free name: the symbol that covers it (with the offset into it), else the
    section it falls in (without offset), else 'abs'."""
    syms = sorted((s["value"], s["value"] + max(s["size"], 1), s["name"]) for s in symbols if s["name"]
                  and not s["name"].startswith((".L", "$")) and s["type"] in (0, 1, 2))
    secs = [(s["addr"], s["addr"] + s["size"], s["name"]) for s in sections if s["addr"] and s["flags"] & 0x2]

    def locate(addr):
        best = None
        for lo, hi, name in syms:
            if lo <= addr < hi and (best is None or lo > best[0]):
                best = (lo, name)
        if best is not None:
            return f"{best[1]}+{addr - best[0]}"
        for lo, hi, name in secs:
            if lo <= addr <= hi:
                return name
        return "abs"
    return locate


def sext(value, bits):
    return value - (1 << bits) if value >> (bits - 1) & 1 else value


def normalize(addr, body, locate):
    """The function's words with every address field replaced by where it points."""
    words = [struct.unpack_from("<I", body, i)[0] for i in range(0, len(body) - 3, 4)]
    out = []
    pending = {}  # register -> target high part from an auipc, until overwritten
    for i, w in enumerate(words):
        pc = addr + 4 * i
        op = w & 0x7F
        rd = (w >> 7) & 0x1F
        rs1 = (w >> 15) & 0x1F
        tok = None
        if op == 0x17:  # auipc
            pending[rd] = pc + sext(w & 0xFFFFF000, 32)
            tok = ("auipc", rd)
        elif op == 0x6F:  # jal
            imm = (((w >> 31) & 1) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1)
            tok = ("jal", rd, locate(pc + sext(imm, 21)))
        elif op == 0x63:  # branch
            imm = (((w >> 31) & 1) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3F) << 5) | (((w >> 8) & 0xF) << 1)
            tok = ("br", w & 0x01FFF07F, locate(pc + sext(imm, 13)))
        elif op in (0x13, 0x03, 0x67) and rs1 in pending:  # addi/loads/jalr completing an auipc
            tok = ("lo", w & 0x000FFFFF, locate(pending[rs1] + sext(w >> 20, 12)))
        elif op == 0x23 and rs1 in pending:  # stores completing an auipc
            imm = ((w >> 25) << 5) | ((w >> 7) & 0x1F)
            tok = ("lo", w & 0x01FFF07F, locate(pending[rs1] + sext(imm, 12)))
        if tok is None:
            tok = w
        # Any write to rd ends a pending auipc in that register (unless this was the auipc).
        if op != 0x17 and op not in (0x23, 0x63) and rd in pending:
            del pending[rd]
        out.append(tok)
    return out


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    verbose = "-v" in sys.argv
    if len(args) != 2:
        sys.exit(__doc__)
    elfs = [read_elf(p) for p in args]
    funcs = [text_functions(*e) for e in elfs]
    locs = [locator(e[1], e[2]) for e in elfs]
    old, new = funcs
    raw, norm = Counter(), Counter()
    words_changed_raw = words_changed_norm = 0
    details = []
    for name in sorted(set(old) | set(new)):
        if name not in new:
            raw["removed"] += 1
            norm["removed"] += 1
            details.append(("removed", "removed", name, 0, 0))
            continue
        if name not in old:
            raw["added"] += 1
            norm["added"] += 1
            details.append(("added", "added", name, 0, 0))
            continue
        (a0, b0), (a1, b1) = old[name], new[name]
        moved = a0 != a1
        if b0 == b1:
            r = "moved" if moved else "unchanged"
        else:
            r = "changed"
        n0, n1 = normalize(a0, b0, locs[0]), normalize(a1, b1, locs[1])
        if n0 == n1:
            n = "moved" if moved else "unchanged"
        else:
            n = "changed"
        raw[r] += 1
        norm[n] += 1
        w0 = [b0[i:i + 4] for i in range(0, len(b0), 4)]
        w1 = [b1[i:i + 4] for i in range(0, len(b1), 4)]
        dr = sum(max(i2 - i1, j2 - j1) for tag, i1, i2, j1, j2 in
                 difflib.SequenceMatcher(None, w0, w1, autojunk=False).get_opcodes() if tag != "equal")
        dn = sum(max(i2 - i1, j2 - j1) for tag, i1, i2, j1, j2 in
                 difflib.SequenceMatcher(None, n0, n1, autojunk=False).get_opcodes() if tag != "equal")
        words_changed_raw += dr
        words_changed_norm += dn
        details.append((r, n, name, dr, dn, len(w0), len(w1)))
    total = [sum(len(b) // 4 for _, b in f.values()) for f in funcs]
    print(f"functions: old {len(old)}, new {len(new)}; instruction words: old {total[0]}, new {total[1]}")
    for label, c, wc in (("raw", raw, words_changed_raw), ("modulo addresses", norm, words_changed_norm)):
        print(f"{label:>17}: " + ", ".join(f"{k} {c[k]}" for k in ("unchanged", "moved", "changed", "added", "removed"))
              + f"; words differing in matched functions {wc}")
    for d in details:
        if d[1] != "unchanged" and (verbose or d[1] != "moved"):
            extra = f" ({d[3]} raw / {d[4]} normalized words differ, {d[5]} -> {d[6]} words)" if len(d) > 5 else ""
            print(f"  [{d[0]:>9} | {d[1]:>9}] {d[2]}{extra}")


if __name__ == "__main__":
    main()
