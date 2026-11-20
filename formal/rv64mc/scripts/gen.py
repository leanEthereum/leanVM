#!/usr/bin/env python3
"""Writes the relocatable templates of every function of the guest's image and the link step that ties them to it.

  python3 -I gen.py --elf ELF --mc MCDIR [--lean-elf PATH] [--out DIR] [--check]
  python3 -I gen.py --diff OLD_HASHES [NEW_HASHES]

ELF is the guest, linked with `--emit-relocs`; MCDIR is the namespace directory `decompile --to lean --proved ELF OUT NS`
wrote (`OUT/NS`, holding `Words.lean` and `F<i>.lean`). PATH is the ELF as `Words.lean`'s `check_elf_words` reads it,
from the Lake package's directory (default `out/gen.elf`). Under DIR (default `Rv64mc/Gen`, beside it `Gen.lean`):

- `Tmpl/<M>.lean`, per function, keyed by its demangled name without crate disambiguators: a structure `Link` of every
  value of the lift that depends on where code and data sit (each callee's index and entry, each call site's `auipc`
  value and `jalr` offset, each data reference's `auipc` value, `lo12` offset and address, the return addresses as
  `L.base + k`), `tmpl L`, the lift with those values `L`'s, and `Link.WF`, what the link step proves of them. It names
  no address or index, so it changes only when the function's own code or its callees' names do.
- `Link/<M>.lean`, per function: the image's `link : Link`, `tmpl_eq : (liftProg fns)[i]? = some (tmpl link)` and
  `wf : Link.WF (liftProg fns) link`, both checked by the kernel.
- `Words.lean` (machine-checked's, in this namespace), `Index.lean` (module, symbol, index, address and size of each
  function, checked against `words`), `Image.lean` (the end statement's `Rv64mc.image`, read from the ELF by
  `Rv64mc/ImageOfElf.lean` when built), the umbrellas `Tmpl.lean`, `Link.lean` and `../Gen.lean`, `hashes.tsv` (a hash
  of each template) and `index.tsv`.

Only files whose text changes are rewritten, and files of functions that are gone are removed. The generator fails on
anything it cannot make relocatable: a call with more than one candidate, an instruction lifted to `abort`, an `auipc`
without its relocation, an address left in a template. `--check` writes nothing and exits 1 if a file would change.
`--diff` prints the templates that changed, were added or were removed between two `hashes.tsv`.
"""

import argparse
import collections
import hashlib
import json
import os
import re
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import v0demangle  # noqa: E402

R_RISCV_64, R_CALL_PLT, R_HI20, R_LO12_I, R_LO12_S = 2, 19, 23, 24, 25
R_ALIGN, R_RELAX = 43, 51
MASK = (1 << 64) - 1
NS = "Rv64mc.Gen"


def fail(msg):
    sys.exit(f"gen.py: {msg}")


def sext(v, bits):
    return v - (1 << bits) if v >> (bits - 1) & 1 else v


def sha(b):
    return hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()


# ---------------------------------------------------------------- the ELF


class Elf:
    def __init__(self, data):
        if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1 or struct.unpack_from("<H", data, 18)[0] != 243:
            fail("not a little-endian RISC-V ELF64")
        self.data = data
        (shoff,) = struct.unpack_from("<Q", data, 40)
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 58)
        raw = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * shentsize) for i in range(shnum)]
        strtab = raw[shstrndx]
        name = lambda off, tab: data[tab[4] + off : data.index(b"\0", tab[4] + off)].decode()
        self.sections = []
        for r in raw:
            self.sections.append(dict(name=name(r[0], strtab), type=r[1], flags=r[2], addr=r[3], off=r[4], size=r[5],
                                      link=r[6], info=r[7], entsize=r[9]))
        self.symbols = []
        for s in self.sections:
            if s["type"] == 2:
                tab = raw[s["link"]]
                for k in range(s["size"] // 24):
                    st_name, info, _, shndx, value, size = struct.unpack_from("<IBBHQQ", data, s["off"] + 24 * k)
                    self.symbols.append(dict(name=name(st_name, tab), type=info & 15, bind=info >> 4, shndx=shndx,
                                             value=value, size=size))
        self.relocs = collections.defaultdict(list)  # target section name -> [(offset, type, symbol, addend)]
        for s in self.sections:
            if s["type"] == 4:
                tgt = self.sections[s["info"]]["name"]
                for k in range(s["size"] // 24):
                    off, info, addend = struct.unpack_from("<QQq", data, s["off"] + 24 * k)
                    self.relocs[tgt].append((off, info & 0xFFFFFFFF, self.symbols[info >> 32], addend))

    def section(self, name):
        for s in self.sections:
            if s["name"] == name:
                return s
        fail(f"no section {name}")

    def section_at(self, addr):
        for i, s in enumerate(self.sections):
            if s["flags"] & 2 and s["addr"] <= addr < s["addr"] + max(s["size"], 1):
                return i, s
        return None, None

    def read(self, addr, n):
        _, s = self.section_at(addr)
        if s is None or addr + n > s["addr"] + s["size"]:
            fail(f"no bytes at {addr:#x}+{n}")
        if s["type"] == 8:
            return b"\0" * n
        o = s["off"] + addr - s["addr"]
        return self.data[o : o + n]


# ---------------------------------------------------------------- names

LEAN_RESERVED = {"Type", "Prop", "Sort", "Link"}
KEYWORDS = set(
    "at by do fun if in let then else match with from have show open end where deriving instance structure class def "
    "theorem import namespace section variable universe mut for return try catch finally unless break continue macro "
    "syntax local private protected partial unsafe noncomputable mutual example abbrev opaque axiom inductive extends "
    "calc suffices obtain nomatch nofun this sorry forall exists notation infix infixl infixr prefix postfix elab "
    "attribute export omit include termination_by decreasing_by using only next case exact apply intro rfl simp "
    "generalizing says set_option".split()
)


def cap(s):
    return s if len(s) <= 40 else s[:24] + "H" + sha(s)[:8]


def stable_name(sym):
    """(key, module components, instantiating crate) of a symbol."""
    if sym.startswith("_R"):
        try:
            tree, inst = v0demangle.parse(sym)
            key = v0demangle.key(tree)
            comps = v0demangle.components(tree, cap)
        except ValueError as e:
            fail(f"cannot demangle {sym}: {e}")
        if inst:
            key += f" @{inst}"
        return key, comps, inst
    if sym.startswith("_Z"):
        fail(f"Itanium-mangled symbol {sym}")
    return sym, [v0demangle.camel(sym)], None


def lean_comps(comps):
    return [c + "_" if c in LEAN_RESERVED else c for c in comps]


def field_ident(s):
    return f"«{s}»" if s in KEYWORDS else s


def lower1(s):
    return s[:1].lower() + s[1:]


def comment_safe(s):
    return s.replace("-/", "- /").replace("/-", "/ -")


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


# ---------------------------------------------------------------- m-c's output

ITEM_SPLIT = re.compile(r"\s+")


def list_items(s, i):
    """The elements of the list literal starting at `s[i] == '['`, flattening nested list literals; and the index
    after it."""
    assert s[i] == "["
    depth, start, j = 0, i + 1, i + 1
    out = []
    while True:
        c = s[j]
        if c in "([":
            if depth == 0 and c == "[" and s[start:j].strip() == "":
                sub, j = list_items(s, j)
                out.extend(sub)
                start = j
                continue
            depth += 1
        elif c in ")]":
            if depth == 0:
                assert c == "]"
                t = s[start:j].strip()
                if t:
                    out.append(t)
                return out, j + 1
            depth -= 1
        elif c == "," and depth == 0:
            t = s[start:j].strip()
            if t:
                out.append(t)
            start = j + 1
        j += 1


def mc_function(path, i):
    """The chunks of m-c's `f<i>` (each a list of normalised items), its name, address and depth."""
    text = open(path).read()
    chunks = []
    for m in re.finditer(rf"^def f{i}_(\d+) : Lcmd \(Op Reg\) Reg :=\n", text, re.M):
        if int(m.group(1)) != len(chunks):
            fail(f"{path}: chunks out of order")
        k = text.index("[", m.end())
        prefix = text[m.end() : k].strip()
        if prefix not in ("", "List.flatten", "List.flatten (List.flatten"):
            fail(f"{path}: unexpected {prefix!r}")
        items, _ = list_items(text, k)
        chunks.append([ITEM_SPLIT.sub(" ", x) for x in items])
    m = re.search(rf"def f{i} : Lfundef \(Op Reg\) Reg :=\n\s*\{{ name := (\"(?:[^\"\\]|\\.)*\"), addr := (\d+), "
                  rf"depth := (\d+),", text)
    if not m or not chunks:
        fail(f"{path}: no f{i}")
    return chunks, m.group(1), int(m.group(2)), int(m.group(3))


def mc_words(path):
    """(symbol, address) of each function, in index order."""
    out = []
    for m in re.finditer(r'^  \("((?:[^"\\]|\\.)*)", (\d+), w(\d+)\)', open(path).read(), re.M):
        if int(m.group(3)) != len(out):
            fail("Words.lean: words out of order")
        out.append((m.group(1).encode().decode("unicode_escape"), int(m.group(2))))
    return out


# ---------------------------------------------------------------- the generator

LIT = re.compile(r"0x([0-9a-f]{16})#64")
AUIPC_ITEM = re.compile(r"^LinstrR\.Lopn \(Op\.set \(Reg\.x(\d+)\) \(Expr\.imm 0x([0-9a-f]{16})#64\)\)$")
CALL_ITEM = re.compile(
    r"^LinstrR\.(?:Lcall 0x(?P<ret>[0-9a-f]{16})#64|Ltail) \(Target\.indirect \(Expr\.bin \(BinOp\.and\) "
    r"\(Expr\.bin \(BinOp\.add\) \(Expr\.reg \(Reg\.x(?P<r>\d+)\)\) \(Expr\.imm 0x(?P<lo>[0-9a-f]{16})#64\)\) "
    r"\(Expr\.imm 0xfffffffffffffffe#64\)\) \[(?P<cands>[^\]]*)\]\)$"
)


class Image:
    def __init__(self, elf, words):
        self.elf = elf
        self.fns = words
        self.entry = {a: i for i, (_, a) in enumerate(words)}
        if len(self.entry) != len(words):
            fail("two functions at one address")
        names = [stable_name(s) for s, _ in words]
        self.key = [k for k, _, _ in names]
        mods = [lean_comps(c) for _, c, _ in names]
        # Collisions: the instantiating crate, then the symbol's hash; each from the function's own name.
        for step in (0, 1):
            groups = collections.defaultdict(list)
            for i, m in enumerate(mods):
                groups[tuple(m)].append(i)
            for g in groups.values():
                if len(g) > 1:
                    for i in g:
                        inst = names[i][2]
                        suffix = ("In" + v0demangle.camel(inst)) if step == 0 and inst else "H" + sha(words[i][0])[:6]
                        mods[i] = mods[i][:-1] + [mods[i][-1] + suffix]
        if len(set(map(tuple, mods))) != len(mods):
            fail("module names collide")
        self.mod = mods
        self.text_relocs = {}
        self.lo12_users = collections.defaultdict(list)
        for off, t, s, a in elf.relocs[".text"]:
            if t in (R_ALIGN, R_RELAX):
                fail(f"relaxation relocation at {off:#x}: link with --no-relax")
            if t in (R_CALL_PLT, R_HI20):
                if off in self.text_relocs:
                    fail(f"two relocations at {off:#x}")
                self.text_relocs[off] = (t, (s["value"] + a) & MASK)
            elif t in (R_LO12_I, R_LO12_S):
                self.lo12_users[s["value"]].append((off, t))
            else:
                fail(f"relocation type {t} at {off:#x}")
        self.data_relocs = {}
        for sec, rs in elf.relocs.items():
            if sec == ".text":
                continue
            for off, t, s, a in rs:
                if t != R_RISCV_64:
                    fail(f"relocation type {t} in {sec}")
                self.data_relocs[off] = (s["value"] + a) & MASK
        self.named = collections.defaultdict(list)
        self.sized = []
        self.labels = collections.defaultdict(set)  # section index -> symbol addresses
        for s in elf.symbols:
            if s["shndx"] == 0 or s["shndx"] >= len(elf.sections) or s["type"] in (3, 4):
                continue
            if s["name"].startswith("$"):
                continue
            self.labels[s["shndx"]].add(s["value"])
            if s["size"] > 0 and s["type"] == 1:
                self.sized.append(s)
            if s["name"] and not s["name"].startswith(".L"):
                self.named[s["value"]].append(s)
        self.memo = {}

    def data_key(self, addr, depth=0):
        """(field name, key) of the data at `addr`: its symbol's name where it has one, else a hash of its bytes, with
        each absolute address in them replaced by its target's key, and their length."""
        if addr in self.memo:
            return self.memo[addr]
        if depth > 32:
            fail(f"data at {addr:#x}: references nest too deep")
        if addr in self.entry:
            r = ("fn_" + "_".join(self.mod[self.entry[addr]]), "fn " + self.key[self.entry[addr]])
        elif self.named.get(addr):
            s = sorted(self.named[addr], key=lambda s: (-s["bind"], s["name"]))[0]
            k, comps, _ = stable_name(s["name"])
            r = (re.sub(r"\W", "_", comps[-1] if s["name"].startswith("_R") else s["name"]).strip("_"), "sym " + k)
        else:
            obj = [s for s in self.sized if s["value"] <= addr < s["value"] + s["size"]]
            if obj:
                start, n = obj[0]["value"], obj[0]["size"]
            else:
                idx, sec = self.elf.section_at(addr)
                if sec is None:
                    fail(f"data reference to {addr:#x}, outside the image")
                start = addr
                later = [a for a in self.labels[idx] if a > addr]
                n = min(later + [sec["addr"] + sec["size"]]) - addr
            body = bytearray(self.elf.read(start, n))
            refs = []
            for o in range(start, start + n):
                if o in self.data_relocs:
                    body[o - start : o - start + 8] = b"\0" * 8
                    refs.append(f"{o - start}:{self.data_key(self.data_relocs[o], depth + 1)[1]}")
            h = sha(bytes(body) + "\n".join(refs).encode())[:8]
            name = f"c{n}_{h}" + (f"_at{addr - start}" if addr != start else "")
            r = (name, f"data {n} {h}" + (f" +{addr - start}" if addr != start else ""))
        self.memo[addr] = r
        return r


def templatize(img, i, chunks):
    """The template's chunks (item strings with `L.` fields), and its fields: callees, sites, data references, each
    with its value in this image."""
    base = img.fns[i][1]
    flat = [x for c in chunks for x in c]
    n = len(flat) // 2
    if len(flat) != 2 * n or any(flat[2 * k] != f"LinstrR.Llabel (LabelKind.internal) {k}" for k in range(n)):
        fail(f"function {i}: items are not label, instruction pairs")
    words = [struct.unpack("<I", img.elf.read(base + 4 * k, 4))[0] for k in range(n)]
    instr = [flat[2 * k + 1] for k in range(n)]
    callees = {}  # function index -> field
    sites, data = [], []  # (field, value tuple, callee field)
    data_names = collections.Counter()
    callee_order = []
    out = list(instr)
    consumed = set()

    def callee_field(j):
        if j not in callees:
            callees[j] = None
            callee_order.append(j)
        return j

    for k in range(n):
        w, pc, item = words[k], base + 4 * k, instr[k]
        if "Labort" in item:
            fail(f"{img.key[i]}: instruction {k} lifts to abort")
        if w & 0x7F != 0x17:
            continue
        m = AUIPC_ITEM.match(item)
        rd = w >> 7 & 31
        hi = (pc + sext(w & 0xFFFFF000, 32)) & MASK
        if not m or int(m.group(1)) != rd or int(m.group(2), 16) != hi:
            fail(f"{img.key[i]}: auipc at {pc:#x} lifts to {item}")
        rel = img.text_relocs.get(pc)
        nxt = words[k + 1] if k + 1 < n else 0
        if rel is None or rel[0] == R_CALL_PLT:
            mc = CALL_ITEM.match(instr[k + 1]) if k + 1 < n else None
            if nxt & 0x707F != 0x67 or (nxt >> 15 & 31) != rd or not mc or int(mc.group("r")) != rd:
                fail(f"{img.key[i]}: auipc at {pc:#x} is no call's (relocation {rel})")
            lo = sext(nxt >> 20, 12) & MASK
            target = (hi + lo) & MASK & ~1
            if rel is not None and rel[1] != target:
                fail(f"{img.key[i]}: call at {pc:#x} reaches {target:#x}, its relocation {rel[1]:#x}")
            if target not in img.entry:
                fail(f"{img.key[i]}: call at {pc:#x} to {target:#x}, no function's entry")
            j = img.entry[target]
            if mc.group("cands").strip() != str(j) or int(mc.group("lo"), 16) != lo:
                fail(f"{img.key[i]}: call at {pc:#x} has candidates [{mc.group('cands')}], not [{j}]")
            s = f"s{len(sites)}"
            sites.append((s, (hi, lo), callee_field(j)))
            out[k] = f"LinstrR.Lopn (Op.set (Reg.x{rd}) (Expr.imm L.{s}.hi))"
            call = instr[k + 1]
            if mc.group("ret"):
                ret = int(mc.group("ret"), 16)
                if ret != pc + 8:
                    fail(f"{img.key[i]}: call at {pc + 4:#x} returns to {ret:#x}")
                call = call.replace(f"Lcall 0x{ret:016x}#64", f"Lcall (L.base + 0x{ret - base:x}#64)", 1)
            call = call.replace(f"(Expr.imm 0x{lo:016x}#64)) (Expr.imm 0xfffffffffffffffe#64)",
                                f"(Expr.imm L.{s}.lo)) (Expr.imm 0xfffffffffffffffe#64)", 1)
            call = re.sub(r"\[\d+\]\)$", f"[L.@{j}@.idx])", call)
            out[k + 1] = call
            consumed.add(k + 1)
        elif rel[0] == R_HI20:
            target = rel[1]
            users = img.lo12_users.get(pc, [])
            if not users:
                fail(f"{img.key[i]}: PCREL_HI20 at {pc:#x} has no user")
            los = set()
            for u, t in users:
                ku = (u - base) // 4
                if not (0 <= ku < n) or (u - base) % 4:
                    fail(f"{img.key[i]}: lo12 user at {u:#x} of {pc:#x} is outside the function")
                uw = words[ku]
                lo = sext(uw >> 20, 12) if t == R_LO12_I else sext((uw >> 25) << 5 | (uw >> 7 & 31), 12)
                if (uw >> 15 & 31) != rd or (hi + lo) & MASK != target:
                    fail(f"{img.key[i]}: lo12 user at {u:#x} does not complete {pc:#x} to {target:#x}")
                los.add(lo & MASK)
            if len(los) != 1:
                fail(f"{img.key[i]}: the users of {pc:#x} add different offsets")
            lo = los.pop()
            fname, _ = img.data_key(target)
            data_names[fname] += 1
            d = "d_" + fname + (f"_{data_names[fname] - 1}" if data_names[fname] > 1 else "")
            data.append((d, (hi, lo, target)))
            out[k] = f"LinstrR.Lopn (Op.set (Reg.x{rd}) (Expr.imm L.{d}.hi))"
            for u, _ in users:
                ku = (u - base) // 4
                lit = f"(Expr.imm 0x{lo:016x}#64)"
                if out[ku].count(lit) != 1 or ku in consumed:
                    fail(f"{img.key[i]}: lo12 user {k} -> {ku} ({out[ku]}) has {out[ku].count(lit)} offsets {lit}")
                out[ku] = out[ku].replace(lit, f"(Expr.imm L.{d}.lo)")
                consumed.add(ku)
        else:
            fail(f"{img.key[i]}: auipc at {pc:#x} with relocation {rel}")
    for k in range(n):
        if (out[k].startswith("LinstrR.Lcall") or out[k].startswith("LinstrR.Ltail")) and k not in consumed:
            fail(f"{img.key[i]}: call at instruction {k} not after an auipc: {out[k]}")
        if "Target.direct" in out[k] or "List.range" in out[k]:
            fail(f"{img.key[i]}: instruction {k}: {out[k]}")
    # callee fields: the shortest suffix of the module path unique among this function's callees
    taken = {"name", "base"} | {s for s, _, _ in sites} | {d for d, _ in data}
    for j in callee_order:
        comps = img.mod[j]
        for ln in range(1, len(comps) + 1):
            f = lower1("_".join(comps[-ln:]))
            clash = f in taken or any(lower1("_".join(img.mod[o][-ln:])) == f for o in callee_order if o != j)
            if not clash:
                break
        else:
            f = "f_" + "_".join(comps)
        if f in taken:
            fail(f"{img.key[i]}: no field name for callee {img.key[j]}")
        taken.add(f)
        callees[j] = field_ident(f)
    for k in range(n):
        out[k] = re.sub(r"@(\d+)@", lambda m: callees[int(m.group(1))], out[k])
    # nothing that depends on the layout is left
    ranges = [(s["addr"], s["addr"] + s["size"]) for s in img.elf.sections if s["flags"] & 2]
    for k in range(n):
        for m in LIT.finditer(out[k]):
            v = int(m.group(1), 16)
            if any(a <= v < b for a, b in ranges) or v in img.entry:
                fail(f"{img.key[i]}: instruction {k} keeps the address {v:#x}: {out[k]}")
    sizes = [len(c) // 2 for c in chunks]
    res, k = [], 0
    for sz in sizes:
        res.append(out[k : k + sz])
        k += sz
    return res, [(j, callees[j]) for j in callee_order], sites, data


def tmpl_module(img, i, tchunks, callees, sites, data, depth):
    mod = ".".join(img.mod[i])
    ns = f"{NS}.{mod}"
    cf = dict(callees)
    lines = [
        "/-",
        f"  {NS}.Tmpl.{mod}",
        "",
        "  Written by `scripts/gen.py`; do not edit. The lift of",
        "",
        f"    {comment_safe(img.key[i])}",
        "",
        "  with every value that depends on the layout of the image a field of `Link`.",
        "-/",
        "",
        "import Rv64mc.Link.Basic",
        "",
        f"namespace {ns}",
        "",
        "open RiscvZkvm.Rv64 Lprog Lprog.RiscV",
        "",
        "noncomputable section",
        "",
        "/-- Where the template's addresses come from: its name and entry, its callees, call sites and data. -/",
        "structure Link where",
        "  name : String",
        "  base : Word",
    ]
    lines += [f"  {f} : Callee" for _, f in callees]
    lines += [f"  {s} : Site" for s, _, _ in sites]
    lines += [f"  {d} : DataRef" for d, _ in data]
    lines.append("")
    for j, c in enumerate(tchunks):
        var = "L" if any("L." in x for x in c) else "_L"
        lines.append(f"def c{j} ({var} : Link) : Lcmd (Op Reg) Reg := [")
        items = []
        for k, x in enumerate(c):
            items.append(f"  LinstrR.Llabel (LabelKind.internal) {sum(len(t) for t in tchunks[:j]) + k}")
            items.append("  " + x)
        lines.append(",\n".join(items) + "]")
        lines.append("")
    names = ", ".join(f"c{j} L" for j in range(len(tchunks)))
    lines += [
        "/-- The function, its addresses those of `L`. -/",
        "def tmpl (L : Link) : Lfundef (Op Reg) Reg :=",
        f"  {{ name := L.name, addr := L.base, depth := {depth}, body := List.flatten [{names}] }}",
        "",
        "/-- What the link step proves of `L`: each callee where `L` says (`Callee.WF`), each site reaching its callee",
        "    (`Site.WF`), each data reference's parts making its address (`DataRef.WF`), as equations for `simp`. -/",
        "structure Link.WF (p : Lprog (Op Reg) Reg) (L : Link) : Prop where",
    ]
    lines += [f"  {f} : (p[L.{f}.idx]?).map (·.addr) = some L.{f}.entry" for _, f in callees]
    lines += [f"  {s} : (L.{s}.hi + L.{s}.lo) &&& 0xfffffffffffffffe#64 = L.{cf[j]}.entry" for s, _, j in sites]
    lines += [f"  {d} : L.{d}.hi + L.{d}.lo = L.{d}.addr" for d, _ in data]
    lines += ["", "end", "", f"end {ns}", ""]
    return "\n".join(lines)


def w64(v):
    return f"0x{v:016x}#64"


def link_module(img, i, tchunks, callees, sites, data, mcname):
    mod = ".".join(img.mod[i])
    ns = f"{NS}.{mod}"
    cf = dict(callees)
    base = img.fns[i][1]
    fields = [f"name := {mcname}", f"base := {w64(base)}"]
    fields += [f"«{f.strip('«»')}» := ⟨{j}, {w64(img.fns[j][1])}⟩" for j, f in callees]
    fields += [f"{s} := ⟨{w64(hi)}, {w64(lo)}⟩" for s, (hi, lo), _ in sites]
    fields += [f"{d} := ⟨{w64(hi)}, {w64(lo)}, {w64(a)}⟩" for d, (hi, lo, a) in data]
    parts = ", ".join(f"c{j} link" for j in range(len(tchunks)))
    lines = [
        "/-",
        f"  {NS}.Link.{mod}",
        "",
        f"  Written by `scripts/gen.py`; do not edit. Function {i} of the image is the template at `link`.",
        "-/",
        "",
        f"import {NS}.Words",
        f"import {NS}.Tmpl.{mod}",
        "",
        f"namespace {ns}",
        "",
        "open RiscvZkvm.Rv64 Lprog Lprog.RiscV MachineChecked.RiscV.Lift Tools.ToLean",
        "",
        "noncomputable section",
        "",
        "/-- The addresses of the image. -/",
        "def link : Link where",
    ]
    lines += [f"  {x}" for x in fields]
    lines += [
        "",
        f"kernel_eq head : (liftProg fns)[{i}]?.map (fun g => (g.name, g.addr, g.depth)) =",
        "    some ((tmpl link).name, (tmpl link).addr, (tmpl link).depth)",
        "",
        f"kernel_eq parts : (liftProg fns)[{i}]?.map (fun g => chunks chunk g.body) = some [{parts}]",
        "",
        f"/-- **Function {i} of the image is the template at `link`.** -/",
        f"theorem tmpl_eq : (liftProg fns)[{i}]? = some (tmpl link) :=",
        "  getElem?_eq_of_chunks head parts rfl",
        "",
    ]
    wf = []
    for j, f in callees:
        lines.append(f"kernel_eq wf_{f.strip('«»')} : ((liftProg fns)[link.{f}.idx]?).map (·.addr) = some link.{f}.entry")
        wf.append(f"wf_{f.strip('«»')}")
    for s, _, j in sites:
        lines.append(f"kernel_eq wf_{s} : (link.{s}.hi + link.{s}.lo) &&& 0xfffffffffffffffe#64 = link.{cf[j]}.entry")
        wf.append(f"wf_{s}")
    for d, _ in data:
        lines.append(f"kernel_eq wf_{d} : link.{d}.hi + link.{d}.lo = link.{d}.addr")
        wf.append(f"wf_{d}")
    lines += [
        "",
        "/-- **The link's facts hold of the image.** -/",
        f"theorem wf : Link.WF (liftProg fns) link := ⟨{', '.join(wf)}⟩",
        "",
        "end",
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def words_module(mc_text, lean_elf):
    t = mc_text
    m = re.search(r"^namespace (\S+)$", t, re.M)
    if not m:
        fail("Words.lean: no namespace")
    old = m.group(1)
    t = re.sub(r"\A/-.*?-/", f"/-\n  {NS}.Words\n\n  Written by `scripts/gen.py` from `decompile --to lean --proved`'s "
               "Words.lean; do not edit.\n-/", t, count=1, flags=re.S)
    t = t.replace(f"namespace {old}\n", f"namespace {NS}\n", 1).replace(f"end {old}\n", f"end {NS}\n")
    t, k = re.subn(r'^check_elf_words words "[^"]*"$', f"check_elf_words words {lean_str(lean_elf)}", t, flags=re.M)
    if k != 1:
        fail("Words.lean: no check_elf_words")
    return t


def index_module(img, sizes):
    rows = [
        f"  ({lean_str('.'.join(img.mod[i]))}, {lean_str(s)}, {i}, {a}, {sizes[i]})" for i, (s, a) in enumerate(img.fns)
    ]
    return "\n".join([
        "/-",
        f"  {NS}.Index",
        "",
        "  Written by `scripts/gen.py`; do not edit. Each function's module, symbol, index, address and size in",
        "  instructions, checked against `words`.",
        "-/",
        "",
        f"import {NS}.Words",
        "",
        f"namespace {NS}",
        "",
        "open MachineChecked.RiscV.Lift Tools.ToLean",
        "",
        "noncomputable section",
        "",
        "def index : List (String × String × Nat × Nat × Nat) := [",
        ",\n".join(rows) + "]",
        "",
        "kernel_eq index_eq : words.zipIdx.map (fun ((n, b, ws), i) => (n, i, b, ws.length)) =",
        "    index.map (fun (_, s, i, a, n) => (s, i, a, n))",
        "",
        f"kernel_eq fns_length : fns.length = {len(img.fns)}",
        "",
        "end",
        "",
        f"end {NS}",
        "",
    ])


def image_module(elf_sha, lean_elf):
    """The end statement's `Rv64mc.image`, read from the ELF by `Rv64mc.ImageOfElf` when the module is built; the
    ELF's sha256 is in the text, so that the module is rebuilt when the ELF changes."""
    return (f"/-\n  {NS}.Image\n\n  Written by `scripts/gen.py`; do not edit. The end statement's image: `imageOfElf` of "
            f"the ELF with sha256\n  {elf_sha}.\n-/\n\nimport Rv64mc.ImageOfElf\n\nnamespace Rv64mc\n\n"
            f"elf_image image {json.dumps(lean_elf)}\n\nend Rv64mc\n")


def umbrella(name, mods, doc):
    return f"/-\n  {name}\n\n  Written by `scripts/gen.py`; do not edit. {doc}\n-/\n\n" + "".join(f"import {m}\n" for m in mods)


def generate(args):
    elf = Elf(open(args.elf, "rb").read())
    mcdir = args.mc
    words = mc_words(os.path.join(mcdir, "Words.lean"))
    img = Image(elf, words)
    files = {}
    hashes, index_rows, sizes = [], [], []
    for i in range(len(words)):
        chunks, mcname, addr, depth = mc_function(os.path.join(mcdir, f"F{i}.lean"), i)
        if addr != words[i][1]:
            fail(f"F{i}: address {addr:#x}, Words {words[i][1]:#x}")
        tchunks, callees, sites, data = templatize(img, i, chunks)
        rel = "/".join(img.mod[i]) + ".lean"
        t = tmpl_module(img, i, tchunks, callees, sites, data, depth)
        files["Tmpl/" + rel] = t
        files["Link/" + rel] = link_module(img, i, tchunks, callees, sites, data, mcname)
        sizes.append(sum(len(c) for c in chunks) // 2)
        hashes.append(f"{'.'.join(img.mod[i])}\t{sha(t)[:16]}\t{img.key[i]}")
        index_rows.append(f"{'.'.join(img.mod[i])}\t{i}\t{words[i][1]:#x}\t{sizes[i]}\t{words[i][0]}\t{img.key[i]}")
    files["Words.lean"] = words_module(open(os.path.join(mcdir, "Words.lean")).read(), args.lean_elf)
    files["Index.lean"] = index_module(img, sizes)
    files["Image.lean"] = image_module(sha(open(args.elf, "rb").read()), args.lean_elf)
    tm = sorted(f"{NS}.Tmpl." + ".".join(m) for m in img.mod)
    lm = sorted(f"{NS}.Link." + ".".join(m) for m in img.mod)
    files["Tmpl.lean"] = umbrella(f"{NS}.Tmpl", tm, "Every function's template.")
    files["Link.lean"] = umbrella(f"{NS}.Link", [f"{NS}.Index"] + lm, "The link step: every function's link.")
    files["hashes.tsv"] = "".join(h + "\n" for h in sorted(hashes))
    files["index.tsv"] = "module\tindex\taddress\tinstructions\tsymbol\tkey\n" + "".join(r + "\n" for r in index_rows)
    files["../Gen.lean"] = umbrella(NS, [f"{NS}.Tmpl", f"{NS}.Link"], "The templates and the link step.")
    return files


def sync(out, files, check):
    """Writes the files whose text changed and removes the generated files no longer written; returns what changed."""
    changed = collections.Counter()
    present = set()
    for root, _, fs in os.walk(out):
        for f in fs:
            present.add(os.path.relpath(os.path.join(root, f), out))
    want = {os.path.normpath(p) for p in files}
    for p, text in sorted(files.items()):
        path = os.path.join(out, p)
        old = open(path).read() if os.path.exists(path) else None
        if old != text:
            changed[p.split("/")[0] if "/" in p and not p.startswith("..") else p] += 1
            if not check:
                os.makedirs(os.path.dirname(path), exist_ok=True)
                with open(path, "w") as f:
                    f.write(text)
    # Layouts.lean is scripts/type-layouts.sh's
    for p in sorted(present - want - {"Layouts.lean"}):
        if p.endswith(".lean") or p.endswith(".tsv"):
            changed["removed"] += 1
            if not check:
                os.remove(os.path.join(out, p))
    if not check:
        for root, dirs, fs in os.walk(out, topdown=False):
            if root != out and not os.listdir(root):
                os.rmdir(root)
    return changed


def read_hashes(path):
    out = {}
    for line in open(path):
        m, h, k = line.rstrip("\n").split("\t", 2)
        out[m] = (h, k)
    return out


def diff(old_path, new_path):
    old, new = read_hashes(old_path), read_hashes(new_path)
    ch = sorted(m for m in old.keys() & new.keys() if old[m][0] != new[m][0])
    add, rem = sorted(new.keys() - old.keys()), sorted(old.keys() - new.keys())
    for tag, ms, src in (("changed", ch, new), ("added", add, new), ("removed", rem, old)):
        for m in ms:
            print(f"{tag}\t{m}\t{src[m][1]}")
    print(f"templates: {len(ch)} changed, {len(add)} added, {len(rem)} removed, "
          f"{len(old.keys() & new.keys()) - len(ch)} unchanged")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--elf")
    ap.add_argument("--mc")
    ap.add_argument("--lean-elf", default="out/gen.elf")
    ap.add_argument("--out", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "Rv64mc", "Gen"))
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--diff", nargs="+", metavar="HASHES")
    args = ap.parse_args()
    if args.diff:
        if len(args.diff) > 2:
            ap.error("--diff takes OLD_HASHES [NEW_HASHES]")
        diff(args.diff[0], args.diff[1] if len(args.diff) == 2 else os.path.join(args.out, "hashes.tsv"))
        return
    if not args.elf or not args.mc:
        ap.error("--elf and --mc are required")
    out = os.path.normpath(args.out)
    files = generate(args)
    changed = sync(out, files, args.check)
    n = len([p for p in files if p.startswith("Tmpl/")])
    print(f"gen.py: {n} functions; files {'that would change' if args.check else 'written'}: "
          + (", ".join(f"{k} {v}" for k, v in sorted(changed.items())) or "none"))
    if args.check and changed:
        sys.exit(1)


if __name__ == "__main__":
    main()
