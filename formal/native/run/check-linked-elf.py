#!/usr/bin/env python3
"""Verify that a linked Linux ELF executes the exact proved leanSPHINCS machine code.

Usage:
  check-linked-elf.py --arch {x86_64,aarch64} [--asm PATH] ELF_FILE...

For each linked ELF (shared library, PIE, or static executable), this script:
  1. Assembles the reference assembly (`formal/native/rustc/asm/signatures-{arch}.s`)
     into a relocatable `.o` using `clang --target={arch}-unknown-linux-musl -c`.
  2. Locates `sphincs_verify` in the linked ELF's `.symtab` and confirms it is not
     exported in `.dynsym` (preventing dynamic symbol interposition in shared libraries).
  3. Recursively verifies `sphincs_verify` and every reachable non-panic callee
     (`memcpy`, `memset`, `keccak_f`, `Hasher::update`, `Hasher::finalize`):
     - Every non-relocated byte matches the reference `.o` byte-for-byte.
       On x86-64 this rejects `GOTPCRELX` relaxation rewrites (`movq@GOTPCREL` -> `lea`,
       `callq *@GOTPCREL` -> `addr32 call`).
     - Every call/jump/GOT/rodata relocation resolves to the exact corresponding proved
       callee or read-only data section (`RC`, `LAYER_HEIGHTS`), with read-only segment
       permissions (`PF_W == 0`) for `.rodata`.
     - Every reached `memcpy` and `memset` symbol is `STB_LOCAL` (never libc or dynamic).
     - On x86-64 ET_DYN (`.so`/PIE), every reached GOT slot is relocated by
       `R_X86_64_RELATIVE` (never `GLOB_DAT` or `JUMP_SLOT`) pointing directly to the
       local proved callee.
"""

import argparse
import os
import pathlib
import struct
import subprocess
import sys
import tempfile

PT_LOAD = 1
PF_W = 2

ET_EXEC = 2
ET_DYN = 3

SHT_SYMTAB = 2
SHT_RELA = 4
SHT_NOBITS = 8
SHT_DYNSYM = 11

STB_LOCAL = 0
STT_SECTION = 3
SHN_UNDEF = 0

EM_X86_64 = 0x3E
EM_AARCH64 = 0xB7

# x86-64 relocations
R_X86_64_PC32 = 2
R_X86_64_PLT32 = 4
R_X86_64_RELATIVE = 8
R_X86_64_GOTPCREL = 9
R_X86_64_GOTPCRELX = 41
R_X86_64_REX_GOTPCRELX = 42

# AArch64 relocations
R_AARCH64_ADR_PREL_PG_HI21 = 275
R_AARCH64_ADD_ABS_LO12_NC = 277
R_AARCH64_LDST8_ABS_LO12_NC = 278
R_AARCH64_JUMP26 = 282
R_AARCH64_CALL26 = 283
R_AARCH64_LDST16_ABS_LO12_NC = 284
R_AARCH64_LDST32_ABS_LO12_NC = 285
R_AARCH64_LDST64_ABS_LO12_NC = 286
R_AARCH64_LDST128_ABS_LO12_NC = 299

AARCH64_LO12_SHIFT = {
    R_AARCH64_ADD_ABS_LO12_NC: 0,
    R_AARCH64_LDST8_ABS_LO12_NC: 0,
    R_AARCH64_LDST16_ABS_LO12_NC: 1,
    R_AARCH64_LDST32_ABS_LO12_NC: 2,
    R_AARCH64_LDST64_ABS_LO12_NC: 3,
    R_AARCH64_LDST128_ABS_LO12_NC: 4,
}

PANIC_SUFFIXES = (
    "9panicking9panic_fmt",
    "9panicking5panic",
    "5slice5index16slice_index_fail",
    "6option13unwrap_failed",
    "17rust_begin_unwind",
)


def sign_extend(value, bits):
    sign = 1 << (bits - 1)
    return (value & (sign - 1)) - (value & sign)


class Elf:
    def __init__(self, path):
        self.path = str(path)
        self.data = open(path, "rb").read()
        if self.data[:4] != b"\x7fELF" or self.data[4] != 2 or self.data[5] != 1:
            raise SystemExit(f"{path}: not a little-endian ELF64 file")
        self.etype, self.machine = struct.unpack_from("<HH", self.data, 0x10)
        phoff, shoff = struct.unpack_from("<QQ", self.data, 0x20)
        phentsize, phnum, shentsize, shnum, shstrndx = struct.unpack_from("<HHHHH", self.data, 0x36)

        self.phdrs = []
        for i in range(phnum):
            p_type, p_flags, p_offset, p_vaddr, _, p_filesz, p_memsz, _ = struct.unpack_from(
                "<IIQQQQQQ", self.data, phoff + i * phentsize
            )
            self.phdrs.append(
                dict(
                    type=p_type,
                    flags=p_flags,
                    off=p_offset,
                    vaddr=p_vaddr,
                    filesz=p_filesz,
                    memsz=p_memsz,
                )
            )

        self.secs = []
        for i in range(shnum):
            name, typ, flags, addr, off, size, link, info, _, entsize = struct.unpack_from(
                "<IIQQQQIIQQ", self.data, shoff + i * shentsize
            )
            self.secs.append(
                dict(
                    name=name,
                    type=typ,
                    flags=flags,
                    addr=addr,
                    off=off,
                    size=size,
                    link=link,
                    info=info,
                    entsize=entsize,
                )
            )
        if shnum:
            strtab = self.secs[shstrndx]
            for s in self.secs:
                s["name"] = self._str(strtab["off"], s["name"])
                s["data"] = (
                    self.data[s["off"] : s["off"] + s["size"]]
                    if s["type"] != SHT_NOBITS
                    else b"\0" * s["size"]
                )

        self.syms = []
        self.dynsyms = []
        for s in self.secs:
            if s["type"] in (SHT_SYMTAB, SHT_DYNSYM):
                names = self.secs[s["link"]]
                dst = self.syms if s["type"] == SHT_SYMTAB else self.dynsyms
                for k in range(s["size"] // 24):
                    name, info, other, shndx, value, size = struct.unpack_from(
                        "<IBBHQQ", self.data, s["off"] + 24 * k
                    )
                    dst.append(
                        dict(
                            name=self._str(names["off"], name),
                            type=info & 0xF,
                            bind=info >> 4,
                            vis=other & 0x3,
                            shndx=shndx,
                            value=value,
                            size=size,
                        )
                    )

        # Relocations per target section (for ET_REL) and dynamic relocations by vaddr (for ET_DYN/ET_EXEC)
        self.sec_relocs = {}
        self.dyn_relocs = {}
        for s in self.secs:
            if s["type"] == SHT_RELA:
                if s["name"] in (".rela.dyn", ".rela.plt"):
                    for k in range(s["size"] // 24):
                        off, info, addend = struct.unpack_from("<QQq", self.data, s["off"] + 24 * k)
                        self.dyn_relocs[off] = (info & 0xFFFFFFFF, info >> 32, addend)
                else:
                    rs = self.sec_relocs.setdefault(s["info"], {})
                    for k in range(s["size"] // 24):
                        off, info, addend = struct.unpack_from("<QQq", self.data, s["off"] + 24 * k)
                        rs.setdefault(off, []).append((info & 0xFFFFFFFF, info >> 32, addend))

    def _str(self, base, off):
        end = self.data.index(b"\0", base + off)
        return self.data[base + off : end].decode()

    def named_at(self, shndx, value):
        return sorted(
            s["name"]
            for s in self.syms
            if s["shndx"] == shndx
            and s["value"] == value
            and s["type"] != STT_SECTION
            and s["name"]
            and not s["name"].startswith((".L", "$"))
        )

    def ref_functions(self):
        out = {}
        for i, s in enumerate(self.secs):
            if s["name"].startswith(".text."):
                for n in self.named_at(i, 0):
                    out[n] = i
        return out

    def ref_target(self, symidx, addend):
        sym = self.syms[symidx]
        if sym["type"] != STT_SECTION and sym["name"] and not sym["name"].startswith((".L", "$")):
            if sym["shndx"] == SHN_UNDEF:
                return ("undefined", sym["name"], addend)
            if self.secs[sym["shndx"]]["name"].startswith(".text."):
                return ("func", sym["name"], addend)
        shndx = sym["shndx"]
        sec = self.secs[shndx]
        if sec["name"].startswith(".text."):
            named = self.named_at(shndx, 0)
            if named:
                return ("func", named[0], sym["value"] + addend)
        return ("data", shndx, sym["value"] + addend)

    def read_vaddr(self, vaddr, size):
        for p in self.phdrs:
            if p["type"] == PT_LOAD and p["vaddr"] <= vaddr and vaddr + size <= p["vaddr"] + p["filesz"]:
                off = p["off"] + (vaddr - p["vaddr"])
                return self.data[off : off + size], p["flags"]
        raise ValueError(f"vaddr {vaddr:#x}..{vaddr + size:#x} not mapped in PT_LOAD of {self.path}")

    def syms_at_vaddr(self, vaddr):
        return [
            s
            for s in self.syms
            if s["value"] == vaddr and s["shndx"] != SHN_UNDEF and s["type"] != STT_SECTION
            and s["name"] and not s["name"].startswith((".L", "$"))
        ]


def check_linked_elf(ref, linked, entry="sphincs_verify"):
    if linked.machine != ref.machine:
        raise SystemExit(f"{linked.path}: machine {linked.machine:#x} != expected {ref.machine:#x}")
    if not linked.syms:
        raise SystemExit(f"{linked.path}: missing .symtab (binary is stripped); cannot locate {entry}")

    # Confirm sphincs_verify is not exported dynamically (prevents interposition in .so).
    exported = [s for s in linked.dynsyms if s["name"] == entry and s["shndx"] != SHN_UNDEF]
    if exported:
        raise SystemExit(f"{linked.path}: {entry} is exported in .dynsym (must be hidden/local)")

    entry_syms = [s for s in linked.syms if s["name"] == entry and s["shndx"] != SHN_UNDEF]
    if len(entry_syms) != 1:
        raise SystemExit(f"{linked.path}: expected 1 defined {entry} in .symtab, found {len(entry_syms)}")
    entry_vaddr = entry_syms[0]["value"]

    ref_fns = ref.ref_functions()
    if entry not in ref_fns:
        raise SystemExit(f"{ref.path}: missing {entry}")

    checked_funcs = {}
    checked_rodata = set()
    checked_got = set()
    errors = []

    def verify_func(name, vaddr):
        if name.endswith(PANIC_SUFFIXES):
            return
        if name in checked_funcs:
            if checked_funcs[name] != vaddr:
                errors.append(f"{name}: linked at multiple addresses {checked_funcs[name]:#x} and {vaddr:#x}")
            return
        if name not in ref_fns:
            errors.append(f"{name}: not in reference object {ref.path}")
            return
        checked_funcs[name] = vaddr

        # Check binding of memcpy/memset in linked .symtab
        if name in ("memcpy", "memset"):
            at_addr = [s for s in linked.syms_at_vaddr(vaddr) if s["name"] == name]
            if not at_addr:
                errors.append(f"{name} at {vaddr:#x}: missing local symbol in .symtab")
            elif any(s["bind"] != STB_LOCAL for s in at_addr):
                errors.append(f"{name} at {vaddr:#x}: expected STB_LOCAL binding, got {at_addr}")

        shndx = ref_fns[name]
        rsym = [s for s in ref.syms if s["name"] == name and s["shndx"] == shndx and s["value"] == 0]
        rbytes_full = ref.secs[shndx]["data"]
        rsize = rsym[0]["size"] if rsym and rsym[0]["size"] else len(rbytes_full)
        rbytes = rbytes_full[:rsize]
        rrels = {o: entries for o, entries in ref.sec_relocs.get(shndx, {}).items() if o < rsize}

        try:
            lbytes, _ = linked.read_vaddr(vaddr, rsize)
        except ValueError as exc:
            errors.append(f"{name}: {exc}")
            return

        if ref.machine == EM_X86_64:
            verify_x64_func(name, vaddr, rbytes, lbytes, rrels)
        elif ref.machine == EM_AARCH64:
            verify_arm64_func(name, vaddr, rbytes, lbytes, rrels)
        else:
            errors.append(f"unsupported machine {ref.machine:#x}")

    def verify_rodata(fn_name, off, ref_shndx, target_vaddr, target_offset):
        sec = ref.secs[ref_shndx]
        base_vaddr = target_vaddr - target_offset
        try:
            actual, flags = linked.read_vaddr(base_vaddr, len(sec["data"]))
        except ValueError as exc:
            errors.append(f"{fn_name}+{off:#x}: rodata {sec['name']}: {exc}")
            return
        if sec["name"].startswith(".data.rel.ro"):
            # Relocated read-only metadata (e.g. panic::Location structs holding string pointers).
            # Check all non-relocated bytes against the reference section.
            sec_rels = ref.sec_relocs.get(ref_shndx, {})
            masked = bytearray(len(sec["data"]))
            for roff in sec_rels:
                for k in range(8):
                    if roff + k < len(masked):
                        masked[roff + k] = 1
            for i in range(len(sec["data"])):
                if not masked[i] and actual[i] != sec["data"][i]:
                    errors.append(
                        f"{fn_name}+{off:#x}: {sec['name']}+{i:#x} mismatch at {base_vaddr:#x}"
                    )
                    return
            checked_rodata.add((sec["name"], base_vaddr, len(sec["data"])))
            return
        if flags & PF_W:
            errors.append(f"{fn_name}+{off:#x}: rodata {sec['name']} at {base_vaddr:#x} is writable")
        if actual != sec["data"]:
            errors.append(f"{fn_name}+{off:#x}: rodata {sec['name']} bytes at {base_vaddr:#x} do not match reference")
            return
        checked_rodata.add((sec["name"], base_vaddr, len(sec["data"])))

    def verify_x64_func(name, vaddr, rbytes, lbytes, rrels):
        masked = bytearray(len(rbytes))
        for off in rrels:
            for k in range(4):
                if off + k < len(masked):
                    masked[off + k] = 1

        for i in range(len(rbytes)):
            if not masked[i] and rbytes[i] != lbytes[i]:
                errors.append(
                    f"{name}+{i:#x}: byte mismatch (linked {lbytes[i:i + 8].hex()} != ref {rbytes[i:i + 8].hex()}; "
                    f"possible linker relaxation?)"
                )
                break

        for off, entries in sorted(rrels.items()):
            if len(entries) != 1:
                errors.append(f"{name}+{off:#x}: expected 1 relocation, got {len(entries)}")
                continue
            rtype, symidx, addend = entries[0]
            disp32, = struct.unpack_from("<i", lbytes, off)
            target = ref.ref_target(symidx, addend)

            if rtype in (R_X86_64_GOTPCREL, R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX):
                if target[0] != "func":
                    errors.append(f"{name}+{off:#x}: unexpected GOT target {target}")
                    continue
                callee = target[1]
                got_vaddr = vaddr + off + disp32 - addend
                if linked.etype == ET_DYN:
                    dyn = linked.dyn_relocs.get(got_vaddr)
                    if dyn is None:
                        errors.append(
                            f"{name}+{off:#x}: GOT slot {got_vaddr:#x} for {callee} has no dynamic relocation"
                        )
                        continue
                    dtype, dsym, daddend = dyn
                    if dtype != R_X86_64_RELATIVE or dsym != 0:
                        errors.append(
                            f"{name}+{off:#x}: GOT slot {got_vaddr:#x} for {callee} uses reloc type {dtype} "
                            f"(expected R_X86_64_RELATIVE)"
                        )
                        continue
                    target_vaddr = daddend
                elif linked.etype == ET_EXEC:
                    if got_vaddr in linked.dyn_relocs:
                        errors.append(
                            f"{name}+{off:#x}: static EXEC GOT slot {got_vaddr:#x} has dynamic reloc"
                        )
                        continue
                    slot_bytes, _ = linked.read_vaddr(got_vaddr, 8)
                    target_vaddr, = struct.unpack("<Q", slot_bytes)
                else:
                    errors.append(f"{name}+{off:#x}: unsupported ELF type {linked.etype}")
                    continue
                checked_got.add((callee, got_vaddr, target_vaddr))
                verify_func(callee, target_vaddr)

            elif rtype in (R_X86_64_PLT32, R_X86_64_PC32):
                if target[0] == "func":
                    callee, sym_addend = target[1], target[2]
                    # For call/jmp, ref addend is -4; S = P + disp32 - A.
                    target_vaddr = vaddr + off + disp32 - addend
                    if sym_addend != addend:
                        errors.append(f"{name}+{off:#x}: unexpected func addend {sym_addend} vs {addend}")
                    verify_func(callee, target_vaddr)
                elif target[0] == "data":
                    ref_shndx, sec_off_plus_a = target[1], target[2]
                    # On x86-64 RIP-relative data access, effective address is P + 4 + disp32 = S + (A + 4).
                    target_vaddr = vaddr + off + 4 + disp32
                    verify_rodata(name, off, ref_shndx, target_vaddr, sec_off_plus_a + 4)
                else:
                    errors.append(f"{name}+{off:#x}: unresolved target {target}")
            else:
                errors.append(f"{name}+{off:#x}: unsupported x86-64 relocation type {rtype}")

    def verify_arm64_func(name, vaddr, rbytes, lbytes, rrels):
        if len(rbytes) % 4 != 0:
            errors.append(f"{name}: AArch64 size {len(rbytes)} not 4-byte aligned")
            return
        # Track ADRP resolved pages by destination register for pairing with LO12 relocs.
        adrp_pages = {}
        for off in range(0, len(rbytes), 4):
            rw, = struct.unpack_from("<I", rbytes, off)
            lw, = struct.unpack_from("<I", lbytes, off)
            entries = rrels.get(off)
            if not entries:
                if rw != lw:
                    errors.append(f"{name}+{off:#x}: word {lw:#010x} != ref {rw:#010x}")
                    break
                continue
            if len(entries) != 1:
                errors.append(f"{name}+{off:#x}: expected 1 relocation, got {len(entries)}")
                continue
            rtype, symidx, addend = entries[0]
            target = ref.ref_target(symidx, addend)
            if rtype in (R_AARCH64_CALL26, R_AARCH64_JUMP26):
                if (rw & 0xFC000000) != (lw & 0xFC000000):
                    errors.append(f"{name}+{off:#x}: branch opcode {lw:#010x} != ref {rw:#010x}")
                    continue
                if target[0] != "func":
                    errors.append(f"{name}+{off:#x}: unexpected branch target {target}")
                    continue
                imm26 = sign_extend(lw & 0x03FFFFFF, 26)
                target_vaddr = vaddr + off + imm26 * 4
                verify_func(target[1], target_vaddr)
            elif rtype == R_AARCH64_ADR_PREL_PG_HI21:
                if (rw & 0x9F00001F) != (lw & 0x9F00001F):
                    errors.append(f"{name}+{off:#x}: ADRP opcode/rd {lw:#010x} != ref {rw:#010x}")
                    continue
                rd = lw & 0x1F
                immlo = (lw >> 29) & 0x3
                immhi = (lw >> 5) & 0x7FFFF
                imm21 = sign_extend((immhi << 2) | immlo, 21)
                page = ((vaddr + off) & ~0xFFF) + (imm21 << 12)
                adrp_pages[rd] = (page, target)
            elif rtype in AARCH64_LO12_SHIFT:
                if (rw & 0xFFC003FF) != (lw & 0xFFC003FF):
                    errors.append(f"{name}+{off:#x}: LO12 opcode/regs {lw:#010x} != ref {rw:#010x}")
                    continue
                rn = (lw >> 5) & 0x1F
                if rn not in adrp_pages:
                    errors.append(f"{name}+{off:#x}: LO12 reloc on x{rn} without preceding ADRP")
                    continue
                page, adrp_target = adrp_pages[rn]
                if adrp_target != target:
                    errors.append(f"{name}+{off:#x}: LO12 target {target} != ADRP target {adrp_target}")
                    continue
                imm12 = (lw >> 10) & 0xFFF
                target_vaddr = page + (imm12 << AARCH64_LO12_SHIFT[rtype])
                if target[0] == "data":
                    verify_rodata(name, off, target[1], target_vaddr, target[2])
                elif target[0] == "func":
                    verify_func(target[1], target_vaddr)
                else:
                    errors.append(f"{name}+{off:#x}: unresolved LO12 target {target}")
            else:
                errors.append(f"{name}+{off:#x}: unsupported AArch64 relocation type {rtype}")

    verify_func(entry, entry_vaddr)

    expected_count = 6
    if len(checked_funcs) != expected_count:
        errors.append(
            f"expected {expected_count} verified functions, checked {len(checked_funcs)}: {sorted(checked_funcs)}"
        )

    if errors:
        for e in errors:
            print(f"FAIL {linked.path}: {e}", file=sys.stderr)
        return False

    print(
        f"OK {linked.path}: {len(checked_funcs)} functions byte-identical, "
        f"{len(checked_rodata)} rodata sections verified, "
        f"{len(checked_got)} GOT slots R_X86_64_RELATIVE/local"
    )
    return True


def main():
    parser = argparse.ArgumentParser(description="Verify linked ELF files against proved leanSPHINCS assembly")
    parser.add_argument("--arch", required=True, choices=("x86_64", "aarch64"))
    parser.add_argument("--asm", help="Path to signatures-{arch}.s")
    parser.add_argument("--clang", default=os.environ.get("CLANG", "clang"))
    parser.add_argument("elfs", nargs="+", help="Linked ELF files to verify")
    args = parser.parse_args()

    repo_root = pathlib.Path(__file__).resolve().parents[3]
    asm_path = (
        pathlib.Path(args.asm)
        if args.asm
        else repo_root / "formal/native/rustc/asm" / f"signatures-{args.arch}.s"
    )
    if not asm_path.is_file():
        raise SystemExit(f"reference assembly not found: {asm_path}")

    target = f"{args.arch}-unknown-linux-musl"
    with tempfile.TemporaryDirectory() as tmp:
        ref_obj = pathlib.Path(tmp) / f"ref-{args.arch}.o"
        subprocess.run(
            [args.clang, f"--target={target}", "-c", str(asm_path), "-o", str(ref_obj)],
            check=True,
        )
        ref = Elf(ref_obj)
        ok = True
        for path in args.elfs:
            linked = Elf(path)
            if not check_linked_elf(ref, linked):
                ok = False
    if not ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
