#!/usr/bin/env python3
"""Generate a concrete Lean 4 MultiHost (`ElfHost`) witness from a linked Linux ELF binary.

Usage:
  elf_witness.py --arch {x86_64,aarch64} --elf PATH --out PATH [--asm PATH]

Verifies the linked ELF against the proved leanSPHINCS assembly (reusing `check-linked-elf.py`),
extracts exact virtual addresses, per-instruction byte sizes, `.rodata` addresses, and (on x86-64)
GOT slot addresses, and emits a standalone Lean module that:
  1. Constructs a concrete `ElfHost` instance for the real linked ELF's 8 disjoint sections.
  2. Discharges `addr_determines_offset`, `sections_disjoint`, and all 6 `PlacedIn` hypotheses.
  3. Instantiates `SphincsVerifier.verify_correct` and `SphincsVerifier.verify_confined` on the
     real linked ELF.
  4. Exhibits a concrete `MachineData` non-vacuity witness satisfying every premise simultaneously.
"""

import argparse
import importlib.util
import os
import pathlib
import re
import struct
import subprocess
import sys
import tempfile


def load_checker():
    checker_path = pathlib.Path(__file__).resolve().with_name("check-linked-elf.py")
    spec = importlib.util.spec_from_file_location("check_linked_elf", checker_path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def extract_x64_instr_sizes(elf_path, vaddr, rsize, objdump):
    """Return merged per-instruction byte sizes matching Kraken's `.nopalign` directives."""
    out = subprocess.check_output(
        [
            objdump,
            "-d",
            f"--start-address={vaddr:#x}",
            f"--stop-address={vaddr + rsize:#x}",
            str(elf_path),
        ],
        text=True,
    )
    raw = []
    for line in out.splitlines():
        m = re.match(r"^\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s)+)\s*(.*)$", line)
        if m:
            nbytes = len(m.group(2).split())
            text = m.group(3).strip()
            is_nop = text.startswith("nop") or text.startswith("data16 nop")
            raw.append((nbytes, is_nop))
    # Merge consecutive nop instructions emitted by a single `.p2align` directive.
    merged = []
    for nbytes, is_nop in raw:
        if is_nop and merged and merged[-1][1]:
            merged[-1] = (merged[-1][0] + nbytes, True)
        else:
            merged.append((nbytes, is_nop))
    sizes = [n for n, _ in merged]
    if sum(sizes) != rsize:
        raise SystemExit(f"x86-64 disassembly size mismatch at {vaddr:#x}: sum={sum(sizes)} != rsize={rsize}")
    return sizes


def inspect_elf(cle, arch, asm_path, elf_path, clang, objdump):
    target = f"{arch}-unknown-linux-musl"
    with tempfile.TemporaryDirectory() as tmp:
        ref_obj = pathlib.Path(tmp) / f"ref-{arch}.o"
        subprocess.run(
            [clang, f"--target={target}", "-c", str(asm_path), "-o", str(ref_obj)],
            check=True,
        )
        ref = cle.Elf(ref_obj)
        linked = cle.Elf(elf_path)
        if not cle.check_linked_elf(ref, linked):
            raise SystemExit(f"check-linked-elf.py rejected {elf_path}")

        # Re-walk from sphincs_verify to capture exact addresses of the 6 funcs, RC, LH, and GOT slots.
        entry_syms = [s for s in linked.syms if s["name"] == "sphincs_verify" and s["shndx"] != cle.SHN_UNDEF]
        entry_vaddr = entry_syms[0]["value"]
        ref_fns = ref.ref_functions()

        rc_shndx = None
        lh_shndx = None
        for idx, s in enumerate(ref.secs):
            if len(s["data"]) == 24 and struct.unpack("<3Q", s["data"]) == (8, 8, 10):
                lh_shndx = idx
            if len(s["data"]) == 192 and struct.unpack_from("<Q", s["data"], 0)[0] == 1:
                rc_shndx = idx
        if rc_shndx is None or lh_shndx is None:
            raise SystemExit("failed to identify roundConstants / layerHeights rodata sections in ref.o")

        funcs = {}
        rodata = {}
        got_slots = {}

        def visit_func(name, vaddr):
            if name.endswith(cle.PANIC_SUFFIXES) or name in funcs:
                return
            shndx = ref_fns[name]
            rsym = [s for s in ref.syms if s["name"] == name and s["shndx"] == shndx and s["value"] == 0]
            rbytes_full = ref.secs[shndx]["data"]
            rsize = rsym[0]["size"] if rsym and rsym[0]["size"] else len(rbytes_full)
            rrels = {o: entries for o, entries in ref.sec_relocs.get(shndx, {}).items() if o < rsize}
            lbytes, _ = linked.read_vaddr(vaddr, rsize)
            funcs[name] = (vaddr, rsize)

            if arch == "x86_64":
                for off, entries in sorted(rrels.items()):
                    rtype, symidx, addend = entries[0]
                    disp32, = struct.unpack_from("<i", lbytes, off)
                    target_info = ref.ref_target(symidx, addend)
                    if rtype in (cle.R_X86_64_GOTPCREL, cle.R_X86_64_GOTPCRELX, cle.R_X86_64_REX_GOTPCRELX):
                        callee = target_info[1]
                        got_vaddr = vaddr + off + disp32 - addend
                        if linked.etype == cle.ET_DYN:
                            _, _, target_vaddr = linked.dyn_relocs[got_vaddr]
                        else:
                            slot_bytes, _ = linked.read_vaddr(got_vaddr, 8)
                            target_vaddr, = struct.unpack("<Q", slot_bytes)
                        got_slots[callee] = got_vaddr
                        visit_func(callee, target_vaddr)
                    elif rtype in (cle.R_X86_64_PLT32, cle.R_X86_64_PC32):
                        if target_info[0] == "func":
                            visit_func(target_info[1], vaddr + off + disp32 - addend)
                        elif target_info[0] == "data":
                            ref_shndx, sec_off_plus_a = target_info[1], target_info[2]
                            target_vaddr = vaddr + off + 4 + disp32
                            base_vaddr = target_vaddr - (sec_off_plus_a + 4)
                            if ref_shndx == rc_shndx:
                                rodata["rc"] = base_vaddr
                            elif ref_shndx == lh_shndx:
                                rodata["lh"] = base_vaddr
            else:
                adrp_pages = {}
                for off in range(0, len(lbytes), 4):
                    lw, = struct.unpack_from("<I", lbytes, off)
                    entries = rrels.get(off)
                    if not entries:
                        continue
                    rtype, symidx, addend = entries[0]
                    target_info = ref.ref_target(symidx, addend)
                    if rtype in (cle.R_AARCH64_CALL26, cle.R_AARCH64_JUMP26):
                        imm26 = cle.sign_extend(lw & 0x03FFFFFF, 26)
                        visit_func(target_info[1], vaddr + off + imm26 * 4)
                    elif rtype == cle.R_AARCH64_ADR_PREL_PG_HI21:
                        rd = lw & 0x1F
                        immlo = (lw >> 29) & 0x3
                        immhi = (lw >> 5) & 0x7FFFF
                        imm21 = cle.sign_extend((immhi << 2) | immlo, 21)
                        page = ((vaddr + off) & ~0xFFF) + (imm21 << 12)
                        adrp_pages[rd] = (page, target_info)
                    elif rtype in cle.AARCH64_LO12_SHIFT:
                        rn = (lw >> 5) & 0x1F
                        page, _ = adrp_pages[rn]
                        imm12 = (lw >> 10) & 0xFFF
                        target_vaddr = page + (imm12 << cle.AARCH64_LO12_SHIFT[rtype])
                        if target_info[0] == "data":
                            base_vaddr = target_vaddr - target_info[2]
                            if target_info[1] == rc_shndx:
                                rodata["rc"] = base_vaddr
                            elif target_info[1] == lh_shndx:
                                rodata["lh"] = base_vaddr
                        elif target_info[0] == "func":
                            visit_func(target_info[1], target_vaddr)

        visit_func("sphincs_verify", entry_vaddr)

        fn_sizes = {}
        if arch == "x86_64":
            for name, (vaddr, rsize) in funcs.items():
                fn_sizes[name] = extract_x64_instr_sizes(elf_path, vaddr, rsize, objdump)

        return funcs, rodata, got_slots, fn_sizes


def emit_x64_lean(elf_path, funcs, rodata, got_slots, fn_sizes):
    fn_order = [
        ("memcpy", "Common.Memcpy.code"),
        ("memset", "Common.Memset.code"),
        ("sphincs_verify", "Sphincs.SphincsVerify.code"),
        ("_RNvCsndc0WgnAaH_9keccak2568keccak_f", "Common.KeccakF.code"),
        ("_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update", "Common.Update.code"),
        ("_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize", "Common.Finalize.code"),
    ]
    def fmt_list(xs):
        return "[" + ", ".join(str(x) for x in xs) + "]"

    size_defs = []
    sec_entries = []
    for idx, (sym, lean_code) in enumerate(fn_order):
        vaddr, rsize = funcs[sym]
        sizes = fn_sizes[sym]
        size_defs.append(f"private def instrSizes{idx} : List Nat := {fmt_list(sizes)}")
        sec_entries.append(
            f"  ({lean_code}, mkX64Layout {vaddr:#x} {lean_code} instrSizes{idx})"
        )

    rc_vaddr = rodata["rc"]
    lh_vaddr = rodata["lh"]
    got_memcpy = got_slots["memcpy"]
    got_memset = got_slots["memset"]
    sec_entries.append(
        f"  ([.label roundConstantsLabel, .byteArray ⟨rcBytes.toArray⟩], constLayout {rc_vaddr:#x})"
    )
    sec_entries.append(
        f"  ([.label layerHeightsLabel, .byteArray ⟨SphincsVerifier.layerHeightsBytes.toArray⟩], constLayout {lh_vaddr:#x})"
    )

    return f"""import NativeRustcX64.Sphincs
import NativeRustc.ElfWitness

/-!
# Concrete x86-64 Real-ELF Witness (`{elf_path}`)

Auto-generated by `formal/native/run/elf_witness.py`.
Instantiates `NativeRustcX64.ElfHost` with the exact section virtual addresses, instruction byte
sizes, `.rodata` addresses, and GOT slots of the linked Linux x86-64 ELF binary, proves all
structural invariants in Lean, instantiates `SphincsVerifier.verify_correct` and `verify_confined`,
and proves non-vacuity with an explicit `MachineData` state.
-/

namespace RealElfWitnessX64

open Kraken NativeRustc NativeRustc.MultiLayout NativeRustc.ElfWitness
open NativeRustcX64 NativeRustcX64.SphincsVerifier LeanVM.Protocol.KeccakHash

private def mkX64Layout (startAddr : UInt64) (prog : Program) (sizes : List Nat) : ElfSectionLayout :=
  let tree := NatTree.ofList (instrSizeList prog sizes)
  {{ start := Int64.ofBitVec startAddr.toBitVec,
     instrSize := fun i => max 1 (tree.get i),
     instrSize_pos := fun i => Nat.lt_of_lt_of_le (by decide : 0 < 1) (Nat.le_max_left 1 _) }}

private def constLayout (startAddr : UInt64) : ElfSectionLayout :=
  {{ start := Int64.ofBitVec startAddr.toBitVec,
     instrSize := fun _ => 1,
     instrSize_pos := fun _ => by decide }}

{chr(10).join(size_defs)}

private def realSections : List (Program × ElfSectionLayout) := [
{("," + chr(10)).join(sec_entries)}
]

private def realGotSlot (l : Kraken.Label) : Int64 :=
  if l == "memcpy" then Int64.ofBitVec ({got_memcpy:#x} : UInt64).toBitVec
  else if l == "memset" then Int64.ofBitVec ({got_memset:#x} : UInt64).toBitVec
  else 0

set_option maxRecDepth 20000 in
private theorem realSections_ok : boundsOk (sectionBounds realSections) = true := by decide +kernel
private theorem realLabels_nodup : (allLabels (realSections.map Prod.fst)).Nodup :=
  nodup_of_labelKeys (by decide +kernel)

/-- Concrete `ElfHost` instance matching the real linked Linux x86-64 ELF binary. -/
instance realElfHost : ElfHost where
  sections := realSections
  gotSlot := realGotSlot
  addr_determines_offset := boundsOk_addr_determines_offset realSections realSections_ok
  sections_disjoint := boundsOk_disjoint realSections realSections_ok

private theorem placedIn_real {{sec : Nat}} (hsec : sec < realSections.length) :
    PlacedIn (realSections[sec].1) sec 0 := by
  refine ⟨?_, fun j hj l hl => ?_⟩
  · rw [ElfHost.sectionProg_eq hsec]
    exact ⟨[], by rw [List.append_nil]; rfl⟩
  · have h := findSome?_label_of_nodup realSections realLabels_nodup hsec hj hl
    change (ElfExecutable.labels ElfHost.exe realGotSlot).label l = ElfHost.addrOf sec (0 + j)
    rw [Nat.zero_add, ElfHost.addrOf, ElfHost.sectionAt_eq hsec]
    exact h

theorem placed_memcpy : PlacedIn Common.Memcpy.code 0 0 := placedIn_real (sec := 0) (by decide)
theorem placed_memset : PlacedIn Common.Memset.code 1 0 := placedIn_real (sec := 1) (by decide)
theorem placed_sphincs : PlacedIn Sphincs.SphincsVerify.code 2 0 := placedIn_real (sec := 2) (by decide)
theorem placed_keccakF : PlacedIn Common.KeccakF.code 3 0 := placedIn_real (sec := 3) (by decide)
theorem placed_update : PlacedIn Common.Update.code 4 0 := placedIn_real (sec := 4) (by decide)
theorem placed_finalize : PlacedIn Common.Finalize.code 5 0 := placedIn_real (sec := 5) (by decide)

theorem real_rcAddr : roundConstsAddr = ({rc_vaddr:#x} : BitVec 64) := by
  have h := findSome?_label_of_nodup realSections realLabels_nodup (sec := 6) (j := 0) (by decide) (by decide) rfl
  change ((ElfExecutable.labels ElfHost.exe realGotSlot).label roundConstantsLabel).toBitVec = _
  rw [show (ElfExecutable.labels ElfHost.exe realGotSlot).label roundConstantsLabel =
    (realSections[6].2.apply realSections[6].1).addrOf 0 from h]
  decide

theorem real_lhAddr : layerHeightsAddr = ({lh_vaddr:#x} : BitVec 64) := by
  have h := findSome?_label_of_nodup realSections realLabels_nodup (sec := 7) (j := 0) (by decide) (by decide) rfl
  change ((ElfExecutable.labels ElfHost.exe realGotSlot).label layerHeightsLabel).toBitVec = _
  rw [show (ElfExecutable.labels ElfHost.exe realGotSlot).label layerHeightsLabel =
    (realSections[7].2.apply realSections[7].1).addrOf 0 from h]
  decide

/-- `verify_correct` instantiated directly on the real linked Linux x86-64 ELF binary. -/
theorem real_elf_verify_correct
    (pkBytes : Vector UInt8 pkSize) (msgBytes : Vector UInt8 msgSize) (sigBytes : Vector UInt8 sigSize)
    (initState : MachineData) (retAddr : Int64)
    (hStackOk : StackOk initState sphincsStackSize)
    (hRetAddr : BytesAt initState.dmem (rspOf initState) (wordBytes (UInt64.ofBitVec retAddr.toBitVec)))
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes initState (sphincsStackSize + retAddrSize))
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes initState (sphincsStackSize + retAddrSize))
    (hPkBuf : ReadOnlyBuf initState.dmem (reg initState .rdi) pkBytes.toList initState (sphincsStackSize + retAddrSize))
    (hMsgBuf : ReadOnlyBuf initState.dmem (reg initState .rsi) msgBytes.toList initState (sphincsStackSize + retAddrSize))
    (hSigBuf : ReadOnlyBuf initState.dmem (reg initState .rdx) sigBytes.toList initState (sphincsStackSize + retAddrSize))
    (hGotSlots : GotSlotsOk initState sphincsStackSize
      [(reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
        (layerHeightsAddr, layerHeightsSize)] ["memcpy", "memset"]) :
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = retAddr ∧
        rspOf finalState.data = rspOf initState + 8#64 ∧
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        SameOutside initState.dmem finalState.data.dmem
          (InRange (stackBottomAddr initState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept initState finalState.data)
      ⟨initState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ :=
  @SphincsVerifier.verify_correct realElfHost
    2 0 placed_sphincs 0 0 placed_memcpy 1 0 placed_memset
    3 0 placed_keccakF 4 0 placed_update 5 0 placed_finalize
    pkBytes msgBytes sigBytes initState retAddr hStackOk hRetAddr
    hRoundConsts hLayerHeights hPkBuf hMsgBuf hSigBuf hGotSlots

/-- `verify_confined` instantiated directly on the real linked Linux x86-64 ELF binary. -/
theorem real_elf_verify_confined
    (pkBytes : Vector UInt8 pkSize) (msgBytes : Vector UInt8 msgSize) (sigBytes : Vector UInt8 sigSize)
    (initState : MachineData) (retAddr : Int64)
    (hStackOk : StackOk initState sphincsStackSize)
    (hRetAddr : BytesAt initState.dmem (rspOf initState) (wordBytes (UInt64.ofBitVec retAddr.toBitVec)))
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes initState (sphincsStackSize + retAddrSize))
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes initState (sphincsStackSize + retAddrSize))
    (hPkBuf : ReadOnlyBuf initState.dmem (reg initState .rdi) pkBytes.toList initState (sphincsStackSize + retAddrSize))
    (hMsgBuf : ReadOnlyBuf initState.dmem (reg initState .rsi) msgBytes.toList initState (sphincsStackSize + retAddrSize))
    (hSigBuf : ReadOnlyBuf initState.dmem (reg initState .rdx) sigBytes.toList initState (sphincsStackSize + retAddrSize))
    (hGotSlots : GotSlotsOk initState sphincsStackSize
      [(reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
        (layerHeightsAddr, layerHeightsSize)] ["memcpy", "memset"]) :
    let allowedRegions := [
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize + retAddrSize),
      (reg initState .rdi, pkSize), (reg initState .rsi, msgSize), (reg initState .rdx, sigSize),
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize),
      (gotAddr "memcpy", gotSlotSize), (gotAddr "memset", gotSlotSize)]
    let confinedState := {{ initState with dmem := restrictMemory initState.dmem allowedRegions }}
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = retAddr ∧
        rspOf finalState.data = rspOf confinedState + 8#64 ∧
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept confinedState finalState.data)
      ⟨confinedState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ :=
  @SphincsVerifier.verify_confined realElfHost
    2 0 placed_sphincs 0 0 placed_memcpy 1 0 placed_memset
    3 0 placed_keccakF 4 0 placed_update 5 0 placed_finalize
    pkBytes msgBytes sigBytes initState retAddr hStackOk hRetAddr
    hRoundConsts hLayerHeights hPkBuf hMsgBuf hSigBuf hGotSlots

/-! ## Non-vacuity witness: concrete `MachineData` satisfying every premise simultaneously -/

private def storeBytes (d : DataMem) (base : BitVec 64) (bs : List UInt8) : DataMem :=
  (bs.zipIdx).foldl (fun m (b, i) => m.insert (base + BitVec.ofNat 64 i) b) d

private theorem get?_storeBytes_inside (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : bs.length ≤ 2 ^ 64) {{i : Nat}} (hi : i < bs.length) :
    (storeBytes d base bs).get? (base + BitVec.ofNat 64 i) = some bs[i] := by
  have hgen : ∀ (l : List (UInt8 × Nat)) (m : DataMem) (p : BitVec 64),
      (∀ x ∈ l, x.2 < 2 ^ 64) → (l.map Prod.snd).Nodup →
      (∀ (b : UInt8) (k : Nat), (b, k) ∈ l → p = base + BitVec.ofNat 64 k →
        (l.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m).get? p = some b) := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro m p hlt hnd b k hmem hp
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with hEq | htl
      · rcases hd with ⟨b', k'⟩
        cases hEq
        subst hp
        have hnot : ∀ x ∈ tl, base + BitVec.ofNat 64 x.2 ≠ base + BitVec.ofNat 64 k := by
          intro x hx heq
          have hbv : BitVec.ofNat 64 x.2 = BitVec.ofNat 64 k := by
            have := congrArg (fun z => z - base) heq
            simpa using this
          have hxlt := hlt x (List.mem_cons_of_mem _ hx)
          have hklt := hlt (b, k) List.mem_cons_self
          have hnat : x.2 = k := by
            have := congrArg BitVec.toNat hbv
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hklt] at this
            exact this
          exact hnd.1 (hnat ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
        have hkeep : ∀ (l' : List (UInt8 × Nat)) (m' : DataMem),
            (∀ x ∈ l', base + BitVec.ofNat 64 x.2 ≠ base + BitVec.ofNat 64 k) →
            (l'.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m').get?
              (base + BitVec.ofNat 64 k) = m'.get? (base + BitVec.ofNat 64 k) := by
          intro l'
          induction l' with
          | nil => intro _ _; rfl
          | cons y ys ihy =>
            intro m' hy
            simp only [List.foldl_cons]
            rw [ihy _ (fun x hx => hy x (List.mem_cons_of_mem _ hx))]
            simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
            have hne : (base + BitVec.ofNat 64 y.2 == base + BitVec.ofNat 64 k) = false :=
              beq_false_of_ne (hy y List.mem_cons_self)
            simp [hne]
        simp only [List.foldl_cons]
        rw [hkeep tl _ hnot]
        simp [Std.ExtHashMap.get?_eq_getElem?]
      · simp only [List.foldl_cons]
        exact ih _ p (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) hnd.2 b k htl hp
  have hzip_mem : (bs[i], i) ∈ bs.zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp⟩
  exact hgen bs.zipIdx d (base + BitVec.ofNat 64 i)
    (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_zipIdx] at hj
      simp only [List.getElem_zipIdx, Nat.zero_add]
      omega)
    (by
      rw [show bs.zipIdx.map Prod.snd = List.range bs.length by
        apply List.ext_getElem (by simp)
        intro j h1 h2; simp]
      exact List.nodup_range)
    bs[i] i hzip_mem rfl

private theorem get?_storeBytes_outside (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : base.toNat + bs.length ≤ 2 ^ 64) {{p : BitVec 64}}
    (hout : p.toNat < base.toNat ∨ base.toNat + bs.length ≤ p.toNat) :
    (storeBytes d base bs).get? p = d.get? p := by
  have hne : ∀ x ∈ bs.zipIdx, base + BitVec.ofNat 64 x.2 ≠ p := by
    intro x hx heq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_zipIdx] at hj
    simp only [List.getElem_zipIdx, Nat.zero_add] at heq
    have hnat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : base.toNat + j < 2 ^ 64)] at hnat
    omega
  have hkeep : ∀ (l : List (UInt8 × Nat)) (m : DataMem),
      (∀ x ∈ l, base + BitVec.ofNat 64 x.2 ≠ p) →
      (l.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m).get? p = m.get? p := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons y ys ih =>
      intro m hy
      simp only [List.foldl_cons]
      rw [ih _ (fun x hx => hy x (List.mem_cons_of_mem _ hx))]
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      have hbf : (base + BitVec.ofNat 64 y.2 == p) = false := beq_false_of_ne (hy y List.mem_cons_self)
      simp [hbf]
  exact hkeep bs.zipIdx d hne

private def storeZeros (d : DataMem) (base : BitVec 64) (n : Nat) : DataMem :=
  storeBytes d base (List.replicate n 0)

private theorem bytesAt_of_storeBytes (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : bs.length ≤ 2 ^ 64) : BytesAt (storeBytes d base bs) base bs :=
  fun _ hi => get?_storeBytes_inside d base bs hno hi

private theorem bytesAt_of_storeZeros (d : DataMem) (base : BitVec 64) (n : Nat)
    (hno : n ≤ 2 ^ 64) : BytesAt (storeZeros d base n) base (List.replicate n 0) :=
  bytesAt_of_storeBytes d base (List.replicate n 0) (by simpa using hno)

private theorem bytesAt_storeBytes_other {{d : DataMem}} {{a base : BitVec 64}} {{bs bs' : List UInt8}}
    (h : BytesAt d a bs) (hnoA : a.toNat + bs.length ≤ 2 ^ 64)
    (hnoB : base.toNat + bs'.length ≤ 2 ^ 64)
    (hdisj : a.toNat + bs.length ≤ base.toNat ∨ base.toNat + bs'.length ≤ a.toNat) :
    BytesAt (storeBytes d base bs') a bs := by
  intro i hi
  rw [get?_storeBytes_outside d base bs' hnoB (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : a.toNat + i < 2 ^ 64)]
    omega)]
  exact h i hi

private theorem bytesAt_storeZeros_other {{d : DataMem}} {{a base : BitVec 64}} {{bs : List UInt8}} {{n : Nat}}
    (h : BytesAt d a bs) (hnoA : a.toNat + bs.length ≤ 2 ^ 64)
    (hnoB : base.toNat + n ≤ 2 ^ 64)
    (hdisj : a.toNat + bs.length ≤ base.toNat ∨ base.toNat + n ≤ a.toNat) :
    BytesAt (storeZeros d base n) a bs :=
  bytesAt_storeBytes_other h hnoA (by simpa using hnoB) (by simpa using hdisj)

private def wPkAddr : UInt64 := 0x10000000
private def wMsgAddr : UInt64 := 0x10001000
private def wSigAddr : UInt64 := 0x10002000
private def wRspAddr : UInt64 := 0x70000000
private def wRetAddr : Int64 := 0x12345678

private def wd0 : DataMem := {{}}
private def wd1 : DataMem := storeZeros wd0 (wRspAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize) sphincsStackSize
private def wd2 : DataMem := storeBytes wd1 wRspAddr.toBitVec (wordBytes (UInt64.ofBitVec wRetAddr.toBitVec))
private def wd3 : DataMem := storeBytes wd2 ({rc_vaddr:#x} : BitVec 64) roundConstsBytes
private def wd4 : DataMem := storeBytes wd3 ({lh_vaddr:#x} : BitVec 64) layerHeightsBytes
private def wd5 : DataMem := storeZeros wd4 wPkAddr.toBitVec pkSize
private def wd6 : DataMem := storeZeros wd5 wMsgAddr.toBitVec msgSize
private def wd7 : DataMem := storeZeros wd6 wSigAddr.toBitVec sigSize
private def wd8 : DataMem := storeBytes wd7 ({got_memcpy:#x} : BitVec 64) (Int.toBytes 8 (Labels.label "memcpy").toBitVec.toInt)
private def witnessDmem : DataMem := storeBytes wd8 ({got_memset:#x} : BitVec 64) (Int.toBytes 8 (Labels.label "memset").toBitVec.toInt)

private def witnessState : MachineData :=
  {{ regs := {{ rsp := wRspAddr, rdi := wPkAddr, rsi := wMsgAddr, rdx := wSigAddr }},
     dmem := witnessDmem }}

private theorem witness_premises :
    StackOk witnessState sphincsStackSize ∧
    BytesAt witnessState.dmem (rspOf witnessState) (wordBytes (UInt64.ofBitVec wRetAddr.toBitVec)) ∧
    ReadOnlyBuf witnessState.dmem roundConstsAddr roundConstsBytes witnessState (sphincsStackSize + retAddrSize) ∧
    ReadOnlyBuf witnessState.dmem layerHeightsAddr layerHeightsBytes witnessState (sphincsStackSize + retAddrSize) ∧
    ReadOnlyBuf witnessState.dmem (reg witnessState .rdi) (Vector.replicate pkSize 0).toList witnessState (sphincsStackSize + retAddrSize) ∧
    ReadOnlyBuf witnessState.dmem (reg witnessState .rsi) (Vector.replicate msgSize 0).toList witnessState (sphincsStackSize + retAddrSize) ∧
    ReadOnlyBuf witnessState.dmem (reg witnessState .rdx) (Vector.replicate sigSize 0).toList witnessState (sphincsStackSize + retAddrSize) ∧
    GotSlotsOk witnessState sphincsStackSize
      [(reg witnessState .rdi, pkSize), (reg witnessState .rsi, msgSize), (reg witnessState .rdx, sigSize),
        (layerHeightsAddr, layerHeightsSize)] ["memcpy", "memset"] := by
  have hrcLen : roundConstsBytes.length = 192 := roundConstsSize_eq
  have hlhLen : layerHeightsBytes.length = 24 := layerHeightsBytes_length
  have hgot1Len : (Int.toBytes 8 (Labels.label "memcpy").toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  have hgot2Len : (Int.toBytes 8 (Labels.label "memset").toBitVec.toInt).length = 8 := Int.toBytes_length _ _
  have hretLen : (wordBytes (UInt64.ofBitVec wRetAddr.toBitVec)).length = 8 := by decide
  have hpkLen : (Vector.replicate pkSize (0 : UInt8)).toList = List.replicate pkSize 0 := by simp
  have hmsgLen : (Vector.replicate msgSize (0 : UInt8)).toList = List.replicate msgSize 0 := by simp
  have hsigLen : (Vector.replicate sigSize (0 : UInt8)).toList = List.replicate sigSize 0 := by simp
  have hdmem : witnessState.dmem = witnessDmem := by unfold witnessState; rfl
  have hrsp : rspOf witnessState = wRspAddr.toBitVec := rfl
  have hrdi : reg witnessState .rdi = wPkAddr.toBitVec := rfl
  have hrsi : reg witnessState .rsi = wMsgAddr.toBitVec := rfl
  have hrdx : reg witnessState .rdx = wSigAddr.toBitVec := rfl
  have hstkToNat : (wRspAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize).toNat = 0x70000000 - 22304 := by
    rw [sphincsStackSize_eq]; decide
  have hrspToNat : wRspAddr.toBitVec.toNat = 0x70000000 := rfl
  have hpkToNat : wPkAddr.toBitVec.toNat = 0x10000000 := rfl
  have hmsgToNat : wMsgAddr.toBitVec.toNat = 0x10001000 := rfl
  have hsigToNat : wSigAddr.toBitVec.toNat = 0x10002000 := rfl
  have hrcToNat : ({rc_vaddr:#x} : BitVec 64).toNat = {rc_vaddr:#x} := rfl
  have hlhToNat : ({lh_vaddr:#x} : BitVec 64).toNat = {lh_vaddr:#x} := rfl
  have hgot1ToNat : ({got_memcpy:#x} : BitVec 64).toNat = {got_memcpy:#x} := rfl
  have hgot2ToNat : ({got_memset:#x} : BitVec 64).toNat = {got_memset:#x} := rfl
  have hstkSz : sphincsStackSize = 22304 := sphincsStackSize_eq
  have hpkSz : pkSize = 32 := rfl
  have hmsgSz : msgSize = 32 := rfl
  have hsigSz : sigSize = 7740 := rfl
  have hretB : BytesAt witnessDmem wRspAddr.toBitVec (wordBytes (UInt64.ofBitVec wRetAddr.toBitVec)) := by
    have b2 : BytesAt wd2 wRspAddr.toBitVec _ := bytesAt_of_storeBytes _ _ _ (by omega)
    have b3 : BytesAt wd3 wRspAddr.toBitVec _ := bytesAt_storeBytes_other b2 (by omega) (by omega) (by omega)
    have b4 : BytesAt wd4 wRspAddr.toBitVec _ := bytesAt_storeBytes_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 wRspAddr.toBitVec _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    have b6 : BytesAt wd6 wRspAddr.toBitVec _ := bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
    have b7 : BytesAt wd7 wRspAddr.toBitVec _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 wRspAddr.toBitVec _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hstackLowB : BytesAt witnessDmem (wRspAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize)
      (List.replicate sphincsStackSize 0) := by
    have hlen : (List.replicate sphincsStackSize (0 : UInt8)).length = sphincsStackSize := List.length_replicate
    have b1 : BytesAt wd1 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b2 : BytesAt wd2 _ _ := bytesAt_storeBytes_other b1 (by omega) (by omega) (by omega)
    have b3 : BytesAt wd3 _ _ := bytesAt_storeBytes_other b2 (by omega) (by omega) (by omega)
    have b4 : BytesAt wd4 _ _ := bytesAt_storeBytes_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    have b6 : BytesAt wd6 _ _ := bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
    have b7 : BytesAt wd7 _ _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hStackOk : StackOk witnessState sphincsStackSize := by
    refine ⟨by rw [hrsp]; omega, by rw [hrsp]; omega, fun i hi => ?_⟩
    rw [hrsp, hdmem]
    by_cases hlt : i < sphincsStackSize
    · have hb := hstackLowB i (by simpa using hlt)
      rw [hb]; rfl
    · have hj : i - sphincsStackSize < 8 := by omega
      have haddr : (wRspAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize) + BitVec.ofNat 64 i =
          wRspAddr.toBitVec + BitVec.ofNat 64 (i - sphincsStackSize) := by
        have hsplit : BitVec.ofNat 64 i = BitVec.ofNat 64 sphincsStackSize + BitVec.ofNat 64 (i - sphincsStackSize) := by
          rw [← BitVec.ofNat_add, Nat.add_sub_of_le (by omega)]
        rw [hsplit, ← BitVec.add_assoc, BitVec.sub_add_cancel]
      have hb := hretB (i - sphincsStackSize) (by rw [hretLen]; exact hj)
      rw [haddr, hb]; rfl
  have hrcB : BytesAt witnessDmem ({rc_vaddr:#x} : BitVec 64) roundConstsBytes := by
    have b3 : BytesAt wd3 _ _ := bytesAt_of_storeBytes _ _ _ (by omega)
    have b4 : BytesAt wd4 _ _ := bytesAt_storeBytes_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    have b6 : BytesAt wd6 _ _ := bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
    have b7 : BytesAt wd7 _ _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hlhB : BytesAt witnessDmem ({lh_vaddr:#x} : BitVec 64) layerHeightsBytes := by
    have b4 : BytesAt wd4 _ _ := bytesAt_of_storeBytes _ _ _ (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    have b6 : BytesAt wd6 _ _ := bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
    have b7 : BytesAt wd7 _ _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hpkB : BytesAt witnessDmem wPkAddr.toBitVec (List.replicate pkSize 0) := by
    have hlen : (List.replicate pkSize (0 : UInt8)).length = pkSize := List.length_replicate
    have b5 : BytesAt wd5 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b6 : BytesAt wd6 _ _ := bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
    have b7 : BytesAt wd7 _ _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hmsgB : BytesAt witnessDmem wMsgAddr.toBitVec (List.replicate msgSize 0) := by
    have hlen : (List.replicate msgSize (0 : UInt8)).length = msgSize := List.length_replicate
    have b6 : BytesAt wd6 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b7 : BytesAt wd7 _ _ := bytesAt_storeZeros_other b6 (by omega) (by omega) (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hsigB : BytesAt witnessDmem wSigAddr.toBitVec (List.replicate sigSize 0) := by
    have hlen : (List.replicate sigSize (0 : UInt8)).length = sigSize := List.length_replicate
    have b7 : BytesAt wd7 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b8 : BytesAt wd8 _ _ := bytesAt_storeBytes_other b7 (by omega) (by omega) (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hgot1B : BytesAt witnessDmem ({got_memcpy:#x} : BitVec 64)
      (Int.toBytes 8 (Labels.label "memcpy").toBitVec.toInt) := by
    have b8 : BytesAt wd8 _ _ := bytesAt_of_storeBytes _ _ _ (by omega)
    exact bytesAt_storeBytes_other b8 (by omega) (by omega) (by omega)
  have hgot2B : BytesAt witnessDmem ({got_memset:#x} : BitVec 64)
      (Int.toBytes 8 (Labels.label "memset").toBitVec.toInt) :=
    bytesAt_of_storeBytes _ _ _ (by omega)
  refine ⟨hStackOk, by rw [hdmem, hrsp]; exact hretB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hdmem, real_rcAddr]; exact hrcB, by rw [real_rcAddr]; unfold NoWrap; omega,
      by rw [real_rcAddr]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hrsp]; omega⟩
  · refine ⟨by rw [hdmem, real_lhAddr]; exact hlhB, by rw [real_lhAddr]; unfold NoWrap; omega,
      by rw [real_lhAddr]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hrsp]; omega⟩
  · refine ⟨by rw [hdmem, hrdi, hpkLen]; exact hpkB, by rw [hrdi, hpkLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hrdi, hpkLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hrsp]; omega⟩
  · refine ⟨by rw [hdmem, hrsi, hmsgLen]; exact hmsgB, by rw [hrsi, hmsgLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hrsi, hmsgLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hrsp]; omega⟩
  · refine ⟨by rw [hdmem, hrdx, hsigLen]; exact hsigB, by rw [hrdx, hsigLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hrdx, hsigLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hrsp]; omega⟩
  · refine ⟨fun l hl => ?_, ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · refine ⟨by rw [hdmem]; exact hgot1B, by change NoWrap ({got_memcpy:#x} : BitVec 64) 8; unfold NoWrap; omega,
          by change Apart ({got_memcpy:#x} : BitVec 64) 8 (rspOf witnessState - BitVec.ofNat 64 sphincsStackSize) (sphincsStackSize + 8)
             rw [hrsp]; unfold Apart; omega,
          fun a ha => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · change Apart ({got_memcpy:#x} : BitVec 64) 8 wPkAddr.toBitVec pkSize; unfold Apart; omega
        · change Apart ({got_memcpy:#x} : BitVec 64) 8 wMsgAddr.toBitVec msgSize; unfold Apart; omega
        · change Apart ({got_memcpy:#x} : BitVec 64) 8 wSigAddr.toBitVec sigSize; unfold Apart; omega
        · rw [real_lhAddr]; change Apart ({got_memcpy:#x} : BitVec 64) 8 ({lh_vaddr:#x} : BitVec 64) 24; unfold Apart; omega
      · refine ⟨by rw [hdmem]; exact hgot2B, by change NoWrap ({got_memset:#x} : BitVec 64) 8; unfold NoWrap; omega,
          by change Apart ({got_memset:#x} : BitVec 64) 8 (rspOf witnessState - BitVec.ofNat 64 sphincsStackSize) (sphincsStackSize + 8)
             rw [hrsp]; unfold Apart; omega,
          fun a ha => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · change Apart ({got_memset:#x} : BitVec 64) 8 wPkAddr.toBitVec pkSize; unfold Apart; omega
        · change Apart ({got_memset:#x} : BitVec 64) 8 wMsgAddr.toBitVec msgSize; unfold Apart; omega
        · change Apart ({got_memset:#x} : BitVec 64) 8 wSigAddr.toBitVec sigSize; unfold Apart; omega
        · rw [real_lhAddr]; change Apart ({got_memset:#x} : BitVec 64) 8 ({lh_vaddr:#x} : BitVec 64) 24; unfold Apart; omega
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.Pairwise.nil, and_true, forall_eq]
      refine ⟨?_, fun _ h => h.elim⟩
      change Apart ({got_memcpy:#x} : BitVec 64) 8 ({got_memset:#x} : BitVec 64) 8
      unfold Apart; omega

/-- Concrete non-vacuity proof: an explicit `MachineData` state satisfies every premise of
`verify_correct` on the real linked Linux x86-64 ELF binary. -/
theorem real_elf_non_vacuous :
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = wRetAddr ∧
        rspOf finalState.data = rspOf witnessState + 8#64 ∧
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk (Vector.replicate pkSize 0).toList)
          (Native.SphincsVerifier.decodeMsg (Vector.replicate msgSize 0).toList)
          (Native.SphincsVerifier.decodeSig (Vector.replicate sigSize 0).toList) then 1 else 0) ∧
        SameOutside witnessState.dmem finalState.data.dmem
          (InRange (stackBottomAddr witnessState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept witnessState finalState.data)
      ⟨witnessState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := witness_premises
  exact real_elf_verify_correct
    (Vector.replicate pkSize 0) (Vector.replicate msgSize 0) (Vector.replicate sigSize 0)
    witnessState wRetAddr h1 h2 h3 h4 h5 h6 h7 h8

/-- Concrete non-vacuity proof for `verify_confined` on the real linked Linux x86-64 ELF binary. -/
theorem real_elf_confined_non_vacuous :
    let allowedRegions := [
      (stackBottomAddr witnessState sphincsStackSize, sphincsStackSize + retAddrSize),
      (reg witnessState .rdi, pkSize), (reg witnessState .rsi, msgSize), (reg witnessState .rdx, sigSize),
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize),
      (gotAddr "memcpy", gotSlotSize), (gotAddr "memset", gotSlotSize)]
    let confinedState := {{ witnessState with dmem := restrictMemory witnessState.dmem allowedRegions }}
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = wRetAddr ∧
        rspOf finalState.data = rspOf confinedState + 8#64 ∧
        reg finalState.data .rax = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk (Vector.replicate pkSize 0).toList)
          (Native.SphincsVerifier.decodeMsg (Vector.replicate msgSize 0).toList)
          (Native.SphincsVerifier.decodeSig (Vector.replicate sigSize 0).toList) then 1 else 0) ∧
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept confinedState finalState.data)
      ⟨confinedState, label NativeRustcX64.Sphincs.SphincsVerify.entryLabel⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := witness_premises
  exact real_elf_verify_confined
    (Vector.replicate pkSize 0) (Vector.replicate msgSize 0) (Vector.replicate sigSize 0)
    witnessState wRetAddr h1 h2 h3 h4 h5 h6 h7 h8

#print axioms real_elf_verify_correct
#print axioms real_elf_verify_confined
#print axioms real_elf_non_vacuous
#print axioms real_elf_confined_non_vacuous

end RealElfWitnessX64
"""


def emit_arm64_lean(elf_path, funcs, rodata):
    fn_order = [
        ("memcpy", "Common.Memcpy.code"),
        ("memset", "Common.Memset.code"),
        ("sphincs_verify", "Sphincs.SphincsVerify.code"),
        ("_RNvCsndc0WgnAaH_9keccak2568keccak_f", "Common.KeccakF.code"),
        ("_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher6update", "Common.Update.code"),
        ("_RNvMCsndc0WgnAaH_9keccak256NtB2_6Hasher8finalize", "Common.Finalize.code"),
    ]
    sec_entries = []
    for sym, lean_code in fn_order:
        vaddr, _ = funcs[sym]
        sec_entries.append(f"  ({lean_code}, arm4Layout {vaddr:#x})")

    rc_vaddr = rodata["rc"]
    lh_vaddr = rodata["lh"]
    sec_entries.append(
        f"  ([.label roundConstantsLabel, .byteArray ⟨rcBytes.toArray⟩], arm4Layout {rc_vaddr:#x})"
    )
    sec_entries.append(
        f"  ([.label layerHeightsLabel, .byteArray ⟨SphincsVerifier.layerHeightsBytes.toArray⟩], arm4Layout {lh_vaddr:#x})"
    )

    return f"""import NativeRustcArm.Sphincs
import NativeRustc.ElfWitness

/-!
# Concrete AArch64 Real-ELF Witness (`{elf_path}`)

Auto-generated by `formal/native/run/elf_witness.py`.
Instantiates `NativeRustcArm.ElfHost` with the exact section virtual addresses and `.rodata`
addresses of the linked Linux AArch64 ELF binary, proves all structural invariants in Lean,
instantiates `SphincsVerifier.verify_correct` and `verify_confined`, and proves non-vacuity with
an explicit `MachineData` state.
-/

namespace RealElfWitnessArm

open Kraken NativeRustc NativeRustc.MultiLayout NativeRustc.ElfWitness
open NativeRustcArm NativeRustcArm.SphincsVerifier

private def arm4Layout (startAddr : UInt64) : ElfSectionLayout :=
  {{ start := Int64.ofBitVec startAddr.toBitVec,
     instrSize := fun _ => 4,
     instrSize_pos := fun _ => by decide }}

private def realSections : List (Program × ElfSectionLayout) := [
{("," + chr(10)).join(sec_entries)}
]

set_option maxRecDepth 20000 in
private theorem realSections_ok : boundsOk (sectionBounds realSections) = true := by decide +kernel
private theorem realLabels_nodup : (allLabels (realSections.map Prod.fst)).Nodup :=
  nodup_of_labelKeys (by decide +kernel)

/-- Concrete `ElfHost` instance matching the real linked Linux AArch64 ELF binary. -/
instance realElfHost : ElfHost where
  sections := realSections
  addr_determines_offset := boundsOk_addr_determines_offset realSections realSections_ok
  sections_disjoint := boundsOk_disjoint realSections realSections_ok

private theorem placedIn_real {{sec : Nat}} (hsec : sec < realSections.length) :
    PlacedIn (realSections[sec].1) sec 0 := by
  refine ⟨?_, fun j hj l hl => ?_⟩
  · rw [ElfHost.sectionProg_eq hsec]
    exact ⟨[], by rw [List.append_nil]; rfl⟩
  · have h := findSome?_label_of_nodup realSections realLabels_nodup hsec hj hl
    change (ElfExecutable.labels ElfHost.exe).label l = ElfHost.addrOf sec (0 + j)
    rw [Nat.zero_add, ElfHost.addrOf, ElfHost.sectionAt_eq hsec]
    exact h

theorem placed_memcpy : PlacedIn Common.Memcpy.code 0 0 := placedIn_real (sec := 0) (by decide)
theorem placed_memset : PlacedIn Common.Memset.code 1 0 := placedIn_real (sec := 1) (by decide)
theorem placed_sphincs : PlacedIn Sphincs.SphincsVerify.code 2 0 := placedIn_real (sec := 2) (by decide)
theorem placed_keccakF : PlacedIn Common.KeccakF.code 3 0 := placedIn_real (sec := 3) (by decide)
theorem placed_update : PlacedIn Common.Update.code 4 0 := placedIn_real (sec := 4) (by decide)
theorem placed_finalize : PlacedIn Common.Finalize.code 5 0 := placedIn_real (sec := 5) (by decide)

theorem real_rcAddr : roundConstsAddr = ({rc_vaddr:#x} : BitVec 64) := by
  have h := findSome?_label_of_nodup realSections realLabels_nodup (sec := 6) (j := 0) (by decide) (by decide) rfl
  change ((ElfExecutable.labels ElfHost.exe).label roundConstantsLabel).toBitVec = _
  rw [show (ElfExecutable.labels ElfHost.exe).label roundConstantsLabel =
    (realSections[6].2.apply realSections[6].1).addrOf 0 from h]
  decide

theorem real_lhAddr : layerHeightsAddr = ({lh_vaddr:#x} : BitVec 64) := by
  have h := findSome?_label_of_nodup realSections realLabels_nodup (sec := 7) (j := 0) (by decide) (by decide) rfl
  change ((ElfExecutable.labels ElfHost.exe).label layerHeightsLabel).toBitVec = _
  rw [show (ElfExecutable.labels ElfHost.exe).label layerHeightsLabel =
    (realSections[7].2.apply realSections[7].1).addrOf 0 from h]
  decide

/-- `verify_correct` instantiated directly on the real linked Linux AArch64 ELF binary. -/
theorem real_elf_verify_correct
    (pkBytes : Vector UInt8 pkSize) (msgBytes : Vector UInt8 msgSize) (sigBytes : Vector UInt8 sigSize)
    (initState : MachineData) (hStackOk : StackOk initState sphincsStackSize)
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes initState sphincsStackSize)
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes initState sphincsStackSize)
    (hPkBuf : ReadOnlyBuf initState.dmem initState.regs.X0.toBitVec pkBytes.toList initState sphincsStackSize)
    (hMsgBuf : ReadOnlyBuf initState.dmem initState.regs.X1.toBitVec msgBytes.toList initState sphincsStackSize)
    (hSigBuf : ReadOnlyBuf initState.dmem initState.regs.X2.toBitVec sigBytes.toList initState sphincsStackSize) :
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = returnAddrOf initState ∧
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        SameOutside initState.dmem finalState.data.dmem
          (InRange (stackBottomAddr initState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept initState finalState.data)
      ⟨initState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ :=
  @SphincsVerifier.verify_correct realElfHost
    2 0 0 0 1 0 3 0 4 0 5 0
    placed_sphincs placed_memcpy placed_memset placed_keccakF placed_update placed_finalize
    pkBytes msgBytes sigBytes initState hStackOk
    hRoundConsts hLayerHeights hPkBuf hMsgBuf hSigBuf

/-- `verify_confined` instantiated directly on the real linked Linux AArch64 ELF binary. -/
theorem real_elf_verify_confined
    (pkBytes : Vector UInt8 pkSize) (msgBytes : Vector UInt8 msgSize) (sigBytes : Vector UInt8 sigSize)
    (initState : MachineData) (hStackOk : StackOk initState sphincsStackSize)
    (hRoundConsts : ReadOnlyBuf initState.dmem roundConstsAddr roundConstsBytes initState sphincsStackSize)
    (hLayerHeights : ReadOnlyBuf initState.dmem layerHeightsAddr layerHeightsBytes initState sphincsStackSize)
    (hPkBuf : ReadOnlyBuf initState.dmem initState.regs.X0.toBitVec pkBytes.toList initState sphincsStackSize)
    (hMsgBuf : ReadOnlyBuf initState.dmem initState.regs.X1.toBitVec msgBytes.toList initState sphincsStackSize)
    (hSigBuf : ReadOnlyBuf initState.dmem initState.regs.X2.toBitVec sigBytes.toList initState sphincsStackSize) :
    let allowedRegions := [
      (stackBottomAddr initState sphincsStackSize, sphincsStackSize),
      (initState.regs.X0.toBitVec, pkSize), (initState.regs.X1.toBitVec, msgSize),
      (initState.regs.X2.toBitVec, sigSize),
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize)]
    let confinedState := {{ initState with dmem := restrictMemory initState.dmem allowedRegions }}
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = returnAddrOf confinedState ∧
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk pkBytes.toList)
          (Native.SphincsVerifier.decodeMsg msgBytes.toList)
          (Native.SphincsVerifier.decodeSig sigBytes.toList) then 1 else 0) ∧
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept confinedState finalState.data)
      ⟨confinedState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ :=
  @SphincsVerifier.verify_confined realElfHost
    2 0 0 0 1 0 3 0 4 0 5 0
    placed_sphincs placed_memcpy placed_memset placed_keccakF placed_update placed_finalize
    pkBytes msgBytes sigBytes initState hStackOk
    hRoundConsts hLayerHeights hPkBuf hMsgBuf hSigBuf

/-! ## Non-vacuity witness: concrete `MachineData` satisfying every premise simultaneously -/

private def storeBytes (d : DataMem) (base : BitVec 64) (bs : List UInt8) : DataMem :=
  (bs.zipIdx).foldl (fun m (b, i) => m.insert (base + BitVec.ofNat 64 i) b) d

private theorem get?_storeBytes_inside (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : bs.length ≤ 2 ^ 64) {{i : Nat}} (hi : i < bs.length) :
    (storeBytes d base bs).get? (base + BitVec.ofNat 64 i) = some bs[i] := by
  have hgen : ∀ (l : List (UInt8 × Nat)) (m : DataMem) (p : BitVec 64),
      (∀ x ∈ l, x.2 < 2 ^ 64) → (l.map Prod.snd).Nodup →
      (∀ (b : UInt8) (k : Nat), (b, k) ∈ l → p = base + BitVec.ofNat 64 k →
        (l.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m).get? p = some b) := by
    intro l
    induction l with
    | nil => intro _ _ _ _ _ _ hmem; cases hmem
    | cons hd tl ih =>
      intro m p hlt hnd b k hmem hp
      simp only [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hmem with hEq | htl
      · rcases hd with ⟨b', k'⟩
        cases hEq
        subst hp
        have hnot : ∀ x ∈ tl, base + BitVec.ofNat 64 x.2 ≠ base + BitVec.ofNat 64 k := by
          intro x hx heq
          have hbv : BitVec.ofNat 64 x.2 = BitVec.ofNat 64 k := by
            have := congrArg (fun z => z - base) heq
            simpa using this
          have hxlt := hlt x (List.mem_cons_of_mem _ hx)
          have hklt := hlt (b, k) List.mem_cons_self
          have hnat : x.2 = k := by
            have := congrArg BitVec.toNat hbv
            rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hklt] at this
            exact this
          exact hnd.1 (hnat ▸ List.mem_map.mpr ⟨x, hx, rfl⟩)
        have hkeep : ∀ (l' : List (UInt8 × Nat)) (m' : DataMem),
            (∀ x ∈ l', base + BitVec.ofNat 64 x.2 ≠ base + BitVec.ofNat 64 k) →
            (l'.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m').get?
              (base + BitVec.ofNat 64 k) = m'.get? (base + BitVec.ofNat 64 k) := by
          intro l'
          induction l' with
          | nil => intro _ _; rfl
          | cons y ys ihy =>
            intro m' hy
            simp only [List.foldl_cons]
            rw [ihy _ (fun x hx => hy x (List.mem_cons_of_mem _ hx))]
            simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
            have hne : (base + BitVec.ofNat 64 y.2 == base + BitVec.ofNat 64 k) = false :=
              beq_false_of_ne (hy y List.mem_cons_self)
            simp [hne]
        simp only [List.foldl_cons]
        rw [hkeep tl _ hnot]
        simp [Std.ExtHashMap.get?_eq_getElem?]
      · simp only [List.foldl_cons]
        exact ih _ p (fun x hx => hlt x (List.mem_cons_of_mem _ hx)) hnd.2 b k htl hp
  have hzip_mem : (bs[i], i) ∈ bs.zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simp [hi], by simp⟩
  exact hgen bs.zipIdx d (base + BitVec.ofNat 64 i)
    (fun x hx => by
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
      simp only [List.length_zipIdx] at hj
      simp only [List.getElem_zipIdx, Nat.zero_add]
      omega)
    (by
      rw [show bs.zipIdx.map Prod.snd = List.range bs.length by
        apply List.ext_getElem (by simp)
        intro j h1 h2; simp]
      exact List.nodup_range)
    bs[i] i hzip_mem rfl

private theorem get?_storeBytes_outside (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : base.toNat + bs.length ≤ 2 ^ 64) {{p : BitVec 64}}
    (hout : p.toNat < base.toNat ∨ base.toNat + bs.length ≤ p.toNat) :
    (storeBytes d base bs).get? p = d.get? p := by
  have hne : ∀ x ∈ bs.zipIdx, base + BitVec.ofNat 64 x.2 ≠ p := by
    intro x hx heq
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_zipIdx] at hj
    simp only [List.getElem_zipIdx, Nat.zero_add] at heq
    have hnat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : j < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : base.toNat + j < 2 ^ 64)] at hnat
    omega
  have hkeep : ∀ (l : List (UInt8 × Nat)) (m : DataMem),
      (∀ x ∈ l, base + BitVec.ofNat 64 x.2 ≠ p) →
      (l.foldl (fun acc (b', i') => acc.insert (base + BitVec.ofNat 64 i') b') m).get? p = m.get? p := by
    intro l
    induction l with
    | nil => intro _ _; rfl
    | cons y ys ih =>
      intro m hy
      simp only [List.foldl_cons]
      rw [ih _ (fun x hx => hy x (List.mem_cons_of_mem _ hx))]
      simp only [Std.ExtHashMap.get?_eq_getElem?, Std.ExtHashMap.getElem?_insert]
      have hbf : (base + BitVec.ofNat 64 y.2 == p) = false := beq_false_of_ne (hy y List.mem_cons_self)
      simp [hbf]
  exact hkeep bs.zipIdx d hne

private def storeZeros (d : DataMem) (base : BitVec 64) (n : Nat) : DataMem :=
  storeBytes d base (List.replicate n 0)

private theorem bytesAt_of_storeBytes (d : DataMem) (base : BitVec 64) (bs : List UInt8)
    (hno : bs.length ≤ 2 ^ 64) : BytesAt (storeBytes d base bs) base bs :=
  fun _ hi => get?_storeBytes_inside d base bs hno hi

private theorem bytesAt_of_storeZeros (d : DataMem) (base : BitVec 64) (n : Nat)
    (hno : n ≤ 2 ^ 64) : BytesAt (storeZeros d base n) base (List.replicate n 0) :=
  bytesAt_of_storeBytes d base (List.replicate n 0) (by simpa using hno)

private theorem bytesAt_storeBytes_other {{d : DataMem}} {{a base : BitVec 64}} {{bs bs' : List UInt8}}
    (h : BytesAt d a bs) (hnoA : a.toNat + bs.length ≤ 2 ^ 64)
    (hnoB : base.toNat + bs'.length ≤ 2 ^ 64)
    (hdisj : a.toNat + bs.length ≤ base.toNat ∨ base.toNat + bs'.length ≤ a.toNat) :
    BytesAt (storeBytes d base bs') a bs := by
  intro i hi
  rw [get?_storeBytes_outside d base bs' hnoB (by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : a.toNat + i < 2 ^ 64)]
    omega)]
  exact h i hi

private theorem bytesAt_storeZeros_other {{d : DataMem}} {{a base : BitVec 64}} {{bs : List UInt8}} {{n : Nat}}
    (h : BytesAt d a bs) (hnoA : a.toNat + bs.length ≤ 2 ^ 64)
    (hnoB : base.toNat + n ≤ 2 ^ 64)
    (hdisj : a.toNat + bs.length ≤ base.toNat ∨ base.toNat + n ≤ a.toNat) :
    BytesAt (storeZeros d base n) a bs :=
  bytesAt_storeBytes_other h hnoA (by simpa using hnoB) (by simpa using hdisj)

private def wPkAddr : UInt64 := 0x10000000
private def wMsgAddr : UInt64 := 0x10001000
private def wSigAddr : UInt64 := 0x10002000
private def wSpAddr : UInt64 := 0x70000000
private def wRetAddr : UInt64 := 0x12345678

private def wd0 : DataMem := {{}}
private def wd1 : DataMem := storeZeros wd0 (wSpAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize) sphincsStackSize
private def wd2 : DataMem := storeBytes wd1 ({rc_vaddr:#x} : BitVec 64) roundConstsBytes
private def wd3 : DataMem := storeBytes wd2 ({lh_vaddr:#x} : BitVec 64) layerHeightsBytes
private def wd4 : DataMem := storeZeros wd3 wSigAddr.toBitVec sigSize
private def wd5 : DataMem := storeZeros wd4 wMsgAddr.toBitVec msgSize
private def witnessDmem : DataMem := storeZeros wd5 wPkAddr.toBitVec pkSize

private def witnessState : MachineData :=
  {{ regs := {{ SP := wSpAddr, X0 := wPkAddr, X1 := wMsgAddr, X2 := wSigAddr, X30 := wRetAddr }},
     dmem := witnessDmem }}

private theorem witness_premises :
    StackOk witnessState sphincsStackSize ∧
    ReadOnlyBuf witnessState.dmem roundConstsAddr roundConstsBytes witnessState sphincsStackSize ∧
    ReadOnlyBuf witnessState.dmem layerHeightsAddr layerHeightsBytes witnessState sphincsStackSize ∧
    ReadOnlyBuf witnessState.dmem witnessState.regs.X0.toBitVec (Vector.replicate pkSize 0).toList witnessState sphincsStackSize ∧
    ReadOnlyBuf witnessState.dmem witnessState.regs.X1.toBitVec (Vector.replicate msgSize 0).toList witnessState sphincsStackSize ∧
    ReadOnlyBuf witnessState.dmem witnessState.regs.X2.toBitVec (Vector.replicate sigSize 0).toList witnessState sphincsStackSize := by
  have hrcLen : roundConstsBytes.length = 192 := roundConstsSize_eq
  have hlhLen : layerHeightsBytes.length = 24 := layerHeightsBytes_length
  have hpkLen : (Vector.replicate pkSize (0 : UInt8)).toList = List.replicate pkSize 0 := by simp
  have hmsgLen : (Vector.replicate msgSize (0 : UInt8)).toList = List.replicate msgSize 0 := by simp
  have hsigLen : (Vector.replicate sigSize (0 : UInt8)).toList = List.replicate sigSize 0 := by simp
  have hdmem : witnessState.dmem = witnessDmem := by unfold witnessState; rfl
  have hsp : witnessState.regs.SP = wSpAddr := rfl
  have hx0 : witnessState.regs.X0 = wPkAddr := rfl
  have hx1 : witnessState.regs.X1 = wMsgAddr := rfl
  have hx2 : witnessState.regs.X2 = wSigAddr := rfl
  have hstkToNat : (wSpAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize).toNat = 0x70000000 - 22192 := by
    rw [sphincsStackSize_eq]; decide
  have hspToNat : wSpAddr.toNat = 0x70000000 := rfl
  have hpkToNat : wPkAddr.toBitVec.toNat = 0x10000000 := rfl
  have hmsgToNat : wMsgAddr.toBitVec.toNat = 0x10001000 := rfl
  have hsigToNat : wSigAddr.toBitVec.toNat = 0x10002000 := rfl
  have hrcToNat : ({rc_vaddr:#x} : BitVec 64).toNat = {rc_vaddr:#x} := rfl
  have hlhToNat : ({lh_vaddr:#x} : BitVec 64).toNat = {lh_vaddr:#x} := rfl
  have hstkSz : sphincsStackSize = 22192 := sphincsStackSize_eq
  have hpkSz : pkSize = 32 := rfl
  have hmsgSz : msgSize = 32 := rfl
  have hsigSz : sigSize = 7740 := rfl
  have hstackLowB : BytesAt witnessDmem (wSpAddr.toBitVec - BitVec.ofNat 64 sphincsStackSize)
      (List.replicate sphincsStackSize 0) := by
    have hlen : (List.replicate sphincsStackSize (0 : UInt8)).length = sphincsStackSize := List.length_replicate
    have b1 : BytesAt wd1 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b2 : BytesAt wd2 _ _ := bytesAt_storeBytes_other b1 (by omega) (by omega) (by omega)
    have b3 : BytesAt wd3 _ _ := bytesAt_storeBytes_other b2 (by omega) (by omega) (by omega)
    have b4 : BytesAt wd4 _ _ := bytesAt_storeZeros_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    exact bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
  have hStackOk : StackOk witnessState sphincsStackSize := by
    refine ⟨by rw [hsp]; omega, by rw [hsp]; omega, fun i hi => ?_⟩
    rw [hsp, hdmem]
    have hb := hstackLowB i (by simpa using hi)
    rw [hb]; rfl
  have hrcB : BytesAt witnessDmem ({rc_vaddr:#x} : BitVec 64) roundConstsBytes := by
    have b2 : BytesAt wd2 _ _ := bytesAt_of_storeBytes _ _ _ (by omega)
    have b3 : BytesAt wd3 _ _ := bytesAt_storeBytes_other b2 (by omega) (by omega) (by omega)
    have b4 : BytesAt wd4 _ _ := bytesAt_storeZeros_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    exact bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
  have hlhB : BytesAt witnessDmem ({lh_vaddr:#x} : BitVec 64) layerHeightsBytes := by
    have b3 : BytesAt wd3 _ _ := bytesAt_of_storeBytes _ _ _ (by omega)
    have b4 : BytesAt wd4 _ _ := bytesAt_storeZeros_other b3 (by omega) (by omega) (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    exact bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
  have hsigB : BytesAt witnessDmem wSigAddr.toBitVec (List.replicate sigSize 0) := by
    have hlen : (List.replicate sigSize (0 : UInt8)).length = sigSize := List.length_replicate
    have b4 : BytesAt wd4 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    have b5 : BytesAt wd5 _ _ := bytesAt_storeZeros_other b4 (by omega) (by omega) (by omega)
    exact bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
  have hmsgB : BytesAt witnessDmem wMsgAddr.toBitVec (List.replicate msgSize 0) := by
    have hlen : (List.replicate msgSize (0 : UInt8)).length = msgSize := List.length_replicate
    have b5 : BytesAt wd5 _ _ := bytesAt_of_storeZeros _ _ _ (by omega)
    exact bytesAt_storeZeros_other b5 (by omega) (by omega) (by omega)
  have hpkB : BytesAt witnessDmem wPkAddr.toBitVec (List.replicate pkSize 0) :=
    bytesAt_of_storeZeros _ _ _ (by omega)
  refine ⟨hStackOk, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by rw [hdmem, real_rcAddr]; exact hrcB, by rw [real_rcAddr]; unfold NoWrap; omega,
      by rw [real_rcAddr]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hsp]; omega⟩
  · refine ⟨by rw [hdmem, real_lhAddr]; exact hlhB, by rw [real_lhAddr]; unfold NoWrap; omega,
      by rw [real_lhAddr]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hsp]; omega⟩
  · refine ⟨by rw [hdmem, hx0, hpkLen]; exact hpkB, by rw [hx0, hpkLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hx0, hpkLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hsp]; omega⟩
  · refine ⟨by rw [hdmem, hx1, hmsgLen]; exact hmsgB, by rw [hx1, hmsgLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hx1, hmsgLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hsp]; omega⟩
  · refine ⟨by rw [hdmem, hx2, hsigLen]; exact hsigB, by rw [hx2, hsigLen, List.length_replicate]; unfold NoWrap; omega,
      by rw [hx2, hsigLen, List.length_replicate]; unfold SphincsVerifier.Disjoint Apart stackBottomAddr stackBelow; rw [hsp]; omega⟩

/-- Concrete non-vacuity proof: an explicit `MachineData` state satisfies every premise of
`verify_correct` on the real linked Linux AArch64 ELF binary. -/
theorem real_elf_non_vacuous :
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = returnAddrOf witnessState ∧
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk (Vector.replicate pkSize 0).toList)
          (Native.SphincsVerifier.decodeMsg (Vector.replicate msgSize 0).toList)
          (Native.SphincsVerifier.decodeSig (Vector.replicate sigSize 0).toList) then 1 else 0) ∧
        SameOutside witnessState.dmem finalState.data.dmem
          (InRange (stackBottomAddr witnessState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept witnessState finalState.data)
      ⟨witnessState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := witness_premises
  exact real_elf_verify_correct
    (Vector.replicate pkSize 0) (Vector.replicate msgSize 0) (Vector.replicate sigSize 0)
    witnessState h1 h2 h3 h4 h5 h6

/-- Concrete non-vacuity proof for `verify_confined` on the real linked Linux AArch64 ELF binary. -/
theorem real_elf_confined_non_vacuous :
    let allowedRegions := [
      (stackBottomAddr witnessState sphincsStackSize, sphincsStackSize),
      (witnessState.regs.X0.toBitVec, pkSize), (witnessState.regs.X1.toBitVec, msgSize),
      (witnessState.regs.X2.toBitVec, sigSize),
      (roundConstsAddr, roundConstsSize),
      (layerHeightsAddr, layerHeightsSize)]
    let confinedState := {{ witnessState with dmem := restrictMemory witnessState.dmem allowedRegions }}
    (∀ addr, ¬ InRegions allowedRegions addr → confinedState.dmem.get? addr = none) ∧
    Eventually (elfStep1 ElfHost.exe)
      (fun finalState ↦
        finalState.pc = returnAddrOf confinedState ∧
        finalState.data.regs.X0 = (if _root_.Sphincs.verifyWithKeccak
          (Native.SphincsVerifier.decodePk (Vector.replicate pkSize 0).toList)
          (Native.SphincsVerifier.decodeMsg (Vector.replicate msgSize 0).toList)
          (Native.SphincsVerifier.decodeSig (Vector.replicate sigSize 0).toList) then 1 else 0) ∧
        SameOutside confinedState.dmem finalState.data.dmem
          (InRange (stackBottomAddr confinedState sphincsStackSize) sphincsStackSize) ∧
        CalleeSavedAndMemKept confinedState finalState.data)
      ⟨confinedState, label NativeRustcArm.Sphincs.SphincsVerify.entryLabel⟩ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := witness_premises
  exact real_elf_verify_confined
    (Vector.replicate pkSize 0) (Vector.replicate msgSize 0) (Vector.replicate sigSize 0)
    witnessState h1 h2 h3 h4 h5 h6

#print axioms real_elf_verify_correct
#print axioms real_elf_verify_confined
#print axioms real_elf_non_vacuous
#print axioms real_elf_confined_non_vacuous

end RealElfWitnessArm
"""


def main():
    parser = argparse.ArgumentParser(description="Emit a concrete Lean ElfHost witness for a linked ELF binary")
    parser.add_argument("--arch", required=True, choices=("x86_64", "aarch64"))
    parser.add_argument("--elf", required=True, help="Path to linked Linux ELF binary")
    parser.add_argument("--out", required=True, help="Output Lean witness path")
    parser.add_argument("--asm", help="Path to signatures-{arch}.s")
    parser.add_argument("--clang", default=os.environ.get("CLANG", "clang"))
    parser.add_argument("--objdump", default=os.environ.get("OBJDUMP", "llvm-objdump"))
    args = parser.parse_args()

    repo_root = pathlib.Path(__file__).resolve().parents[3]
    asm_path = (
        pathlib.Path(args.asm)
        if args.asm
        else repo_root / "formal/native/rustc/asm" / f"signatures-{args.arch}.s"
    )
    cle = load_checker()
    funcs, rodata, got_slots, fn_sizes = inspect_elf(
        cle, args.arch, asm_path, pathlib.Path(args.elf), args.clang, args.objdump
    )
    if args.arch == "x86_64":
        src = emit_x64_lean(args.elf, funcs, rodata, got_slots, fn_sizes)
    else:
        src = emit_arm64_lean(args.elf, funcs, rodata)

    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(src)
    print(f"Wrote concrete {args.arch} ElfHost witness to {out_path}")


if __name__ == "__main__":
    main()
