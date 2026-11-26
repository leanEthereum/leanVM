/-
  Rv64mc.Table.CopyScratch

  `compiler_builtins`' `memcpy` and `memmove` write scratch below their entry's stack pointer and leave it there:
  `memcpy`'s `load_aligned_partial` assembles a partial word in its slot at `sp + 8` when the source is not 8-byte
  aligned against the destination, and `memmove` saves `s0` at `sp + 8`. So at the image's environment, a contract
  that keeps every byte outside the destination is false of both: `memcpy_byteFrame_false` and
  `memmove_byteFrame_false`, each from a concrete run the kernel evaluates (`Isa.lrunReturns`,
  `Contract.not_of_lrun`). The run starts at `stackTop` with the slot's doubleword all ones, and returns with it
  changed: `memcpy` copies 16 zero bytes from a source 4 bytes past an 8-byte boundary, `memmove` copies none.

  The entry state holds the image's static data words (`StaticData`, through `Image.WF`'s distinct addresses), so
  that it meets `Holds`' precondition at `env`; every other doubleword is zero but the slot.

  ## Main results

  * `memcpy_byteFrame_false`, `memmove_byteFrame_false`
-/

import Rv64mc.Core.LocalRun
import Rv64mc.Final.End
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Gen.Needs

namespace Rv64mc.Table.CopyScratch

open RiscvZkvm.Rv64 Lprog Lprog.RiscV MachineChecked.RiscV.Lift Rv64mc.Spec.Runtime

/-- The value of the image's data word at `a`, zero where there is none. -/
noncomputable def dataAt (a : Word) : Word := ((image.data.find? fun q => q.1 == a).map (·.2)).getD 0

/-- The entry state: the image's data words from `heapEnd` to `NEXT`, `st` elsewhere, no code. -/
noncomputable def entryM (st : Word → Word) : MachineState where
  regs := fun _ => 0
  mem := fun a => if heapEnd.toNat ≤ a.toNat ∧ a.toNat ≤ nextAddr.toNat then dataAt a else st a
  code := fun _ => none
  pc := 0

/-- The entry registers: return address `0x1000`, stack pointer `stackTop`, the arguments `dst`, `src`, `n`. -/
noncomputable def entryRegs (dst src n : Word) : Reg → Word := fun r =>
  if r = .x1 then 0x1000#64 else if r = .x2 then stackTop else if r = .x10 then dst else if r = .x11 then src
  else if r = .x12 then n else 0

/-- The doubleword of the copies' scratch slot, `sp + 8` after their 16-byte frame. -/
noncomputable def slot : Word := stackTop - 8#64

/-- The slot's doubleword all ones, every other zero. -/
noncomputable def onesAtSlot (a : Word) : Word := if a = slot then 0xffffffffffffffff#64 else 0

theorem dataAt_of_mem {a v : Word} (hp : (a, v) ∈ image.data) : dataAt a = v := by
  suffices h : ∀ l : List (Word × Word), (l.map (·.1)).Nodup → (a, v) ∈ l →
      ((l.find? fun q => q.1 == a).map (·.2)).getD 0 = v from h _ (Image.wf_of_check wf_check).1 hp
  intro l hl hpl
  induction l with
  | nil => cases hpl
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
    rcases List.mem_cons.1 hpl with rfl | hpl
    · simp
    · have hne : q.1 ≠ a := fun he => hl.1 ⟨(a, v), hpl, he.symm⟩
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact ih hl.2 hpl

/-- The entry state holds the static data. -/
theorem entryM_static (st : Word → Word) : env.Static (entryM st) := by
  intro p hp hne
  have := List.all_eq_true.1 static_region p hp
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with he | ⟨h1, h2⟩
  · exact absurd he hne
  · simp only [MachineState.getMem, entryM, h1, Nat.le_of_lt h2, and_self, ite_true]
    exact dataAt_of_mem (a := p.1) (v := p.2) hp

/-- `NEXT` at the entry is the heap's start. -/
theorem entryM_next (st : Word → Word) : env.next (entryM st) = heapStart := by
  have hn : (nextAddr, heapStart) ∈ image.data := List.contains_iff_mem.1 next_check
  have hl := layout_facts
  have e : env.next (entryM st) = (entryM st).mem nextAddr := rfl
  rw [e]
  unfold entryM
  dsimp only
  simp only [hl.1, Nat.le_refl, and_self, ↓reduceIte]
  exact dataAt_of_mem hn

/-- Neither range wraps. -/
theorem entry_noWrap {dst src n : Word} (hd : dst.toNat + n.toNat < 2 ^ 64) (hs : src.toNat + n.toNat < 2 ^ 64) :
    NoWrap (entryRegs dst src n .x10) (entryRegs dst src n .x12).toNat ∧
      NoWrap (entryRegs dst src n .x11) (entryRegs dst src n .x12).toNat :=
  ⟨hd, hs⟩

/-- `Holds`' precondition at the entry, from the copy's. -/
theorem entry_pre {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat)
    (Pre : (Reg → Word) → MachineState → Prop) {dst src n : Word} {st : Word → Word}
    (h : Pre (entryRegs dst src n) (entryM st)) :
    Holds.pre env need Pre 0x1000#64 stackTop (entryRegs dst src n) (entryM st) :=
  ⟨⟨rfl, rfl⟩, hn, entryM_static st, by rw [entryM_next]; show heapStart.toNat ≤ heapEnd.toNat; decide, h,
    by decide⟩

set_option maxRecDepth 100000 in
/-- **`memcpy` does not keep every byte outside its destination**: copying 16 bytes to `0x20000000` from
    `0x20000104` from `stackTop`, it returns with its slot changed. -/
theorem memcpy_byteFrame_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ MemcpySpec env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memcpy need := by
  obtain ⟨r', m', hrun, hb⟩ := Isa.lrunReturns_spec (I := rvIsa)
    (show Isa.lrunReturns (Gen.CompilerBuiltins.Mem.Memcpy.tmpl Gen.CompilerBuiltins.Mem.Memcpy.link).body
      0x1000#64 stackTop 1000 (some 0, entryRegs 0x20000000#64 0x20000104#64 16#64, entryM onesAtSlot)
      (fun _ (m' : MachineState) => m'.getByte slot != (entryM onesAtSlot).getByte slot) = true by decide)
  refine Isa.Contract.not_of_lrun Gen.CompilerBuiltins.Mem.Memcpy.tmpl_eq
    (entry_pre hn _ ⟨(entry_noWrap (by decide) (by decide)).1, (entry_noWrap (by decide) (by decide)).2,
      fun _ b h1 h2 => ?_⟩) hrun fun ⟨_, _, _, _, _, hf⟩ => ?_
  · simp only [InRange, entryRegs] at h1 h2
    simp at h1 h2
    omega
  · have := hf slot (by simp [InRange, entryRegs, slot]; decide)
    simp only [bne_iff_ne, ne_eq] at hb
    exact hb this

set_option maxRecDepth 100000 in
/-- **`memmove` does not keep every byte outside its destination**: copying no bytes from `stackTop`, it returns with
    its slot changed (it saves `s0` there). -/
theorem memmove_byteFrame_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ MemmoveSpec env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memmove need := by
  obtain ⟨r', m', hrun, hb⟩ := Isa.lrunReturns_spec (I := rvIsa)
    (show Isa.lrunReturns (Gen.CompilerBuiltins.Mem.Memmove.tmpl Gen.CompilerBuiltins.Mem.Memmove.link).body
      0x1000#64 stackTop 1000 (some 0, entryRegs 0x20000000#64 0x20000100#64 0#64, entryM onesAtSlot)
      (fun _ (m' : MachineState) => m'.getByte slot != (entryM onesAtSlot).getByte slot) = true by decide)
  refine Isa.Contract.not_of_lrun Gen.CompilerBuiltins.Mem.Memmove.tmpl_eq
    (entry_pre hn _ ⟨(entry_noWrap (by decide) (by decide)).1, (entry_noWrap (by decide) (by decide)).2,
      fun h => nomatch h⟩) hrun fun ⟨_, _, _, _, _, hf⟩ => ?_
  have := hf slot (by simp [InRange, entryRegs])
  simp only [bne_iff_ne, ne_eq] at hb
  exact hb this

end Rv64mc.Table.CopyScratch

/-- info: 'Rv64mc.Table.CopyScratch.memcpy_byteFrame_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memcpy_byteFrame_false

/-- info: 'Rv64mc.Table.CopyScratch.memmove_byteFrame_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memmove_byteFrame_false
