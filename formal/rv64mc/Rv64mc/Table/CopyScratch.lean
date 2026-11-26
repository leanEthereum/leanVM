/-
  Rv64mc.Table.CopyScratch

  `compiler_builtins`' `memcpy` and `memmove` write scratch below their entry's stack pointer and leave it there:
  `memcpy`'s `load_aligned_partial` assembles a partial word in its slot at `sp + 8` when the source is not 8-byte
  aligned against the destination, and `memmove` saves `s0` at `sp + 8`. So at the image's environment, a contract
  that keeps every byte outside the destination (`KeepAllPost`, `CopyPost` before its frame left out that stack) is
  false of both: `memcpy_byteFrame_false` and `memmove_byteFrame_false`. Nor are the bytes always copied right when
  the source or the destination overlaps the slot: `memcpy_srcOnStack_false`, against `CopyPost` under `CopyPre`
  alone, and `memcpy_dstOnStack_false`, under `CopyPre` and a source apart from the stack, which is why
  `MemcpySpec` and `MemmoveSpec` ask `CopyApart` too. Each is a concrete run the kernel evaluates
  (`Isa.lrunReturns`, `Contract.not_of_lrun`) from `stackTop`: `memcpy` copies 16 or 24 bytes from a source 4 bytes
  past an 8-byte boundary, `memmove` copies none. The corrected precondition holds with bytes to copy
  (`copySpec_pre_inhabited`), and from that state `memcpy` and `memmove` copy a misaligned source right (`copies`);
  so do `memcpy` to a destination at or above the stack pointer and `memmove` with overlapping ranges. These runs check
  `a0`, the copied bytes and the 8 bytes on either side of the destination, not the rest of `Holds`' postcondition.

  The entry state holds the image's static data words (`StaticData`, through `Image.WF`'s distinct addresses), so
  that it meets `Holds`' precondition at `env`; every other doubleword is the witness's.

  ## Main results

  * `memcpy_byteFrame_false`, `memmove_byteFrame_false`, `memcpy_srcOnStack_false`, `memcpy_dstOnStack_false`
  * `copySpec_pre_inhabited`, `copies`, `memcpy_copies_aboveTop`, `memmove_copies_overlap`: guards of the corrected
    contracts
  * `memcpySpec_of_keepAll`, `memmoveSpec_of_keepAll`: the contracts as they were imply `MemcpySpec`, `MemmoveSpec`
-/

import Rv64mc.Core.LocalRun
import Rv64mc.Final.End
import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Gen.Needs

namespace Rv64mc.Table.CopyScratch

open RiscvZkvm.Rv64 Lprog Lprog.RiscV MachineChecked.RiscV.Lift Rv64mc.Spec.Runtime

/-- A copy's postcondition with a frame that keeps every byte outside the destination, the callee's stack
    included. -/
def KeepAllPost (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = regs .x10 ∧
    (∀ k, k < (regs .x12).toNat →
      m'.getByte (regs .x10 + BitVec.ofNat 64 k) = m.getByte (regs .x11 + BitVec.ofNat 64 k)) ∧
    ByteFrame m m' (regs .x10) (regs .x12).toNat

/-- **The contract as it was implies `MemcpySpec`**: a stronger precondition and a weaker postcondition. -/
theorem memcpySpec_of_keepAll {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}
    (h : Holds env p i need (CopyPre false) KeepAllPost CopyOut) : MemcpySpec env p i need :=
  fun G n Q ret top rest regs m ⟨he, hs, hst, hn, ⟨hP, _⟩, hal⟩ hk =>
    h G n Q ret top rest regs m ⟨he, hs, hst, hn, hP, hal⟩ fun r' m' ⟨ha, hf, hs', hx, hc, hb⟩ =>
      hk r' m' ⟨ha, hf, hs', hx, hc, fun b hb' _ => hb b hb'⟩

/-- **The contract as it was implies `MemmoveSpec`.** -/
theorem memmoveSpec_of_keepAll {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}
    (h : Holds env p i need (CopyPre true) KeepAllPost CopyOut) : MemmoveSpec env p i need :=
  fun G n Q ret top rest regs m ⟨he, hs, hst, hn, ⟨hP, _⟩, hal⟩ hk =>
    h G n Q ret top rest regs m ⟨he, hs, hst, hn, hP, hal⟩ fun r' m' ⟨ha, hf, hs', hx, hc, hb⟩ =>
      hk r' m' ⟨ha, hf, hs', hx, hc, fun b hb' _ => hb b hb'⟩

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

/-- The doublewords from `stackTop - 16` to `stackTop + 8` distinct, every other zero. -/
noncomputable def distinctAtTop (a : Word) : Word :=
  if a = stackTop - 16#64 then 0x1111111111111111#64 else if a = slot then 0x2222222222222222#64
  else if a = stackTop then 0x3333333333333333#64 else 0

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

/-- `CopyPre` at the entry: neither range wraps, and for `memcpy` the ranges lie apart. -/
theorem entry_copyPre {o : Bool} {dst src n : Word} {st : Word → Word} (hd : dst.toNat + n.toNat < 2 ^ 64)
    (hs : src.toNat + n.toNat < 2 ^ 64)
    (hap : o = false → dst.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ dst.toNat) :
    CopyPre o (entryRegs dst src n) (entryM st) :=
  ⟨hd, hs, fun ho b (h1 : InRange dst n.toNat b) (h2 : InRange src n.toNat b) => by
    unfold InRange at h1 h2
    have := hap ho
    omega⟩

/-- `Holds`' precondition at the entry, from the copy's. -/
theorem entry_pre {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat)
    (Pre : (Reg → Word) → MachineState → Prop) {dst src n : Word} {st : Word → Word}
    (h : Pre (entryRegs dst src n) (entryM st)) :
    Holds.pre env need Pre 0x1000#64 stackTop (entryRegs dst src n) (entryM st) :=
  ⟨⟨rfl, rfl⟩, hn, entryM_static st, by rw [entryM_next]; show heapStart.toNat ≤ heapEnd.toNat; decide, h,
    by decide⟩

/-- **A copy's contract at the image is refuted by a run** of function `f`'s body from the entry with `dst`, `src`,
    `n` and `st` that returns in a state satisfying `P`, if `P` excludes `Post`. -/
theorem not_holds {f need : Nat} {fd : Lfundef (Op Reg) Reg} (hp : (liftProg Gen.fns)[f]? = some fd)
    (hn : stackLimit.toNat + need ≤ stackTop.toNat) {Pre : (Reg → Word) → MachineState → Prop}
    {Post : (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop} (dst src n : Word) (st : Word → Word)
    (hpre : Pre (entryRegs dst src n) (entryM st)) (P : (Reg → Word) → MachineState → Bool)
    (hrun : Isa.lrunReturns (I := rvIsa) fd.body 0x1000#64 stackTop 1000 (some 0, entryRegs dst src n, entryM st) P
      = true)
    (hpost : ∀ r' m', P r' m' = true → ¬ Post (entryRegs dst src n) (entryM st) r' m') :
    ¬ Holds env (liftProg Gen.fns) f need Pre Post CopyOut := by
  obtain ⟨r', m', hr, hb⟩ := Isa.lrunReturns_spec hrun
  exact Isa.Contract.not_of_lrun hp (entry_pre hn _ hpre) hr fun ⟨_, _, _, h⟩ => hpost r' m' hb h

set_option maxRecDepth 100000 in
/-- **`memcpy` does not keep every byte outside its destination**: copying 16 bytes to `0x20000000` from
    `0x20000104` from `stackTop`, it returns with its slot changed. -/
theorem memcpy_byteFrame_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ Holds env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memcpy need (CopyPre false) KeepAllPost CopyOut :=
  not_holds Gen.CompilerBuiltins.Mem.Memcpy.tmpl_eq hn 0x20000000#64 0x20000104#64 16#64 onesAtSlot
    (entry_copyPre (by decide) (by decide) fun _ => by decide)
    (fun _ m' => m'.getByte slot != (entryM onesAtSlot).getByte slot) (by decide)
    fun _ _ hb ⟨_, _, hf⟩ => bne_iff_ne.1 hb (hf slot (by simp [InRange, entryRegs, slot]; decide))

set_option maxRecDepth 100000 in
/-- **`memmove` does not keep every byte outside its destination**: copying no bytes from `stackTop`, it returns with
    its slot changed (it saves `s0` there). -/
theorem memmove_byteFrame_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ Holds env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memmove need (CopyPre true) KeepAllPost CopyOut :=
  not_holds Gen.CompilerBuiltins.Mem.Memmove.tmpl_eq hn 0x20000000#64 0x20000100#64 0#64 onesAtSlot
    (entry_copyPre (by decide) (by decide) nofun)
    (fun _ m' => m'.getByte slot != (entryM onesAtSlot).getByte slot) (by decide)
    fun _ _ hb ⟨_, _, hf⟩ => bne_iff_ne.1 hb (hf slot (by simp [InRange, entryRegs]))

/-- A copy from the entry is refuted by a destination byte other than the source's at entry. -/
theorem not_copied {dst src n : Word} {st : Word → Word} {m' : MachineState}
    (hc : ∀ k, k < (entryRegs dst src n .x12).toNat →
      m'.getByte (entryRegs dst src n .x10 + BitVec.ofNat 64 k) =
        (entryM st).getByte (entryRegs dst src n .x11 + BitVec.ofNat 64 k))
    (hb : ((List.range n.toNat).any fun k =>
      m'.getByte (dst + BitVec.ofNat 64 k) != (entryM st).getByte (src + BitVec.ofNat 64 k)) = true) : False := by
  obtain ⟨k, hk, hne⟩ := List.any_eq_true.1 hb
  exact bne_iff_ne.1 hne (hc k (List.mem_range.1 hk))

set_option maxRecDepth 100000 in
/-- **`memcpy` can copy a source that overlaps its slot wrong**: copying 16 bytes to `0x20000000` from `stackTop - 12`,
    it returns with a destination byte other than the source's at entry. -/
theorem memcpy_srcOnStack_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ Holds env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memcpy need (CopyPre false) (CopyPost env)
      CopyOut :=
  not_holds Gen.CompilerBuiltins.Mem.Memcpy.tmpl_eq hn 0x20000000#64 (stackTop - 12#64) 16#64 distinctAtTop
    (entry_copyPre (by decide) (by decide) fun _ => by decide)
    (fun _ m' => (List.range 16).any fun k =>
      m'.getByte (0x20000000#64 + BitVec.ofNat 64 k) !=
        (entryM distinctAtTop).getByte (stackTop - 12#64 + BitVec.ofNat 64 k)) (by decide)
    fun _ _ hb ⟨_, hc, _⟩ => not_copied hc hb

set_option maxRecDepth 100000 in
/-- **`memcpy` can copy into its slot wrong**: copying 24 bytes to `stackTop - 16` from `0x20000104`, a source apart
    from its stack, it returns with a destination byte other than the source's at entry. -/
theorem memcpy_dstOnStack_false {need : Nat} (hn : stackLimit.toNat + need ≤ stackTop.toNat) :
    ¬ Holds env (liftProg Gen.fns) Gen.Idx.CompilerBuiltins.Mem.Memcpy need
      (fun regs m => CopyPre false regs m ∧ OffStack env (regs .x2) (regs .x11) (regs .x12).toNat) (CopyPost env)
      CopyOut :=
  not_holds Gen.CompilerBuiltins.Mem.Memcpy.tmpl_eq hn (stackTop - 16#64) 0x20000104#64 24#64 id
    ⟨entry_copyPre (by decide) (by decide) fun _ => by decide, .inl (by decide)⟩
    (fun _ m' => (List.range 24).any fun k =>
      m'.getByte (stackTop - 16#64 + BitVec.ofNat 64 k) != (entryM id).getByte (0x20000104#64 + BitVec.ofNat 64 k))
    (by decide)
    fun _ _ hb ⟨_, hc, _⟩ => not_copied hc hb

/-! ## Guards of the corrected contracts -/

/-- **`MemcpySpec`'s and `MemmoveSpec`'s preconditions hold with bytes to copy**: 16 bytes to `0x1fffff00`, below
    `NEXT`, from `0x1fffff84`, 4 bytes past an 8-byte boundary, from `stackTop`. -/
theorem copySpec_pre_inhabited (st : Word → Word) :
    Holds.pre env Gen.Needs.CompilerBuiltins.Mem.Memcpy (fun regs m => CopyPre false regs m ∧ CopyApart env regs m)
      0x1000#64 stackTop (entryRegs 0x1fffff00#64 0x1fffff84#64 16#64) (entryM st) ∧
    Holds.pre env Gen.Needs.CompilerBuiltins.Mem.Memmove (fun regs m => CopyPre true regs m ∧ CopyApart env regs m)
      0x1000#64 stackTop (entryRegs 0x1fffff00#64 0x1fffff84#64 16#64) (entryM st) := by
  have ha : CopyApart env (entryRegs 0x1fffff00#64 0x1fffff84#64 16#64) (entryM st) := by
    refine .inr ⟨⟨.inl ?_, by decide⟩, .inl (by decide)⟩
    rw [entryM_next]
    decide
  exact ⟨entry_pre (by decide) _ ⟨entry_copyPre (by decide) (by decide) fun _ => by decide, ha⟩,
    entry_pre (by decide) _ ⟨entry_copyPre (by decide) (by decide) nofun, ha⟩⟩

/-- A copy's run from `entryM id` is right: it returns `dst`, `[dst, dst + n)` holds what `[src, src + n)` held,
    and the 8 bytes on either side of the destination are kept. -/
noncomputable def CopiedRight (dst src : Word) (n : Nat) (r' : Reg → Word) (m' : MachineState) : Bool :=
  r' .x10 == dst &&
    ((List.range n).all fun k =>
      m'.getByte (dst + BitVec.ofNat 64 k) == (entryM id).getByte (src + BitVec.ofNat 64 k)) &&
    (List.range 8).all fun k =>
      m'.getByte (dst - 8#64 + BitVec.ofNat 64 k) == (entryM id).getByte (dst - 8#64 + BitVec.ofNat 64 k) &&
      m'.getByte (dst + BitVec.ofNat 64 (n + k)) == (entryM id).getByte (dst + BitVec.ofNat 64 (n + k))

/-- `memcpy(dst, src, n)` from `stackTop` and `entryM id` returns with `CopiedRight`. -/
noncomputable def memcpyRight (dst src n : Word) : Bool :=
  Isa.lrunReturns (I := rvIsa) (Gen.CompilerBuiltins.Mem.Memcpy.tmpl Gen.CompilerBuiltins.Mem.Memcpy.link).body
    0x1000#64 stackTop 2000 (some 0, entryRegs dst src n, entryM id) (CopiedRight dst src n.toNat)

/-- `memmove(dst, src, n)` from `stackTop` and `entryM id` returns with `CopiedRight`. -/
noncomputable def memmoveRight (dst src n : Word) : Bool :=
  Isa.lrunReturns (I := rvIsa) (Gen.CompilerBuiltins.Mem.Memmove.tmpl Gen.CompilerBuiltins.Mem.Memmove.link).body
    0x1000#64 stackTop 2000 (some 0, entryRegs dst src n, entryM id) (CopiedRight dst src n.toNat)

set_option maxRecDepth 100000 in
/-- **`memcpy` and `memmove` copy from that state**, with every other doubleword holding its address. -/
theorem copies : memcpyRight 0x1fffff00#64 0x1fffff84#64 16#64 = true ∧
    memmoveRight 0x1fffff00#64 0x1fffff84#64 16#64 = true := by
  decide

set_option maxRecDepth 100000 in
/-- **`memcpy` copies to a destination on the caller's stack** (`Owned` by `top ≤ dst`, as `Duplex`' calls), from a
    misaligned source below `NEXT`. -/
theorem memcpy_copies_aboveTop : memcpyRight (stackTop + 8#64) 0x1fffff84#64 24#64 = true := by
  decide

set_option maxRecDepth 100000 in
/-- **`memmove` copies overlapping ranges**, the destination below the source and above it. -/
theorem memmove_copies_overlap : memmoveRight 0x1fffff00#64 0x1fffff04#64 24#64 = true ∧
    memmoveRight 0x1fffff04#64 0x1fffff00#64 24#64 = true := by
  decide

end Rv64mc.Table.CopyScratch

/-- info: 'Rv64mc.Table.CopyScratch.memcpy_byteFrame_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memcpy_byteFrame_false

/-- info: 'Rv64mc.Table.CopyScratch.memmove_byteFrame_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memmove_byteFrame_false

/-- info: 'Rv64mc.Table.CopyScratch.memcpy_srcOnStack_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memcpy_srcOnStack_false

/-- info: 'Rv64mc.Table.CopyScratch.memcpy_dstOnStack_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memcpy_dstOnStack_false

/-- info: 'Rv64mc.Table.CopyScratch.copySpec_pre_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.copySpec_pre_inhabited

/-- info: 'Rv64mc.Table.CopyScratch.copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.copies

/-- info: 'Rv64mc.Table.CopyScratch.memcpy_copies_aboveTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memcpy_copies_aboveTop

/-- info: 'Rv64mc.Table.CopyScratch.memmove_copies_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Table.CopyScratch.memmove_copies_overlap
