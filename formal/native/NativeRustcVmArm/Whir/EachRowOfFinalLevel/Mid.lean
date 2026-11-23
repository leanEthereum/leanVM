module

public import NativeRustcVmArm.Whir.EachRowOfFinalLevel.Start

/-!
# `each_row` with `final_level`'s closure: inside an iteration

`Mid j m`: in iteration `j` (`j` below both counts), the invariant's frame, locals, rows checked and
loop registers, X29 query `j`. Kept by a callee that changes memory in `HitF` only and keeps the
callee-saved registers (`Mid.call`), and by a block run from `frameS` that writes nothing and keeps
the loop's registers (`Mid.block`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfFinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfFinalLevel
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **Inside iteration `j`.** -/
structure Mid (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 m
  low : Low m0 m.dmem
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  x19 : m.regs.getXReg .X19 = (8 * ((qsOf m0).size - j)).toUInt64
  x25 : m.regs.getXReg .X25 = j.toUInt64
  x28 : m.regs.getXReg .X28 = rows.size.toUInt64
  x20 : m.regs.getXReg .X20 = m0.regs.X6
  x21 : m.regs.getXReg .X21 = m0.regs.X5
  x22 : m.regs.getXReg .X22 = m0.regs.X3
  x23 : m.regs.getXReg .X23 = m0.regs.X1
  x24 : m.regs.getXReg .X24 = m0.regs.X0
  x29 : m.regs.getXReg .X29 = (qsOf m0)[j]'hjq

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- The registers the loop keeps. -/
@[expose] def loopRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X28, .X29]

/-- **A call** changing memory in `HitF` only. -/
theorem Mid.call (hpre : EachRowFinalPre rows op m0) {m m' : MachineData} (h : Mid rows m0 j m)
    (hs : SameOutside m.dmem m'.dmem (HitF m0)) (hsv : Saved m m') : Mid rows m0 j m' := by
  have hl := lay hpre
  have hr : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r := hsv.1
  exact ⟨EachRow.fr_hit hl h.fr hsv.2.1 hsv.2.2 hs slots_ok, h.low.keep hl hs, h.hj, h.hjq, h.ok,
    (hr .X19 rfl).trans h.x19, (hr .X25 rfl).trans h.x25, (hr .X28 rfl).trans h.x28,
    (hr .X20 rfl).trans h.x20, (hr .X21 rfl).trans h.x21, (hr .X22 rfl).trans h.x22,
    (hr .X23 rfl).trans h.x23, (hr .X24 rfl).trans h.x24, (hr .X29 rfl).trans h.x29⟩

/-- **A block** run from the frame alone, without writes, keeping SP and the loop's registers. -/
theorem Mid.block [Labels] {m m' : MachineData} {S' : SState} (h : Mid rows m0 j m)
    (hm : Match (Env.ofMachine m [(fb m0, 1952)]) frameS m)
    (hm' : Match (Env.ofMachine m [(fb m0, 1952)]) S' m') (hwf : (Env.ofMachine m [(fb m0, 1952)]).WF)
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hk : ∀ r ∈ loopRegs, S'.reg r = some (.reg r)) : Mid rows m0 j m' := by
  have hd : m'.dmem = m.dmem := hm'.dmem_eq hwf hmem
  have hr : ∀ r ∈ loopRegs, m'.regs.getXReg r = m.regs.getXReg r := fun r hr' ↦
    (rv hm' (hk r hr')).trans rfl
  refine ⟨Ring.Fr.ofBlock h.fr hm hm' hwf rfl hmem hsp (by simp), hd ▸ h.low, h.hj, h.hjq, h.ok,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr .X19 (by simp [loopRegs]), h.x19]
  · rw [hr .X25 (by simp [loopRegs]), h.x25]
  · rw [hr .X28 (by simp [loopRegs]), h.x28]
  · rw [hr .X20 (by simp [loopRegs]), h.x20]
  · rw [hr .X21 (by simp [loopRegs]), h.x21]
  · rw [hr .X22 (by simp [loopRegs]), h.x22]
  · rw [hr .X23 (by simp [loopRegs]), h.x23]
  · rw [hr .X24 (by simp [loopRegs]), h.x24]
  · rw [hr .X29 (by simp [loopRegs]), h.x29]

/-- **An input** of the entry, unchanged in a body. -/
theorem input_same' (hpre : EachRowFinalPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    {a : BitVec 64} {n : Nat} (h : WhirIn m0 a n eachRowFinalStack) :
    ∀ i < n, m.dmem.get? (a + BitVec.ofNat 64 i) = m0.dmem.get? (a + BitVec.ofNat 64 i) :=
  EachRow.input_same hfr hpre.1.1.2.1 h.1.2 h.2 fun _ _ h ↦ h

/-- The frame alone, as an environment. -/
theorem frame_env [Labels] (hpre : EachRowFinalPre rows op m0) {m : MachineData} (hfr : FR m0 m) :
    (Env.ofMachine m [(fb m0, 1952)]).WF ∧ Match (Env.ofMachine m [(fb m0, 1952)]) frameS m := by
  have hstk := hpre.1.1
  have hS : 3184 ≤ m0.regs.SP.toNat := hstk.2.1
  exact ⟨Env.wf_of ⟨⟨fun i hi ↦ hfr.kept _ (Ring.frame_mapped hstk (by decide) i hi),
      Ring.base_noWrap (by omega)⟩, trivial⟩ (List.pairwise_singleton _ _),
    match_ofMachine ⟨rfl, fun _ ↦ Ring.frame_aligned hstk (by decide) rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval]) trivial trivial trivial trivial⟩

end

end NativeRustcVmArm.Whir.EachRowOfFinalLevel
