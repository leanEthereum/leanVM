module

public import NativeRustcVmArm.Whir.EachRowOfNextLevel.Start

/-!
# `each_row` with `next_level`'s closure: inside an iteration

`Mid j m`: in iteration `j` (`j` below both counts), the invariant's frame, locals, batched value
and loop registers, X26 query `j`. Kept by a callee changing memory in `HitN` only and keeping the
callee-saved registers (`Mid.call`), and by a block run from `frameS` that writes nothing and keeps
the loop's registers (`Mid.block`).
-/

namespace NativeRustcVmArm.Whir.EachRowOfNextLevel

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.EachRowOfNextLevel
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
  bat : EWAt m.dmem (bOf m0) (parOf rows m0 j)
  x19 : m.regs.getXReg .X19 = rows.size.toUInt64
  x20 : (m.regs.getXReg .X20).toBitVec = bOf m0
  x21 : m.regs.getXReg .X21 = m0.regs.X3
  x22 : m.regs.getXReg .X22 = (8 * ((qsOf m0).size - j)).toUInt64
  x23 : (m.regs.getXReg .X23).toBitVec = (nextEnv m0 4).toBitVec + BitVec.ofNat 64 (8 + 16 * j)
  x24 : m.regs.getXReg .X24 = j.toUInt64
  x26 : m.regs.getXReg .X26 = (qsOf m0)[j]'hjq

/-- The registers the loop keeps. -/
def loopRegs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X26]

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- **A call** changing memory in `HitN` only. -/
theorem Mid.call (hpre : EachRowNextPre rows op m0) {m m' : MachineData} (h : Mid rows m0 j m)
    (hs : SameOutside m.dmem m'.dmem (HitN m0)) (hsv : Saved m m') : Mid rows m0 j m' := by
  have hl := lay hpre
  have hr : ∀ r, calleeSaved r = true → m'.regs.getXReg r = m.regs.getXReg r := hsv.1
  exact ⟨EachRow.fr_hit hl h.fr hsv.2.1 hsv.2.2 hs slots_ok, h.low.keep hl hs, h.hj, h.hjq,
    bat_keep hpre h.bat hs fun q h ↦ hl.hit_stack h,
    (hr .X19 rfl).trans h.x19, (hr .X20 rfl) ▸ h.x20, (hr .X21 rfl).trans h.x21,
    (hr .X22 rfl).trans h.x22, (hr .X23 rfl) ▸ h.x23, (hr .X24 rfl).trans h.x24,
    (hr .X26 rfl).trans h.x26⟩

/-- **A block** run from the frame alone, without writes, keeping SP and the loop's registers. -/
theorem Mid.block [Labels] {m m' : MachineData} {S' : SState} (h : Mid rows m0 j m)
    (hm : Match (Env.ofMachine m [(fb m0, 2000)]) frameS m)
    (hm' : Match (Env.ofMachine m [(fb m0, 2000)]) S' m') (hwf : (Env.ofMachine m [(fb m0, 2000)]).WF)
    (hmem : S'.mem = []) (hsp : S'.sp = .ptr 0 0)
    (hk : ∀ r ∈ loopRegs, S'.reg r = some (.reg r)) : Mid rows m0 j m' := by
  have hd : m'.dmem = m.dmem := hm'.dmem_eq hwf hmem
  have hr : ∀ r ∈ loopRegs, m'.regs.getXReg r = m.regs.getXReg r := fun r hr' ↦
    (rv hm' (hk r hr')).trans rfl
  refine ⟨Ring.Fr.ofBlock h.fr hm hm' hwf rfl hmem hsp (by simp), hd ▸ h.low, h.hj, h.hjq,
    hd ▸ h.bat, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr .X19 (by simp [loopRegs]), h.x19]
  · rw [hr .X20 (by simp [loopRegs]), h.x20]
  · rw [hr .X21 (by simp [loopRegs]), h.x21]
  · rw [hr .X22 (by simp [loopRegs]), h.x22]
  · rw [hr .X23 (by simp [loopRegs]), h.x23]
  · rw [hr .X24 (by simp [loopRegs]), h.x24]
  · rw [hr .X26 (by simp [loopRegs]), h.x26]

/-- An input of the entry, in a body, for a callee using `N'` bytes of stack. -/
theorem whirIn_input (hpre : EachRowNextPre rows op m0) {m : MachineData} (hfr : FR m0 m)
    {a : BitVec 64} {n N' : Nat} (h : WhirIn m0 a n eachRowNextStack)
    (hle : 2000 + N' ≤ eachRowNextStack) : WhirIn m a n N' :=
  ⟨⟨fun i hi ↦ hfr.kept _ (h.1.1 i hi), h.1.2⟩, hfr.apart hpre.1.1.2.1 h.2 hle⟩

end

end NativeRustcVmArm.Whir.EachRowOfNextLevel
