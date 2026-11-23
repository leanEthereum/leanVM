module

public import NativeRustcVmX64.Bus.AccumulateSide.Entry

/-!
# `accumulate_side`: what its calls need (x86-64)

A callee's stack (`St.stackOk`), an input slice for it (`St.sliceOk`) and as the entry's
(`St.slice_eq`); a callee's changes as `St.call` takes them (`changes_call`, `same_call`); the
placements in the side layout (`fw_place`, `tb_place`); part of an input apart from another
(`apart_sub`); infix lemmas for the split blocks.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Transcript NativeRustcVm.Transcript
open NativeRustcVmX64.Vm.AccumulateSide
open NativeVm.Model NativeRustcVm.Bus NativeRustcVm.Layout

public section

theorem b2a_in_code : b2a.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b2Offset) :=
  List.IsInfixAt.trans (infix_take b2 15) b2_in_code (by simp [b2])
theorem b2b_in_code : b2b.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b2Offset + b2a.length) :=
  List.IsInfixAt.trans (infix_drop b2 15) b2_in_code (by simp [b2b, b2])
theorem b18a_in_code : b18a.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b18Offset) :=
  List.IsInfixAt.trans (infix_take b18 4) b18_in_code (by simp [b18])
theorem b18b_in_code : b18b.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b18Offset + b18a.length) :=
  List.IsInfixAt.trans (infix_drop b18 4) b18_in_code (by simp [b18b, b18])
theorem b23a_in_code : b23a.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b23Offset) :=
  List.IsInfixAt.trans (infix_take b23 22) b23_in_code (by simp [b23])
theorem b23b_in_code : b23b.IsInfixAt code (NativeRustcVmX64.Vm.AccumulateSide.b23Offset + b23a.length) :=
  List.IsInfixAt.trans (infix_drop b23 22) b23_in_code (by simp [b23b, b23])

/-- Part of a range apart from another. -/
theorem apart_sub {a b : BitVec 64} {n N o l : Nat} (h : Apart a n b N)
    (hb : NativeRustcVm.NoWrap b N) (hol : o + l ≤ N) (hl : 0 < l) : Apart a n (off b o) l := by
  unfold NativeRustcVm.NoWrap at hb
  unfold Apart at h ⊢
  rw [toNat_off (by omega)]
  omega

/-- No byte of an empty range. -/
theorem not_inRange_nil {a q : BitVec 64} : ¬ NativeRustcVm.InRange a 0 q := fun h ↦ by
  unfold NativeRustcVm.InRange at h; omega

/-- **A callee's changes of no outputs** as `St.call` takes them. -/
theorem changes_call {m0 st m' : MachineData} {Nc : Nat} (hc : Changes st m' Nc 0 0) :
    NativeRustcVm.SameOutside st.dmem m'.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨ NativeRustcVm.InRange (off (fb m0) 0) 0 q ∨
        Z q) :=
  NativeRustcVm.SameOutside.mono hc fun _ hq ↦ hq.elim (fun h ↦ absurd h not_inRange_nil) .inl

/-- **A callee changing its stack** as `St.call` takes it. -/
theorem same_call {m0 st m' : MachineData} {Nc : Nat}
    (hc : NativeRustcVm.SameOutside st.dmem m'.dmem (NativeRustcVm.InRange (stackBelow st Nc) Nc)) :
    NativeRustcVm.SameOutside st.dmem m'.dmem (fun q ↦
      NativeRustcVm.InRange (stackBelow st Nc) Nc q ∨ NativeRustcVm.InRange (off (fb m0) 0) 0 q ∨
        Z q) :=
  NativeRustcVm.SameOutside.mono hc fun _ hq ↦ .inl hq

section
variable [Labels] {L : LayoutW} {rows : Array Nat} {bl : List NativeRustcVm.Data.Block}
  {Fm : Array (Array FormW)} {SL : BusLayoutW} {m0 : MachineData}

/-- A callee's stack below the frame. -/
theorem St.stackOk (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 O V D 0 m) {Nc : Nat}
    (hle : F + Nc ≤ N) : StackOk m Nc :=
  stackOk_callee h.stack hst.fr.kept (by rw [hst.fr.sp, off_zero]) hle

/-- A callee's stack is at least `8` above address `0`. -/
theorem St.sb8 (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 O V D 0 m) {Nc : Nat}
    (hle : F + Nc + 8 ≤ N) : 8 ≤ (stackBelow m Nc).toNat := by
  rw [stackBelow_callee (by rw [hst.fr.sp, off_zero]) (by have := h.spN; omega),
    stackBelow_toNat (by have := h.spN; omega)]
  have := h.spN
  omega

/-- An input slice for a callee. -/
theorem St.sliceOk (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {m : MachineData} (hst : St m0 O V D 0 m) {Nc : Nat}
    (hle : F + Nc ≤ N) {a n : BitVec 64} (hs : SliceOk m0 a n N) : SliceOk m a n Nc :=
  ⟨⟨Mapped.keeps hs.1.1 hst.fr.kept, hs.1.2⟩,
    apart_callee hs.2 (by rw [hst.fr.sp, off_zero]) h.spN hle⟩

/-- An input slice apart from the forms reads as at the entry. -/
theorem St.slice_eq (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) {a n : BitVec 64} (hs : SliceOk m0 a n N)
    (hf : Apart a (16 * n.toNat) (reg m0 .rsi) formsBytes) : slice m a n = slice m0 a n := by
  unfold slice
  rw [NativeRustcVm.ewsOf_congr fun i hi ↦ hst.same _ fun hq ↦ hq.elim
    (fun hq ↦ NativeRustcVm.Apart.not_inRange_add hf hs.1.2 h.forms_nw hi (hO _ hq))
    fun hq ↦ NativeRustcVm.Apart.not_inRange_add hs.2 hs.1.2 (noWrap_stackBelow h.stack) hi
      (Ring.inRange_le hq (by omega))]

/-- The point in the body. -/
theorem St.pt (h : Pre L rows bl Fm SL m0) {O : BitVec 64 → Prop} {V : Nat → UInt64}
    {D : List (Sym × Nat)} {o : Nat} {m : MachineData} (hst : St m0 O V D o m)
    (hO : ∀ q, O q → outs m0 q) : slice m (stackArg m0 7) (stackArg m0 8) = ptA m0 :=
  St.slice_eq h hst hO h.pt (Apart.symm' h.fPt)

/-- **Framework placement `i`** in the side layout, at byte `16 + 16 i`. -/
theorem fw_place (h : Pre L rows bl Fm SL m0) {i : Nat} (hi : i < SL.framework.size) :
    NativeRustcVm.Bus.PlacementAt m0.dmem (off (stackArg m0 0) (16 + 16 * i)) (fpl SL i) := by
  have := h.sl.framework.2.2 i hi
  rw [off_off, show 8 + (8 + NativeRustcVm.Bus.placementBytes * i) = 16 + 16 * i by
    unfold NativeRustcVm.Bus.placementBytes; omega] at this
  simpa [fpl, Array.getD_eq_getD_getElem?, hi] using this

/-- **Table placement `j`** in the side layout, at byte `72 + 16 j`. -/
theorem tb_place (h : Pre L rows bl Fm SL m0) {j : Nat} (hj : j < SL.tables.size) :
    NativeRustcVm.Bus.PlacementAt m0.dmem (off (stackArg m0 0) (72 + 16 * j)) (tpl SL j) := by
  have := h.sl.tables.2.2 j hj
  rw [off_off, show 64 + (8 + NativeRustcVm.Bus.placementBytes * j) = 72 + 16 * j by
    unfold NativeRustcVm.Bus.placementBytes; omega] at this
  simpa [tpl, Array.getD_eq_getD_getElem?, hj] using this

end

end

end NativeRustcVmX64.Bus.AccumulateSide
