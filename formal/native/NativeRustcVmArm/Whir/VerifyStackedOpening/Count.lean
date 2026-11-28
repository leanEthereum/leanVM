module

public import NativeRustcVmArm.Whir.VerifyStackedOpening.Basic

/-!
# `verify_stacked_opening`: counting the placed claims

`b0` (the prologue) reads the claims' count; none: `.LVerifyStackedOpening_8` (`b9`). Else `b1`
starts the loop at `.LVerifyStackedOpening_3` (`b3`, `CntInv i`): `b3` reads claim `i`'s column,
`b2` its placement's `present` word (a column below `158`), `b2`, `b4` count it and step to the
next claim or `.LVerifyStackedOpening_5` (`b5`) after the last (`cnt_step`). `onStack_isSome`: a
claim is placed iff its column is below `158` and that word is nonzero.
-/

namespace NativeRustcVmArm.Whir.VerifyStackedOpening

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmArm.Ring NativeRustcVm.Whir NativeRustcVmArm.Vm.VerifyStackedOpening
open NativeRustcVm.Layout (LayoutWAt ClaimsWAt ColumnClaimAt PlacementWAt)

@[expose] public section

/-- **Up to `b11`**: the frame, the arguments in X20 to X29, the caller's X0, X2, X4. -/
structure Base (cs : Array ColumnClaimW) (m0 st : MachineData) : Prop where
  fr : VFr m0 st
  x20 : st.regs.getXReg .X20 = m0.regs.X6
  x21 : st.regs.getXReg .X21 = m0.regs.X5
  x22 : st.regs.getXReg .X22 = m0.regs.X1
  x24 : st.regs.getXReg .X24 = m0.regs.X3
  x26 : st.regs.getXReg .X26 = m0.regs.X7
  x28 : (st.regs.getXReg .X28).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 8
  x29 : st.regs.getXReg .X29 = cs.size.toUInt64
  x0 : st.regs.getXReg .X0 = m0.regs.X0
  x2 : st.regs.getXReg .X2 = m0.regs.X2
  x4 : st.regs.getXReg .X4 = m0.regs.X4
  fo : SameOutside m0.dmem st.dmem (InRange (base m0 512) 512)

/-- The registers `Base` names. -/
def baseRegs : List XReg := [.X0, .X2, .X4, .X20, .X21, .X22, .X24, .X26, .X28, .X29]

/-- **The counting loop's head**, before claim `i`. -/
structure CntInv (layout : LayoutW) (cs : Array ColumnClaimW) (m0 : MachineData) (i : Nat)
    (st : MachineData) : Prop where
  base : Base cs m0 st
  hi : i < cs.size
  x8 : st.regs.getXReg .X8 = (placedOf layout cs i).toUInt64
  x9 : (st.regs.getXReg .X9).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 120
  x10 : (st.regs.getXReg .X10).toBitVec = m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i)
  x11 : st.regs.getXReg .X11 = (cs.size - i).toUInt64

end

public section

/-- **A claim is placed** iff its column is below `158` and its placement's `present` word is
nonzero. -/
theorem onStack_isSome {d : Mem 64} {a : BitVec 64} {layout : LayoutW} (hl : LayoutWAt d a layout)
    (c : ColumnClaimW) : (c.onStack layout).isSome =
      (decide (c.column < 158) && NativeRustcVm.wordOf d (off a (120 + 24 * c.column)) != 0) := by
  unfold ColumnClaimW.onStack
  by_cases hc : c.column < 158
  · have hc' : c.column < layout.placements.size := by rw [hl.placements_size]; exact hc
    rw [Array.getElem?_eq_getElem hc']
    have hw := hl.placements c.column hc'
    cases hp : layout.placements[c.column] with
    | none =>
      rw [hp] at hw
      simp [hc, NativeRustcVm.wordOf_of_wordAt (show NativeRustcVm.WordAt d
        (off a (120 + 24 * c.column)) 0 from hw)]
    | some p =>
      rw [hp] at hw
      simp [hc, NativeRustcVm.wordOf_of_wordAt (show NativeRustcVm.WordAt d
        (off a (120 + 24 * c.column)) 1 from hw.1)]
  · rw [Array.getElem?_eq_none (by rw [hl.placements_size]; show 158 ≤ c.column; omega)]
    simp [hc]

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

omit [Labels] in
/-- `Base` across a block keeping its registers. -/
theorem Base.keep {st st' : MachineData} (hb : Base cs m0 st) (hf : VFr m0 st')
    (hd : st'.dmem = st.dmem)
    (hk : ∀ r ∈ baseRegs, st'.regs.getXReg r = st.regs.getXReg r) : Base cs m0 st' :=
  ⟨hf, (hk .X20 (by simp [baseRegs])).trans hb.x20, (hk .X21 (by simp [baseRegs])).trans hb.x21,
    (hk .X22 (by simp [baseRegs])).trans hb.x22, (hk .X24 (by simp [baseRegs])).trans hb.x24,
    (hk .X26 (by simp [baseRegs])).trans hb.x26, (hk .X28 (by simp [baseRegs])) ▸ hb.x28,
    (hk .X29 (by simp [baseRegs])).trans hb.x29, (hk .X0 (by simp [baseRegs])).trans hb.x0,
    (hk .X2 (by simp [baseRegs])).trans hb.x2, (hk .X4 (by simp [baseRegs])).trans hb.x4,
    hd ▸ hb.fo⟩

variable (h : Parts a s layout target coefficients point slices cs z value m0)
include h

/-- Claim `i`'s column word, in a state of the frame. -/
theorem Parts.column_word {st : MachineData} (hf : VFr m0 st) {i : Nat} (hi : i < cs.size) :
    NativeRustcVm.WordAt st.dmem (m0.regs.X5.toBitVec + BitVec.ofNat 64 (8 + 608 * i))
      cs[i].column.toUInt64 := by
  have hc := h.cl
  have hs := h.same_in hf mem_cl
  have hk : 8 + 608 * i + 8 ≤ NativeRustcVm.Layout.claimsBytes := by
    have := hc.len_le
    have : NativeRustcVm.Layout.claimCap = 160 := rfl
    show _ ≤ 97288
    omega
  exact NativeRustcVm.Layout.WordAt.of_same (hc.claims i hi).column (hs.sub hk) le_rfl

/-- A column's placement word, in a state of the frame. -/
theorem Parts.place_word {st : MachineData} (hf : VFr m0 st) {c : Nat} (hc : c < 158) :
    NativeRustcVm.wordOf st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (120 + 24 * c)) =
      NativeRustcVm.wordOf m0.dmem (off m0.regs.X1.toBitVec (120 + 24 * c)) := by
  have hs := h.same_in hf mem_lay
  refine NativeRustcVm.wordOf_congr fun j hj ↦ ?_
  rw [NativeRustcVm.addr_add_add]
  exact hs _ (by show _ < 3912; omega)

end

end

end NativeRustcVmArm.Whir.VerifyStackedOpening
