module

public import NativeRustcVmArm.Bus.BusLayout.Sizes

/-!
# `bus_layout`: the frame's words across blocks, the placements' loop invariant

- `frame_out`, `word_keep`: a frame word outside what a callee changes.
- `keep_out`, `slot_keep`, `slot_new`: a frame word after a block writing a range of the frame
  (slot stores, `ite (x = k) V old`).
- `frm_block`: the frame through a block writing below the slots.
- `OffsAt`, `PInv`, `PEnd`: the placements' loop (`.LBusLayout_11`) and its exit.
- `b12_*`, `b16_*`, `b18_*`: the writes of the blocks building the layout, by `decide`.
-/

namespace NativeRustcVmArm.Bus.BusLayout

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BusLayout
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout
open NativeRustcVm (wordOf wordsOf WordAt WordsAt)
open NativeRustcVm.Transcript (off)
open LeanVM.Protocol.Verifier (Placement)

@[expose] public section

/-! ## Frame words -/

section
variable {m0 : MachineData}

/-- A frame byte outside the `n` frame bytes at `lo`. -/
theorem frame_out (hF : 1840 ≤ m0.regs.SP.toNat) {lo n p i : Nat} (hlo : lo + n ≤ 1840)
    (hpi : p + i < 1840) (hd : p + i < lo ∨ lo + n ≤ p + i) :
    ¬InRange (fa m0 lo) n (fa m0 p + BitVec.ofNat 64 i) := by
  have hb : (fb m0).toNat = m0.regs.SP.toNat - 1840 := base_toNat hF
  have hlt := m0.regs.SP.toNat_lt
  have ha : (fa m0 lo).toNat = (fb m0).toNat + lo := NativeRustcVm.toNat_add_ofNat (by omega)
  have hnw : NoWrap (fa m0 lo) n := by unfold NoWrap; rw [ha]; omega
  rw [NativeRustcVm.addr_add_add, Sym.inRange_iff hnw, ha,
    NativeRustcVm.toNat_add_ofNat (by omega)]
  omega

/-- A frame word that a change does not touch. -/
theorem word_keep {d d' : Mem 64} {W : BitVec 64 → Prop} {o : Nat} {w : UInt64}
    (hs : SameOutside d d' W) (hW : ∀ i < 8, ¬W (fa m0 o + BitVec.ofNat 64 i))
    (h : WordAt d (fa m0 o) w) : WordAt d' (fa m0 o) w :=
  NativeRustcVm.BytesAt.of_sameOutside h hs fun i hi ↦
    hW i (by rwa [NativeRustcVm.length_wordBytes] at hi)

variable [Labels] {env : Env} {S : SState} {st : MachineData}

/-- A frame word outside the range `[lo, hi)` a block wrote. -/
theorem keep_out (hm : Match env S st) (hwf : env.WF)
    (hb : env.regions[0]? = some (fb m0, 1840)) (hF : 1840 ≤ m0.regs.SP.toNat) {lo hi : Nat}
    (hlh : lo < hi) (hhi : hi ≤ 1840)
    (hall : (S.mem.all fun w ↦ w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) =
      true)
    {o : Nat} {w : UInt64} (ho : o + 8 ≤ 1840) (hd : o + 8 ≤ lo ∨ hi ≤ o)
    (h : WordAt env.mem0 (fa m0 o) w) : WordAt st.dmem (fa m0 o) w := by
  have hfb : (fb m0).toNat + 1840 ≤ 2 ^ 64 := by
    rw [base_toNat hF]; have := m0.regs.SP.toNat_lt; omega
  exact wordAt_keep_out hfb (same_of_writes_in hm hwf hb hfb hlh hhi hall) hlh hhi ho hd h

/-- A frame word of a slot store, at another index: the old word. -/
theorem slot_keep (hm : Match env S st) (hb : env.regions[0]? = some (fb m0, 1840)) {o : Nat}
    (hle : o + 8 ≤ 1840) {x V : Sym} {kk : Nat}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem =
      some (.ite (.cmp .eq .W64 x (.lit kk)) V (.load 0 o 8), i))
    (hx : x.eval env ≠ BitVec.ofNat 64 kk) {w : UInt64} (h : WordAt env.mem0 (fa m0 o) w) :
    WordAt st.dmem (fa m0 o) w := by
  have h' := slot_word hm hb hle hw
  rw [ite_eq_right_of_eq_false _ _ (eq_false hx),
    load_word (by rw [Env.base_eq hb]; exact h)] at h'
  exact h'

/-- A frame word of a slot store, at its index: the stored value. -/
theorem slot_new (hm : Match env S st) (hb : env.regions[0]? = some (fb m0, 1840)) {o : Nat}
    (hle : o + 8 ≤ 1840) {x V : Sym} {kk : Nat}
    (hw : ∀ i < 8, findWrite 0 (o + i) S.mem =
      some (.ite (.cmp .eq .W64 x (.lit kk)) V (.load 0 o 8), i))
    (hx : x.eval env = BitVec.ofNat 64 kk) :
    WordAt st.dmem (fa m0 o) (UInt64.ofBitVec (V.eval env)) := by
  have h' := slot_word hm hb hle hw
  rwa [ite_eq_left_of_eq_true _ _ (eq_true hx)] at h'

end

/-- **The frame through a block** writing `[lo, hi)` of the frame, below the slots. -/
theorem frm_block [Labels] {m0 st st' : MachineData} {S S' : SState}
    (hN : busLayoutStack ≤ m0.regs.SP.toNat) (hfr : Frm m0 st)
    (hm : Match (Env.ofMachine st [(fb m0, 1840)]) S st)
    (hm' : Match (Env.ofMachine st [(fb m0, 1840)]) S' st')
    (hwf : (Env.ofMachine st [(fb m0, 1840)]).WF) (hsp : S'.sp = S.sp)
    (hkeep : ∀ r ∈ keep, ∃ v, S.reg r = some v ∧ S'.reg r = some v) {lo hi : Nat}
    (hhi : hi ≤ 1760)
    (hall : (S'.mem.all fun w ↦ w.r == 0 && decide (lo ≤ w.off) && decide (w.off + w.n ≤ hi)) =
      true) : Frm m0 st' := by
  have hsl : ∀ p ∈ slots, 1760 ≤ p.1 := by decide
  refine Fr.ofBlockW hfr hm hm' hwf rfl hsp hkeep rfl (by decide) hN slots_le fun w hw ↦ ?_
  have := List.all_eq_true.mp hall w hw
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact .inl ⟨this.1.1, by omega, fun p hp ↦ .inl (by have := hsl p hp; omega)⟩

/-! ## Placements in the frame -/

theorem off_fa (m0 : MachineData) (o : Nat) : off (fa m0 o) 8 = fa m0 (o + 8) := by
  simp only [off, fa, NativeRustcVm.addr_add_add]

theorem pa_mk {d : Mem 64} {m0 : MachineData} {o : Nat} {p : Placement}
    (h1 : p.variableCount < 2 ^ 64) (h2 : p.index < 2 ^ 64)
    (h3 : WordAt d (fa m0 o) p.variableCount.toUInt64)
    (h4 : WordAt d (fa m0 (o + 8)) p.index.toUInt64) : PlacementAt d (fa m0 o) p :=
  ⟨h1, h2, h3, by rw [off_fa]; exact h4⟩

/-- A placement in the frame, its two words moved. -/
theorem pa_move {d d' : Mem 64} {m0 : MachineData} {o : Nat} {p : Placement}
    (h : PlacementAt d (fa m0 o) p)
    (k1 : WordAt d (fa m0 o) p.variableCount.toUInt64 →
      WordAt d' (fa m0 o) p.variableCount.toUInt64)
    (k2 : WordAt d (fa m0 (o + 8)) p.index.toUInt64 → WordAt d' (fa m0 (o + 8)) p.index.toUInt64) :
    PlacementAt d' (fa m0 o) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [off_fa] at h4
  exact pa_mk h1 h2 (k1 h3) (k2 h4)

/-! ## The placements' loop -/

/-- The offsets in the frame at `440`. -/
def OffsAt (d : Mem 64) (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) :
    Prop :=
  ∀ j < nf m0 + bl.length, WordAt d (fa m0 (440 + 8 * j)) ((O L bl m0).1.getD j 0).toUInt64

/-- **The placements' loop head** `.LBusLayout_11`, `j` placements pushed. -/
structure PInv (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData) (j : Nat)
    (st : MachineData) : Prop where
  fr : Frm m0 st
  lt : j < nf m0 + bl.length
  sizes : SizesAt st.dmem L bl m0 (nf m0 + bl.length)
  offs : OffsAt st.dmem L bl m0
  part : Part st.dmem L bl m0 j
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x8 : (st.regs.getXReg .X8).toNat = j
  x9 : (st.regs.getXReg .X9).toNat = min j (nf m0)
  x10 : (st.regs.getXReg .X10).toBitVec = fa m0 888
  x11 : (st.regs.getXReg .X11).toBitVec = fa m0 944
  x20 : (st.regs.getXReg .X20).toNat = nf m0
  x21 : (st.regs.getXReg .X21).toNat = nf m0 + bl.length
  x22 : (st.regs.getXReg .X22).toBitVec = fa m0 440
  x23 : (st.regs.getXReg .X23).toBitVec = fa m0 8

/-- **Every placement pushed** (`.LBusLayout_17`). -/
structure PEnd (L : LayoutW) (bl : List NativeRustcVm.Data.Block) (m0 : MachineData)
    (st : MachineData) : Prop where
  fr : Frm m0 st
  part : Part st.dmem L bl m0 (nf m0 + bl.length)
  x19 : st.regs.getXReg .X19 = m0.regs.X0
  x9 : (st.regs.getXReg .X9).toNat = nf m0

/-! ## The blocks' writes -/

theorem b12_depth : ∀ t < 8, findWrite 0 (872 + t) (Bus.after b12 sF).mem = some (.reg .X1, t) := by
  rw [Bus.after_eq run_b12]; decide +kernel

theorem b12_count : ∀ t < 8, findWrite 0 (936 + t) (Bus.after b12 sF).mem = some (.lit 0, t) := by
  rw [Bus.after_eq run_b12]; decide +kernel

theorem b12_mem : ((Bus.after b12 sF).mem.all fun w ↦
    w.r == 0 && decide (872 ≤ w.off) && decide (w.off + w.n ≤ 1760)) = true := by
  rw [Bus.after_eq run_b12]; decide +kernel

theorem b16_lo : ∀ j < 3, ∀ t < 8, findWrite 0 (888 + 16 * j + t) (Bus.after b16 sF16).mem =
    some (.ite (.cmp .eq .W64 (.reg .X9) (.lit j)) (.reg .X13) (.load 0 (888 + 16 * j) 8), t) := by
  rw [Bus.after_eq run_b16]; decide +kernel

theorem b16_hi : ∀ j < 3, ∀ t < 8, findWrite 0 (888 + 16 * j + 8 + t) (Bus.after b16 sF16).mem =
    some (.ite (.cmp .eq .W64 (.reg .X9) (.lit j)) (.reg .X12) (.load 0 (888 + 16 * j + 8) 8),
      t) := by
  rw [Bus.after_eq run_b16]; decide +kernel

theorem b16_mem : ((Bus.after b16 sF16).mem.all fun w ↦
    w.r == 0 && decide (888 ≤ w.off) && decide (w.off + w.n ≤ 936)) = true := by
  rw [Bus.after_eq run_b16]; decide +kernel

theorem b18_lo : ∀ j < 51, ∀ t < 8, findWrite 0 (944 + 16 * j + t) (Bus.after b18 sT).mem =
    some (.ite (.cmp .eq .W64 (.reg .X14) (.lit j)) (.reg .X13) (.load 0 (944 + 16 * j) 8), t) := by
  rw [Bus.after_eq run_b18]; decide +kernel

theorem b18_hi : ∀ j < 51, ∀ t < 8, findWrite 0 (944 + 16 * j + 8 + t) (Bus.after b18 sT).mem =
    some (.ite (.cmp .eq .W64 (.reg .X14) (.lit j)) (.reg .X12) (.load 0 (944 + 16 * j + 8) 8),
      t) := by
  rw [Bus.after_eq run_b18]; decide +kernel

theorem b18_count : ∀ t < 8, findWrite 0 (936 + t) (Bus.after b18 sT).mem =
    some (.bin .add .W64 (.reg .X14) (.lit 1), t) := by
  rw [Bus.after_eq run_b18]; decide +kernel

theorem b18_mem : ((Bus.after b18 sT).mem.all fun w ↦
    w.r == 0 && decide (936 ≤ w.off) && decide (w.off + w.n ≤ 1760)) = true := by
  rw [Bus.after_eq run_b18]; decide +kernel

end

end NativeRustcVmArm.Bus.BusLayout
