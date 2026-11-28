module

public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Weight.Entry

/-!
# `ring_weight`: `r` copied into the powers

For `|r| ≥ 2`, `b6` sets up the copy of the pairs and `b7` copies one per turn (`CopyI`); `b8`
ends there when `|r|` is even. Otherwise (and from `b5` when `|r| = 1`) `b9`, `b10` copy the last
element (`OddI`). Either way all of `r` is copied at `b11` (`Copied`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

@[expose] public section

/-- **The pairs' copy, turn `t`**: `2 t` elements copied, one more pair to go. -/
structure CopyI (m0 : MachineData) (t : Nat) (m : MachineData) : Prop where
  base : Base m0 m
  lt : 2 * t + 2 ≤ nR m0
  x10 : (m.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2)
  x11 : (m.regs.getXReg .X11).toBitVec = m0.regs.X1.toBitVec + BitVec.ofNat 64 (32 * t + 16)
  x12 : (m.regs.getXReg .X12).toBitVec = fb m0 + BitVec.ofNat 64 (32 * t + 32)
  x13 : (m.regs.getXReg .X13).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2 - 2 * t)
  cp : CopyAt m0 m.dmem (2 * t)

/-- **The last element to copy** (`|r|` odd). -/
structure OddI (m0 m : MachineData) : Prop where
  base : Base m0 m
  odd : nR m0 % 2 = 1
  x10 : (m.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 - 1)
  cp : CopyAt m0 m.dmem (nR m0 - 1)

/-- **`r` copied.** -/
structure Copied (m0 m : MachineData) : Prop where
  base : Base m0 m
  cp : CopyAt m0 m.dmem (nR m0)

end

public section

variable {m0 : MachineData}

theorem and62 : ∀ n < 64, n &&& 62 = n / 2 * 2 := by decide

/-- A power before a window of the powers is kept. -/
theorem slot_before (h : RingWeightPre m0) {j o : Nat} (hj : 16 + 16 * j + 16 ≤ o) (ho : o ≤ 688) :
    (slotA m0 j).toNat + 16 ≤ (fb m0 + BitVec.ofNat 64 o).toNat ∧ (slotA m0 j).toNat + 16 ≤ 2 ^ 64 := by
  have := m0.regs.SP.toNat_lt
  rw [frame_toNat h (by omega), frame_toNat h (by omega)]
  omega

variable [Host] {k : Nat}

/-- **The pairs' copy set up** (`b6`). -/
theorem stepB6 (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hB : Base m0 m)
    (h2 : 2 ≤ nR m0) {R : MachineState → Prop}
    (cont : ∀ m', CopyI m0 0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b7Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b6Offset)⟩ := by
  refine exec_then (hb b6_in_code (by simp [b6]) hp) run_b6 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b6Offset + b6.length = k + NativeRustcVmArm.Vm.RingWeight.b7Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b6_next]]
  have hn := n36 h
  have h62 : BinOp.apply .and .W64 m0.regs.X2.toBitVec (BitVec.ofNat 64 62) =
      BitVec.ofNat 64 (nR m0 / 2 * 2) := by
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64]
    show m0.regs.X2.toBitVec &&& BitVec.ofNat 64 62 = _
    have : nR m0 = m0.regs.X2.toBitVec.toNat := rfl
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 62 < 2 ^ 64 by decide), and62 _ (by omega)]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  refine cont st.data ⟨hB.after (match_nil m) hm1 (by decide) (by decide)
    (regs_fr hB.fr hm1 rfl rfl), by omega, ?_, ?_, ?_, ?_, fun j hj ↦ absurd hj (by omega)⟩
  · refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hB.x2]
    exact h62
  · refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hB.x1, add_bv]
  · refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64]
    show m.regs.SP.toBitVec + _ = _
    rw [hB.fr.sp]
  · refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hB.x2]
    exact h62

/-- **A pair copied** (`b7`): the next turn, or the pairs done at `b8`. -/
theorem stepB7 (hp : Placed code k) (h : RingWeightPre m0) {t : Nat} {m : MachineData}
    (hI : CopyI m0 t m) {R : MachineState → Prop}
    (hnext : ∀ m', CopyI m0 (t + 1) m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b7Offset)⟩)
    (hdone : ∀ m', Base m0 m' → (m'.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2) →
      CopyAt m0 m'.dmem (nR m0 / 2 * 2) → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b8Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b7Offset)⟩ := by
  have hn := n36 h
  have hnn : nR m0 = m0.regs.X2.toNat := rfl
  have hlt := hI.lt
  have hfr := hI.base.fr
  have hr := h.2.2.1
  let rs : List (BitVec 64 × Nat) :=
    [(m0.regs.X1.toBitVec + BitVec.ofNat 64 (32 * t), 32), (fb m0 + BitVec.ofNat 64 (16 + 32 * t), 32)]
  have hwf : (Env.ofMachine m rs).WF :=
    win_wf2 (arg_win hfr hr.1 (by omega) (by decide)) (frame_win h hfr (by omega) (by decide))
      (win_apart h hr.2 hr.1.2 (by omega) (by decide) (by omega))
  have hm : Match (Env.ofMachine m rs) copyS m :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl
      ⟨by
        show _ = m0.regs.X1.toBitVec + BitVec.ofNat 64 (32 * t) + BitVec.ofInt 64 (16 : Nat)
        rw [hI.x11, ofInt_lit, addr_eq (z := 32 * t + 16) rfl],
      by
        show _ = fb m0 + BitVec.ofNat 64 (16 + 32 * t) + BitVec.ofInt 64 (16 : Nat)
        rw [hI.x12, ofInt_lit, addr_eq (z := 32 * t + 32) (by omega)], trivial⟩
      trivial trivial trivial
  refine exec_then (hb b7_in_code (by simp [b7]) hp) run_b7 hwf hm fun st hm1 hpc ↦ ?_
  have hfr1 : WFr m0 st.data :=
    frWin h hfr hm hm1 hwf rfl (r := 1) rfl (by omega) (by omega) (by decide)
  have hB1 := hI.base.after hm hm1 (by decide) (by decide) hfr1
  have hcp : CopyAt m0 st.data.dmem (2 * t + 2) := by
    intro j hj
    by_cases hjt : j < 2 * t
    · obtain ⟨a1, a2⟩ := slot_before h (j := j) (o := 16 + 32 * t) (by omega) (by omega)
      exact ew_keep hm1 hwf (r := 1) rfl (by decide) (hI.cp j hjt) a2 (.inl a1)
    · have hsrc : ∀ u < 2, NativeRustcVm.ewOf m.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (32 * t) +
          BitVec.ofNat 64 (16 * u)) = (rL m0).getD (2 * t + u) 0 := fun u hu ↦ by
        rw [addr_eq (z := 16 * (2 * t + u)) (by omega)]
        exact elem_r h hfr (by omega)
      by_cases hj0 : j = 2 * t
      · subst hj0
        have e := ew_copy hm1 (rd := 1) (rsrc := 0) rfl (o := 0) (by decide) rfl (o' := 0)
          (o8 := 8) rfl (by decide) (by decide)
        rw [addr_eq (z := 16 + 16 * (2 * t)) (by omega)] at e
        have := hsrc 0 (by decide)
        rw [Nat.mul_zero, Nat.add_zero] at this
        rwa [this] at e
      · have hj1 : j = 2 * t + 1 := by omega
        subst hj1
        have e := ew_copy hm1 (rd := 1) (rsrc := 0) rfl (o := 16) (by decide) rfl (o' := 16)
          (o8 := 24) rfl (by decide) (by decide)
        rw [addr_eq (z := 16 + 16 * (2 * t + 1)) (by omega)] at e
        rwa [hsrc 1 (by decide)] at e
  have hx10 : (st.data.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2) := by
    rw [Match.reg_eq hm hm1 rfl rfl]; exact hI.x10
  simp only [PcOk] at hpc
  sym_simp at hpc
  have hc := NativeRustcVmArm.Arrays.pc_ne hpc
  rw [Env.ofMachine_regs, hI.x13] at hc
  have h13 : (st.data.regs.getXReg .X13).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2 - 2 * (t + 1)) := by
    refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hI.x13]
    rw [sub_lit (by omega) (by omega)]
    congr 1
  by_cases hl : 2 * (t + 1) + 2 ≤ nR m0
  · have hpc' := hc.1 (fun e ↦ by
      have := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at this
      omega)
    refine at_pc hpc' ?_
    rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b7Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b7Offset) NativeRustcVmArm.Vm.RingWeight.label_7_at]
    refine hnext st.data ⟨hB1, hl, hx10, ?_, ?_, h13, by rw [show 2 * (t + 1) = 2 * t + 2 by omega]; exact hcp⟩
    · refine reg_bv hm1 rfl ?_
      show m0.regs.X1.toBitVec + BitVec.ofNat 64 (32 * t) + BitVec.ofInt 64 (48 : Nat) = _
      rw [ofInt_lit, addr_eq (z := 32 * (t + 1) + 16) (by omega)]
    · refine reg_bv hm1 rfl ?_
      show fb m0 + BitVec.ofNat 64 (16 + 32 * t) + BitVec.ofInt 64 (48 : Nat) = _
      rw [ofInt_lit, addr_eq (z := 32 * (t + 1) + 32) (by omega)]
  · have hpc' := hc.2 (by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      omega)
    refine at_pc hpc' ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b7Offset + b7.length = k + NativeRustcVmArm.Vm.RingWeight.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b7_next]]
    exact hdone st.data hB1 hx10 (by rw [show nR m0 / 2 * 2 = 2 * t + 2 by omega]; exact hcp)

end

end NativeRustcVmArm.Ring.Weight
