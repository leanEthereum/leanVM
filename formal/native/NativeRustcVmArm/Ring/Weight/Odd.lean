module

public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Weight.Copy

/-!
# `ring_weight`: `r`'s last element, `r` copied

`b8` after the pairs: all copied when `|r|` is even, else the last element to copy (`OddI`), as
from `b5` when `|r| = 1`; `b9`, `b10` copy it. `stepCopy`: from `b1`'s branch with `|r| ≥ 1`
(`b5` or `b6`) to `b11` with `r` copied.
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **After the pairs** (`b8`): `r` copied when `|r|` is even, else its last element to copy. -/
theorem stepB8 (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hB : Base m0 m)
    (h10 : (m.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2))
    (hcp : CopyAt m0 m.dmem (nR m0 / 2 * 2)) {R : MachineState → Prop}
    (heven : ∀ m', Copied m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset)⟩)
    (hodd : ∀ m', OddI m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b9Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b8Offset)⟩ := by
  have hn := n36 h
  have hnn : nR m0 = m0.regs.X2.toBitVec.toNat := rfl
  refine exec_then (hb b8_in_code (by simp [b8]) hp) run_b8 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  have hB1 := hB.after (match_nil m) hm1 (by decide) (by decide) (regs_fr hB.fr hm1 rfl rfl)
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq (Env.wf_nil m) rfl
  have h10' : (st.data.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 (nR m0 / 2 * 2) := by
    rw [Match.reg_eq (match_nil m) hm1 rfl rfl]; exact h10
  simp only [PcOk] at hpc
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc
  have he : (SBool.cmp .eq .W64 (.reg .X2) (.reg .X10)).eval (Env.ofMachine m []) = true ↔
      nR m0 % 2 = 0 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64, hB.x2, h10]
    rw [eq_lit (by omega)]
    omega
  by_cases h2 : nR m0 % 2 = 0
  · refine at_pc (hc.1 (he.mpr h2)) ?_
    rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b11Offset) NativeRustcVmArm.Vm.RingWeight.label_11_at]
    exact heven st.data ⟨hB1, by rw [hd, show nR m0 = nR m0 / 2 * 2 by omega]; exact hcp⟩
  · refine at_pc (hc.2 (fun e ↦ h2 (he.mp e))) ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b8Offset + b8.length = k + NativeRustcVmArm.Vm.RingWeight.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b8_next]]
    exact hodd st.data ⟨hB1, by omega, by rw [h10']; congr 1; omega,
      by rw [hd, show nR m0 - 1 = nR m0 / 2 * 2 by omega]; exact hcp⟩

/-- **`|r| = 1`** (`b5`): the last element to copy. -/
theorem stepB5 (hp : Placed code k) {m : MachineData} (hB : Base m0 m) (h1 : nR m0 = 1)
    {R : MachineState → Prop}
    (cont : ∀ m', OddI m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b9Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b5Offset)⟩ := by
  refine exec_then (hb b5_in_code (by simp [b5]) hp) run_b5 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc ?_
  rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_9 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b9Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b9Offset) NativeRustcVmArm.Vm.RingWeight.label_9_at]
  refine cont st.data ⟨hB.after (match_nil m) hm1 (by decide) (by decide)
    (regs_fr hB.fr hm1 rfl rfl), by omega, ?_, fun j hj ↦ absurd hj (by omega)⟩
  refine reg_bv hm1 rfl ?_
  rw [h1]
  rfl

/-- **The last element copied** (`b9`, `b10`). -/
theorem stepOdd (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hO : OddI m0 m)
    {R : MachineState → Prop}
    (cont : ∀ m', Copied m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b9Offset)⟩ := by
  have hn := n36 h
  have hnn : nR m0 = m0.regs.X2.toBitVec.toNat := rfl
  have hnn' : nR m0 = m0.regs.X2.toNat := rfl
  have hodd := hO.odd
  have hB := hO.base
  refine exec_then (hb b9_in_code (by simp [b9]) hp) run_b9 (Env.wf_nil m) (match_nil m)
    fun st hm1 hpc ↦ ?_
  simp only [PcOk] at hpc
  refine at_pc hpc ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b9Offset + b9.length = k + NativeRustcVmArm.Vm.RingWeight.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b9_next]]
  have hB1 := hB.after (match_nil m) hm1 (by decide) (by decide) (regs_fr hB.fr hm1 rfl rfl)
  have hd : st.data.dmem = m.dmem := hm1.dmem_eq (Env.wf_nil m) rfl
  have ho := orr8 (m.regs.getXReg .X10).toBitVec
    (by rw [hO.x10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
  rw [hO.x10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ho
  have h10 : (st.data.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 1 := by
    refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hB.x2, hO.x10]
    rw [show m0.regs.X2.toBitVec = BitVec.ofNat 64 (nR m0) by
        apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← hnn, Nat.mod_eq_of_lt (by omega)],
      sub_lit (by omega) (by omega)]
    congr 1
    omega
  have h11 : (st.data.regs.getXReg .X11).toBitVec =
      m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (nR m0 - 1)) + BitVec.ofInt 64 (8 : Nat) := by
    refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs, hB.x1]
    rw [hO.x10, ho, add_bv, ofInt_lit, addr_eq rfl]
  have h12 : (st.data.regs.getXReg .X12).toBitVec =
      fb m0 + BitVec.ofNat 64 (16 + 16 * (nR m0 - 1)) + BitVec.ofInt 64 (8 : Nat) := by
    refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [hO.x10, ho, add_bv, hB.x9, ofInt_lit, addr_eq (z := 16 + 16 * (nR m0 - 1) + 8) (by omega),
      addr_eq (z := 16 + 16 * (nR m0 - 1) + 8) (by omega)]
  -- b10
  have hfr := hB1.fr
  have hr := h.2.2.1
  let rs : List (BitVec 64 × Nat) :=
    [(m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * (nR m0 - 1)), 16),
      (fb m0 + BitVec.ofNat 64 (16 + 16 * (nR m0 - 1)), 16)]
  have hwf : (Env.ofMachine st.data rs).WF :=
    win_wf2 (arg_win hfr hr.1 (by omega) (by decide)) (frame_win h hfr (by omega) (by decide))
      (win_apart h hr.2 hr.1.2 (by omega) (by decide) (by omega))
  have hm : Match (Env.ofMachine st.data rs) lastS st.data :=
    match_ofMachine ⟨rfl, nofun, rfl, nofun, trivial⟩ rfl ⟨h11, h12, trivial⟩ trivial trivial trivial
  refine exec_then (hb b10_in_code (by simp [b10]) hp) run_b10 hwf hm fun st2 hm2 hpc2 ↦ ?_
  have hfr2 : WFr m0 st2.data :=
    frWin h hfr hm hm2 hwf rfl (r := 1) rfl (by omega) (by omega) (by decide)
  have hB2 := hB1.after hm hm2 (by decide) (by decide) hfr2
  simp only [PcOk] at hpc2
  sym_simp at hpc2
  have hc := NativeRustcVmArm.Arrays.pc_ne hpc2
  rw [Env.ofMachine_regs, h10] at hc
  refine at_pc (hc.2 rfl) ?_
  rw [show k + NativeRustcVmArm.Vm.RingWeight.b10Offset + b10.length = k + NativeRustcVmArm.Vm.RingWeight.b11Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b10_next]]
  refine cont st2.data ⟨hB2, fun j hj ↦ ?_⟩
  by_cases hjl : j < nR m0 - 1
  · obtain ⟨a1, a2⟩ := slot_before h (j := j) (o := 16 + 16 * (nR m0 - 1)) (by omega) (by omega)
    exact ew_keep hm2 hwf (r := 1) rfl (by decide) (by rw [hd]; exact hO.cp j hjl) a2 (.inl a1)
  · have hj : j = nR m0 - 1 := by omega
    subst hj
    have e := ew_copy hm2 (rd := 1) (rsrc := 0) rfl (o := 0) (by decide) rfl (o' := 0)
      (o8 := 8) rfl (by decide) (by decide)
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.addr_add_zero, hd,
      elem_r h hB.fr (by omega)] at e
    exact e

/-- **`r` copied** (`|r| ≥ 1`): from `b5` (`|r| = 1`) or `b6` to `b11`. -/
theorem stepCopy (hp : Placed code k) (h : RingWeightPre m0) {m : MachineData} (hB : Base m0 m)
    (h1 : 1 ≤ nR m0) {R : MachineState → Prop}
    (cont : ∀ m', Copied m0 m' → Eventually (step1 Host.exe) R ⟨m', Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + if nR m0 = 1 then NativeRustcVmArm.Vm.RingWeight.b5Offset else NativeRustcVmArm.Vm.RingWeight.b6Offset)⟩ := by
  by_cases hn1 : nR m0 = 1
  · rw [ite_eq_left hn1]
    exact stepB5 hp hB hn1 fun m' hO ↦ stepOdd hp h hO cont
  · rw [ite_eq_right hn1]
    refine stepB6 hp h hB (by omega) fun m1 hI ↦ ?_
    refine Sym.loop (I := fun n st ↦ ∃ t, n = nR m0 - 2 * t ∧ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b7Offset) ∧
      CopyI m0 t st.data) (fun n st ⟨t, hn, hpc, hI⟩ ↦ ?_) ⟨0, rfl, rfl, hI⟩
    refine at_pc hpc (stepB7 hp h hI (fun m' hI' ↦ .done _ (.inr ⟨nR m0 - 2 * (t + 1),
      by have := hI.lt; omega, t + 1, rfl, rfl, hI'⟩)) fun m' hB' h10 hcp ↦ ?_)
    exact (stepB8 hp h hB' h10 hcp cont fun m'' hO ↦ stepOdd hp h hO cont).mono fun _ h ↦ .inl h

end

end NativeRustcVmArm.Ring.Weight
