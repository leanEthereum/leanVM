module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Ring.Weight.Zero

/-!
# `ring_weight`: the coefficients' loop, from `r` copied to the epilogue

`b11` clears the total, sets X22 past the last power and X24 to `min |r| |r'|`, and branches on
`|r'| = 0`: to `b21` (X24 cleared) and the loop of `Zero.lean`, or to `b12` and the loop of
`Outer.lean` (`stepLoops`).
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Ring
open NativeRustcVmArm.Vm.RingWeight
open NativeRustcVmArm.Arrays (regs_eq_of)

public section

variable {m0 : MachineData} [Host] {k : Nat}

/-- **From `r` copied to the epilogue** (`b11` to `b25`). -/
theorem stepLoops (hp : Placed code k) (h : RingWeightPre m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost) {m : MachineData}
    (hC : Copied m0 m) (hR : 0 < nR m0) :
    Eventually (step1 Host.exe) (fun st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b26Offset) ∧ Done m0 st.data)
      ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b11Offset)⟩ := by
  have hn := n36 h
  have hB := hC.base
  refine exec_then (hb b11_in_code (by simp [b11]) hp) run_b11 (Env.wf_nil m) (match_nil m)
    fun st1 hm1 hpc1 ↦ ?_
  have hfr1 := regs_fr hB.fr hm1 rfl rfl
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq (Env.wf_nil m) rfl
  have k1 := regs_eq_of (match_nil m) hm1 [.X3, .X4, .X20] (by decide)
  have h22 : (st1.data.regs.getXReg .X22).toBitVec = slotA m0 (nR m0) := by
    refine reg_bv hm1 rfl ?_
    simp only [Sym.eval, add_bv, Env.ofMachine_regs]
    rw [hB.x9, hB.x8, addr_eq (z := 16 + 16 * nR m0) (by omega)]
  have h21 : st1.data.regs.getXReg .X21 = 0 := reg_of hm1 rfl rfl
  have h23 : st1.data.regs.getXReg .X23 = 0 := reg_of hm1 rfl rfl
  have hpow : PowP m0 st1.data.dmem (A m0 0).2 := fun l hl ↦ by rw [hd1]; exact hC.cp l hl
  have htot : (⟨st1.data.regs.getXReg .X21, st1.data.regs.getXReg .X23⟩ : EW) = (A m0 0).1 := by
    rw [h21, h23]; rfl
  simp only [PcOk] at hpc1
  have hc := NativeRustcVmArm.Arrays.pc_cond hpc1
  have he : (SBool.cmp .eq .W64 (.reg .X4) (.lit 0)).eval (Env.ofMachine m []) = true ↔
      nQ m0 = 0 := by
    simp only [SBool.eval, CmpOp.apply, Sym.eval, Env.ofMachine_regs, Sym.low_W64, hB.x4]
    exact eq_lit (by decide)
  by_cases hQ : nQ m0 = 0
  · refine at_pc (hc.1 (he.mpr hQ)) ?_
    rw [show Labels.label NativeRustcVmArm.Vm.RingWeight.label_18 = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b21Offset) from hp.label (j := NativeRustcVmArm.Vm.RingWeight.b21Offset) NativeRustcVmArm.Vm.RingWeight.label_18_at]
    refine exec_then (hb b21_in_code (by simp [b21]) hp) run_b21 (Env.wf_nil _) (match_nil _)
      fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    refine at_pc hpc2 ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b21Offset + b21.length = k + NativeRustcVmArm.Vm.RingWeight.b22Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b21_next]]
    have k2 := regs_eq_of (match_nil _) hm2 [.X20, .X21, .X22, .X23] (by decide)
    have hZ : ZerI m0 0 st2.data := by
      refine ⟨regs_fr hfr1 hm2 rfl rfl, by decide, ?_, ?_, reg_bv hm2 rfl rfl, ?_, ?_⟩
      · rw [k2 .X20 (by simp), k1 .X20 (by simp)]; exact hB.x20
      · rw [k2 .X22 (by simp)]; exact h22
      · rw [k2 .X21 (by simp), k2 .X23 (by simp)]; exact htot
      · rw [hm2.dmem_eq (Env.wf_nil _) rfl]; exact hpow
    refine Sym.loop (I := fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b22Offset) ∧ ∃ j, n = 64 - j ∧
        ZerI m0 j st.data) (fun _ _ ⟨hpc', _, hn', hI⟩ ↦ at_pc hpc' ((zerTurn hp h hmul hI hQ hR).mono
          fun _ h' ↦ h'.elim (fun ⟨hp', j', hI', hlt⟩ ↦ .inr ⟨_, hn' ▸ hlt, hp', j', rfl, hI'⟩) .inl))
      ⟨rfl, 0, rfl, hZ⟩
  · refine at_pc (hc.2 (fun e ↦ hQ (he.mp e))) ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b11Offset + b11.length = k + NativeRustcVmArm.Vm.RingWeight.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b11_next]]
    refine exec_then (hb b12_in_code (by simp [b12]) hp) run_b12 (Env.wf_nil _) (match_nil _)
      fun st2 hm2 hpc2 ↦ ?_
    simp only [PcOk] at hpc2
    refine at_pc hpc2 ?_
    rw [show k + NativeRustcVmArm.Vm.RingWeight.b12Offset + b12.length = k + NativeRustcVmArm.Vm.RingWeight.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.RingWeight.b12_next]]
    have k2 := regs_eq_of (match_nil _) hm2 [.X20, .X21, .X22, .X23, .X24] (by decide)
    have h24 : (st1.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 (mn m0) := by
      refine reg_bv hm1 rfl ?_
      simp only [Sym.eval, SBool.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs, hB.x2, hB.x4]
      apply BitVec.eq_of_toNat_eq
      have hmn : mn m0 = min m0.regs.X2.toBitVec.toNat m0.regs.X4.toBitVec.toNat := rfl
      rw [NativeRustcVmArm.Arrays.min_toNat, BitVec.toNat_ofNat, hmn,
        Nat.mod_eq_of_lt (by have := m0.regs.X2.toBitVec.isLt; omega), Nat.min_comm]
    have hO : OutI m0 0 st2.data := by
      refine ⟨regs_fr hfr1 hm2 rfl rfl, by decide, ?_, ?_, ?_, ?_, reg_bv hm2 rfl rfl, ?_, ?_, ?_⟩
      · refine reg_bv hm2 rfl ?_
        simp only [Sym.eval, add_bv, Env.ofMachine_regs]
        rw [k1 .X3 (by simp), hB.x3]
      · rw [k2 .X20 (by simp), k1 .X20 (by simp)]; exact hB.x20
      · rw [k2 .X22 (by simp)]; exact h22
      · rw [k2 .X24 (by simp)]; exact h24
      · refine reg_bv hm2 rfl ?_
        simp only [Sym.eval, add_bv]
        show st1.data.regs.SP.toBitVec + _ = _
        rw [hfr1.sp]
      · rw [k2 .X21 (by simp), k2 .X23 (by simp)]; exact htot
      · rw [hm2.dmem_eq (Env.wf_nil _) rfl]; exact hpow
    refine Sym.loop (I := fun n st ↦ st.pc = Host.addrOf (k + NativeRustcVmArm.Vm.RingWeight.b13Offset) ∧ ∃ j, n = 64 - j ∧
        OutI m0 j st.data) (fun _ _ ⟨hpc', _, hn', hI⟩ ↦ at_pc hpc'
          ((outTurn hp h hmul hI (by omega) hR).mono fun _ h' ↦
            h'.elim (fun ⟨hp', j', hI', hlt⟩ ↦ .inr ⟨_, hn' ▸ hlt, hp', j', rfl, hI'⟩) .inl))
      ⟨rfl, 0, rfl, hO⟩

end

end NativeRustcVmArm.Ring.Weight
