module

public import NativeRustcVmArm.Whir.LanesOf.Pairs

/-!
# `lanes_of` at a later level, from `b1` to the returns

`b1`: `None` for `len ≥ 130`; `b2`: `Some(0)` for `n = 0`; `b3`, `b4`: one lane, the tail from
lane `0`; `b16` the two-lane turns' head; `b18`: `Some(n)` for an even `n`, else the tail.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

public section

variable [Host] {k : Nat}

section
variable (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
  (h0 : m0.regs.X0.toNat ≠ 0)
include hp hpre h0

/-- **From the tail** (`b20`) to the return. -/
theorem from_tail {e : Nat} {st : MachineData} (hT : CpTail m0 e st) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b20Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_pair h0
  have hn64 : nOf m0 ≤ 64 := by have := hT.hn; unfold nOf; omega
  refine (cp_tail hp hT).bind fun s h ↦ goto h.2 ?_
  refine (run_loop (L := Cp1Loop m0) (nOf m0) (fun _ _ h ↦ h.hi)
    (fun _ _ h ↦ cp1_step hp hpre h) h.1).bind fun s' h' ↦ goto h'.2 ?_
  exact ret14 hp h'.1 hsz hf hn64

/-- **From the two-lane turns** (`b17`) to the return. -/
theorem from_loop {st : MachineData} (hL : CpLoop m0 0 st) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b17Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_pair h0
  have hn64 : nOf m0 ≤ 64 := by have := hL.hn; unfold nOf; omega
  refine (run_loop (L := CpLoop m0) (nOf m0 / 2) (fun _ _ h ↦ h.hj)
    (fun _ _ h ↦ cp_step hp hpre h) hL).bind fun s h ↦ goto h.2 ?_
  obtain ⟨hb, hx2, hx8, hn⟩ := h.1
  refine exec_then (inf hp b18_in_code (by simp [b18])) run_b18 (Env.wf_nil _) (match_nil _)
    fun s2 hm hpc ↦ ?_
  have hk := after_eq run_b18 ▸ b18_keeps
  have hb2 := hb.of_regsS hm hk.1 hk.2 rfl rfl rfl
  have e2 : s2.data.regs.X2 = s.data.regs.X2 := reg_kept hm (r := .X2) rfl
  have e8 : s2.data.regs.X8 = s.data.regs.X8 := reg_kept hm (r := .X8) rfl
  have hc : ((SBool.cmp .eq .W64 (.reg .X2) (.reg .X8)).not.eval (Env.ofMachine s.data [])) =
      decide (nOf m0 % 2 = 1) := by
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, bv_beq_toNat]
    show (!decide (s.data.regs.X2.toNat = s.data.regs.X8.toNat)) = _
    rw [hx2, hx8]
    by_cases h : nOf m0 % 2 = 1 <;> simp [h] <;> omega
  by_cases hodd : nOf m0 % 2 = 1
  · have hpc' := pc_taken hpc (by rw [hc]; simp [hodd])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b20Offset) NativeRustcVmArm.Vm.LanesOf.label_20_at] at hpc'
    exact goto hpc' (from_tail hp hpre h0 ⟨hb2, by rw [e2]; exact hx2, by rw [e8]; exact hx8,
      by omega, hn⟩)
  · have hpc' := pc_fall hpc (by rw [hc]; simp [hodd])
    refine goto hpc' (ret19 hp (n := nOf m0) ?_ (by rw [e2]; exact hx2) hsz hf hn64)
    rw [show nOf m0 = 2 * (nOf m0 / 2) by omega]
    exact hb2

/-- **A later level**: from `b1`, the row's pairs. -/
theorem pairs {st : MachineData} (hb : Body m0 (pairL m0) 0 st) (hx2 : st.regs.X2 = m0.regs.X2) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b1Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_pair h0
  have hl2 : (st.regs.getXReg .X2).toBitVec.toNat = lenOf m0 := by
    show st.regs.X2.toNat = _
    rw [hx2]; rfl
  -- `b1`
  refine exec_then (inf hp b1_in_code (by simp [b1])) run_b1 (Env.wf_nil _) (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hk1 := after_eq run_b1 ▸ b1_keeps
  have hb1 := hb.of_regsS hm1 hk1.1 hk1.2 rfl rfl rfl
  have e1 : s1.data.regs.X2 = st.regs.X2 := reg_kept hm1 (r := .X2) rfl
  have hc1 : ((SBool.cmp .ult .W64 (.reg .X2) (.lit 130)).not.eval (Env.ofMachine st [])) =
      decide (130 ≤ lenOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_ult_toNat, hl2, toNat_ofNat_lt (by decide)]
    by_cases h : 130 ≤ lenOf m0
    · simp [h]
    · simp [h]; omega
  by_cases hbig : 130 ≤ lenOf m0
  · have hpc' := pc_taken hpc1 (by rw [hc1]; simp [hbig])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b15Offset) NativeRustcVmArm.Vm.LanesOf.label_15_at] at hpc'
    exact goto hpc' (ret15 hp hb1.fr hb1.x30 (by rw [hsz]; unfold nOf; omega))
  have hpc1' := pc_fall hpc1 (by rw [hc1]; simp [hbig])
  refine goto hpc1' ?_
  -- `b2`
  refine exec_then (inf hp b2_in_code (by simp [b2])) run_b2 (Env.wf_nil _) (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  have hk2 := after_eq run_b2 ▸ b2_keeps
  have hb2 := hb1.of_regsS hm2 hk2.1 hk2.2 rfl rfl rfl
  have hl2' : (s1.data.regs.getXReg .X2).toBitVec.toNat = lenOf m0 := by
    show s1.data.regs.X2.toNat = _
    rw [e1]; exact hl2
  have x2 : s2.data.regs.X2.toNat = nOf m0 := by
    have h : (s2.data.regs.getXReg .X2).toBitVec =
        UnOp.apply (.ubfm 1 63) .W64 (s1.data.regs.getXReg .X2).toBitVec := hm2.regs .X2 _ rfl
    rw [lsr1, hl2'] at h
    refine toNat_of_eq h (toNat_ofNat_lt ?_)
    omega
  have hc2 : (SBool.cmp .eq .W64 (.un (.ubfm 1 63) .W64 (.reg .X2)) (.lit 0)).eval
      (Env.ofMachine s1.data []) = decide (nOf m0 = 0) := by
    simp only [SBool.eval, Sym.eval, CmpOp.apply, Sym.low_W64, Env.ofMachine_regs]
    rw [lsr1, bv_beq_toNat, hl2', toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)]
    rfl
  by_cases hz : nOf m0 = 0
  · have hpc' := pc_taken hpc2 (by rw [hc2]; simp [hz])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b19Offset) NativeRustcVmArm.Vm.LanesOf.label_19_at] at hpc'
    exact goto hpc' (ret19 hp (n := nOf m0) (by rw [hz]; exact hb2) x2 hsz hf (by omega))
  have hpc2' := pc_fall hpc2 (by rw [hc2]; simp [hz])
  refine goto hpc2' ?_
  -- `b3`
  refine exec_then (inf hp b3_in_code (by simp [b3])) run_b3 (Env.wf_nil _) (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  have hk3 := after_eq run_b3 ▸ b3_keeps
  have hb3 := hb2.of_regsS hm3 hk3.1 hk3.2 rfl rfl rfl
  have e3 : s3.data.regs.X2 = s2.data.regs.X2 := reg_kept hm3 (r := .X2) rfl
  have hc3 : ((SBool.cmp .eq .W64 (.reg .X2) (.lit 1)).not.eval (Env.ofMachine s2.data [])) =
      decide (nOf m0 ≠ 1) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat, toNat_ofNat_lt (by decide)]
    show (!decide (s2.data.regs.X2.toNat = 1)) = _
    rw [x2]
    by_cases h : nOf m0 = 1 <;> simp [h]
  have hn130 : lenOf m0 < 130 := by omega
  by_cases h1 : nOf m0 = 1
  · -- one lane: `b4`, the tail from lane `0`
    have hpc' := pc_fall hpc3 (by rw [hc3]; simp [h1])
    refine goto hpc' ?_
    refine exec_then (inf hp b4_in_code (by simp [b4])) run_b4 (Env.wf_nil _) (match_nil _)
      fun s4 hm4 hpc4 ↦ ?_
    have hk4 := after_eq run_b4 ▸ b4_keeps
    have hb4 := hb3.of_regsS hm4 hk4.1 hk4.2 rfl rfl rfl
    simp only [PcOk] at hpc4
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b20Offset) NativeRustcVmArm.Vm.LanesOf.label_20_at] at hpc4
    refine goto hpc4 (from_tail hp hpre h0 ⟨hb4, ?_, ?_, by omega, hn130⟩)
    · rw [show s4.data.regs.X2 = s3.data.regs.X2 from reg_kept hm4 (r := .X2) rfl, e3]
      exact x2
    · have h := hm4.regs .X8 _ rfl
      exact toNat_of_eq h (toNat_ofNat_lt (by decide))
  · -- `b16`: the two-lane turns
    have hpc' := pc_taken hpc3 (by rw [hc3]; simp [h1])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b16Offset) NativeRustcVmArm.Vm.LanesOf.label_16_at] at hpc'
    refine goto hpc' ?_
    refine exec_then (inf hp b16_in_code (by simp [b16])) run_b16 (Env.wf_nil _) (match_nil _)
      fun s4 hm4 hpc4 ↦ ?_
    have hk4 := after_eq run_b16 ▸ b16_keeps
    have hb4 := hb3.of_regsS hm4 hk4.1 hk4.2 rfl rfl rfl
    simp only [PcOk] at hpc4
    have hl3 : (s3.data.regs.getXReg .X2).toBitVec.toNat = nOf m0 := by
      show s3.data.regs.X2.toNat = _
      rw [e3]; exact x2
    have hand : ((s3.data.regs.getXReg .X2).toBitVec &&& BitVec.ofNat 64 126).toNat =
        2 * (nOf m0 / 2) := by
      rw [and_mask2 _ (by rw [hl3]; unfold nOf; omega), hl3]
    refine goto hpc4 (from_loop hp hpre h0 ⟨by simpa using hb4, ?_, ?_, ?_, ?_, ?_, by
      unfold nOf at hz h1 ⊢; omega, hn130⟩)
    · rw [show s4.data.regs.X2 = s3.data.regs.X2 from reg_kept hm4 (r := .X2) rfl, e3]
      exact x2
    · have h := hm4.regs .X8 _ rfl
      sym_simp at h
      rw [Env.ofMachine_regs] at h
      exact toNat_of_eq h hand
    · have h := hm4.regs .X11 _ rfl
      sym_simp at h
      rw [Env.ofMachine_regs] at h
      exact toNat_of_eq h (by rw [hand]; omega)
    · have h := hm4.regs .X9 _ rfl
      sym_simp at h
      show (s4.data.regs.getXReg .X9).toBitVec = _
      rw [h, Env.ofMachine_regs]
      show s3.data.regs.X3.toBitVec + _ = m0.regs.X3.toBitVec + _
      rw [hb3.x3]
    · have h := hm4.regs .X10 _ rfl
      sym_simp at h
      show (s4.data.regs.getXReg .X10).toBitVec = _
      rw [h, Env.ofMachine_regs]
      show s3.data.regs.X1.toBitVec + _ = m0.regs.X1.toBitVec + _
      rw [hb3.x1]

end

end

end NativeRustcVmArm.Whir.LanesOf
