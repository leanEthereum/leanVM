module

public import NativeRustcVmArm.Whir.LanesOf.Rev

/-!
# `lanes_of` at level `0`, from `b5` to the returns

`b5`: `None` for `len ≥ 65`; `b6`: `Some(0)` for an empty row; `b7`: the tail alone for `len ≤ 3`,
else `b8` sets up the four-lane turns; `b10`: `Some(len)` when they covered the row, else the tail.
-/

namespace NativeRustcVmArm.Whir.LanesOf

open NativeRustcArm NativeRustcArm.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmArm.Vm.LanesOf

public section

/-- `b7`'s `(8 len - 8) >> 3`. -/
theorem b7_a (x : BitVec 64) (h1 : 1 ≤ x.toNat) (h : x.toNat < 65) :
    UnOp.apply (.ubfm 3 63) .W64 (UnOp.apply (.ubfm 61 60) .W64 x - BitVec.ofNat 64 8) =
      BitVec.ofNat 64 (x.toNat - 1) := by
  rw [lsl3, ofNat_sub_ofNat (by omega) (by omega), lsr3, toNat_ofNat_lt (by omega)]
  congr 1
  omega

/-- `b7`'s `(16 len - 16) >> 4`. -/
theorem b7_b (x : BitVec 64) (h1 : 1 ≤ x.toNat) (h : x.toNat < 65) :
    UnOp.apply (.ubfm 4 63) .W64 (UnOp.apply (.ubfm 60 59) .W64 x - BitVec.ofNat 64 16) =
      BitVec.ofNat 64 (x.toNat - 1) := by
  rw [lsl4, ofNat_sub_ofNat (by omega) (by omega), lsr4, toNat_ofNat_lt (by omega)]
  congr 1
  omega

variable [Host] {k : Nat}

section
variable (hp : Placed code k) {m0 : MachineData} (hpre : LanesOfPre m0)
  (h0 : m0.regs.X0.toNat = 0)
include hp hpre h0

/-- **From the tail** (`b11`) to the return. -/
theorem from_rv_tail {e : Nat} {st : MachineData} (hT : RvTail m0 e st) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b11Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_rev h0
  have hn64 : lenOf m0 ≤ 64 := by have := hT.hn; omega
  refine (rv_tail hp hT).bind fun s h ↦ goto h.2 ?_
  refine (run_loop (L := Rv1Loop m0) (lenOf m0) (fun _ _ h ↦ h.hi)
    (fun _ _ h ↦ rv1_step hp hpre h) h.1).bind fun s' h' ↦ goto h'.2 ?_
  exact ret14 hp h'.1 hsz hf hn64

/-- **From the four-lane turns** (`b9`) to the return. -/
theorem from_rv_loop {st : MachineData} (hL : RvLoop m0 0 st) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b9Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_rev h0
  refine (run_loop (L := RvLoop m0) (qOf m0) (fun _ _ h ↦ h.hj)
    (fun _ _ h ↦ rv_step hp hpre h) hL).bind fun s h ↦ goto h.2 ?_
  obtain ⟨hb, hx2, hx11, hx12, hx8, hx10, hx9, hn⟩ := h.1
  refine exec_then (inf hp b10_in_code (by simp [b10])) run_b10 (Env.wf_nil _) (match_nil _)
    fun s2 hm hpc ↦ ?_
  have hk := after_eq run_b10 ▸ b10_keeps
  have hb2 := hb.of_regsS hm hk.1 hk.2 rfl rfl rfl
  have kp : ∀ r ∈ [XReg.X2, .X8, .X9, .X10], s2.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact reg_kept hm rfl
  have hc : (SBool.cmp .eq .W64 (.reg .X11) (.reg .X12)).eval (Env.ofMachine s.data []) =
      decide (lenOf m0 = 4 * qOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, bv_beq_toNat]
    show decide (s.data.regs.X11.toNat = s.data.regs.X12.toNat) = _
    rw [hx11, hx12]
  by_cases hall : lenOf m0 = 4 * qOf m0
  · have hpc' := pc_taken hpc (by rw [hc]; simp [hall])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b19Offset) NativeRustcVmArm.Vm.LanesOf.label_19_at] at hpc'
    refine goto hpc' (ret19 hp (n := lenOf m0) (by rw [hall]; exact hb2) ?_ hsz hf (by omega))
    rw [show s2.data.regs.X2 = s.data.regs.X2 from kp .X2 (by simp)]
    exact hx2
  · have hpc' := pc_fall hpc (by rw [hc]; simp [hall])
    refine goto hpc' (from_rv_tail hp hpre h0 ⟨hb2, ?_, ?_, ?_, ?_, by unfold qOf at hall ⊢; omega,
      hn⟩)
    · rw [show s2.data.regs.X2 = s.data.regs.X2 from kp .X2 (by simp)]; exact hx2
    · rw [show s2.data.regs.X8 = s.data.regs.X8 from kp .X8 (by simp), hx8]
      congr 2
      omega
    · rw [show s2.data.regs.X10 = s.data.regs.X10 from kp .X10 (by simp)]; exact hx10
    · rw [show s2.data.regs.X9 = s.data.regs.X9 from kp .X9 (by simp)]; exact hx9

/-- **Level `0`**: from `b5`, the row reversed. -/
theorem rev {st : MachineData} (hb : Body m0 (revL m0) 0 st) (hx2 : st.regs.X2 = m0.regs.X2) :
    Eventually (step1 Host.exe) (Q m0) ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.LanesOf.b5Offset)⟩ := by
  obtain ⟨hsz, hf⟩ := lanes_rev h0
  have hl2 : (st.regs.getXReg .X2).toBitVec.toNat = lenOf m0 := by
    show st.regs.X2.toNat = _
    rw [hx2]; rfl
  -- `b5`
  refine exec_then (inf hp b5_in_code (by simp [b5])) run_b5 (Env.wf_nil _) (match_nil _)
    fun s1 hm1 hpc1 ↦ ?_
  have hk1 := after_eq run_b5 ▸ b5_keeps
  have hb1 := hb.of_regsS hm1 hk1.1 hk1.2 rfl rfl rfl
  have e1 : s1.data.regs.X2 = st.regs.X2 := reg_kept hm1 (r := .X2) rfl
  have hc1 : ((SBool.cmp .ult .W64 (.reg .X2) (.lit 65)).not.eval (Env.ofMachine st [])) =
      decide (65 ≤ lenOf m0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_ult_toNat, hl2, toNat_ofNat_lt (by decide)]
    by_cases h : 65 ≤ lenOf m0
    · simp [h]
    · simp [h]; omega
  by_cases hbig : 65 ≤ lenOf m0
  · have hpc' := pc_taken hpc1 (by rw [hc1]; simp [hbig])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b15Offset) NativeRustcVmArm.Vm.LanesOf.label_15_at] at hpc'
    exact goto hpc' (ret15 hp hb1.fr hb1.x30 (by rw [hsz]; omega))
  have hpc1' := pc_fall hpc1 (by rw [hc1]; simp [hbig])
  refine goto hpc1' ?_
  have hl1 : (s1.data.regs.getXReg .X2).toBitVec.toNat = lenOf m0 := by
    show s1.data.regs.X2.toNat = _
    rw [e1]; exact hl2
  -- `b6`
  refine exec_then (inf hp b6_in_code (by simp [b6])) run_b6 (Env.wf_nil _) (match_nil _)
    fun s2 hm2 hpc2 ↦ ?_
  have hk2 := after_eq run_b6 ▸ b6_keeps
  have hb2 := hb1.of_regsS hm2 hk2.1 hk2.2 rfl rfl rfl
  have e2 : s2.data.regs.X2 = s1.data.regs.X2 := reg_kept hm2 (r := .X2) rfl
  have hc2 : (SBool.cmp .eq .W64 (.reg .X2) (.lit 0)).eval (Env.ofMachine s1.data []) =
      decide (lenOf m0 = 0) := by
    sym_simp
    rw [Env.ofMachine_regs, bv_beq_toNat, hl1, toNat_ofNat_lt (by decide)]
  by_cases hz : lenOf m0 = 0
  · have hpc' := pc_taken hpc2 (by rw [hc2]; simp [hz])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b19Offset) NativeRustcVmArm.Vm.LanesOf.label_19_at] at hpc'
    refine goto hpc' (ret19 hp (n := lenOf m0) (by rw [hz]; exact hb2) ?_ hsz hf (by omega))
    rw [e2]; exact hl1
  have hpc2' := pc_fall hpc2 (by rw [hc2]; simp [hz])
  refine goto hpc2' ?_
  have hl2' : (s2.data.regs.getXReg .X2).toBitVec.toNat = lenOf m0 := by
    show s2.data.regs.X2.toNat = _
    rw [e2]; exact hl1
  -- `b7`
  refine exec_then (inf hp b7_in_code (by simp [b7])) run_b7 (Env.wf_nil _) (match_nil _)
    fun s3 hm3 hpc3 ↦ ?_
  have hk3 := after_eq run_b7 ▸ b7_keeps
  have hb3 := hb2.of_regsS hm3 hk3.1 hk3.2 rfl rfl rfl
  have ha := b7_a (s2.data.regs.getXReg .X2).toBitVec (by omega) (by omega)
  have hb' := b7_b (s2.data.regs.getXReg .X2).toBitVec (by omega) (by omega)
  rw [hl2'] at ha hb'
  have x2 : s3.data.regs.X2.toNat = lenOf m0 := by
    rw [show s3.data.regs.X2 = s2.data.regs.X2 from reg_kept hm3 (r := .X2) rfl]; exact hl2'
  have x8 : s3.data.regs.X8 = m0.regs.X3 := by
    have h := hm3.regs .X8 _ rfl
    exact (UInt64.toBitVec_inj.mp h).trans hb2.x3
  have x9 : s3.data.regs.X9.toBitVec = BitVec.ofNat 64 (16 * lenOf m0) := by
    have h : (s3.data.regs.getXReg .X9).toBitVec =
        UnOp.apply (.ubfm 60 59) .W64 (s2.data.regs.getXReg .X2).toBitVec := hm3.regs .X9 _ rfl
    rw [lsl4, hl2'] at h
    exact h
  have x13 : s3.data.regs.X13.toBitVec = BitVec.ofNat 64 (8 * lenOf m0) := by
    have h : (s3.data.regs.getXReg .X13).toBitVec =
        UnOp.apply (.ubfm 61 60) .W64 (s2.data.regs.getXReg .X2).toBitVec := hm3.regs .X13 _ rfl
    rw [lsl3, hl2'] at h
    exact h
  have x10 : s3.data.regs.X10.toBitVec = rowOf m0 + BitVec.ofNat 64 (8 * lenOf m0) := by
    have h : (s3.data.regs.getXReg .X10).toBitVec = BinOp.apply .add .W64
        (s2.data.regs.getXReg .X1).toBitVec
        (UnOp.apply (.ubfm 61 60) .W64 (s2.data.regs.getXReg .X2).toBitVec) := hm3.regs .X10 _ rfl
    rw [lsl3, hl2'] at h
    simp only [BinOp.apply, Sym.low_W64, Sym.ext_W64] at h
    show (s3.data.regs.getXReg .X10).toBitVec = _
    rw [h]
    show s2.data.regs.X1.toBitVec + _ = m0.regs.X1.toBitVec + _
    rw [hb2.x1]
  have x11 : s3.data.regs.X11.toBitVec = BitVec.ofNat 64 (lenOf m0 - 1) := by
    have h := hm3.regs .X11 _ rfl
    simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, Sym.low_W64, Sym.ext_W64,
      Env.ofMachine_regs] at h
    rw [ha, hb', ite_self] at h
    exact h
  have hc3 : (SBool.cmp .ult .W64 (.ite (SBool.cmp .ult .W64
      (.un (.ubfm 3 63) .W64 (.bin .sub .W64 (.un (.ubfm 61 60) .W64 (.reg .X2)) (.lit 8)))
      (.un (.ubfm 4 63) .W64 (.bin .sub .W64 (.un (.ubfm 60 59) .W64 (.reg .X2)) (.lit 16))))
      (.un (.ubfm 3 63) .W64 (.bin .sub .W64 (.un (.ubfm 61 60) .W64 (.reg .X2)) (.lit 8)))
      (.un (.ubfm 4 63) .W64 (.bin .sub .W64 (.un (.ubfm 60 59) .W64 (.reg .X2)) (.lit 16))))
      (.lit 3)).eval (Env.ofMachine s2.data []) = decide (lenOf m0 < 4) := by
    simp only [Sym.eval, SBool.eval, CmpOp.apply, BinOp.apply, Sym.low_W64, Sym.ext_W64,
      Env.ofMachine_regs]
    rw [ha, hb', ite_self, bv_ult_toNat, toNat_ofNat_lt (by omega), toNat_ofNat_lt (by decide)]
    by_cases h : lenOf m0 < 4
    · simp [h]; omega
    · simp [h]; omega
  by_cases hsmall : lenOf m0 < 4
  · have hpc' := pc_taken hpc3 (by rw [hc3]; simp [hsmall])
    rw [hp.label (j := NativeRustcVmArm.Vm.LanesOf.b11Offset) NativeRustcVmArm.Vm.LanesOf.label_11_at] at hpc'
    refine goto hpc' (from_rv_tail hp hpre h0 ⟨hb3, x2, ?_, ?_, ?_, by omega, by omega⟩)
    · rw [x8, show 16 * 0 = 0 from rfl, NativeRustcVm.addr_add_zero]; rfl
    · rw [x10]; rfl
    · show s3.data.regs.X9.toBitVec.toNat = _
      rw [x9, toNat_ofNat_lt (by omega)]
  have hpc3' := pc_fall hpc3 (by rw [hc3]; simp [hsmall])
  refine goto hpc3' ?_
  -- `b8`
  refine exec_then (inf hp b8_in_code (by simp [b8])) run_b8 (Env.wf_nil _) (match_nil _)
    fun s4 hm4 hpc4 ↦ ?_
  have hk4 := after_eq run_b8 ▸ b8_keeps
  have hb4 := hb3.of_regsS hm4 hk4.1 hk4.2 rfl rfl rfl
  have hL : (s3.data.regs.getXReg .X11).toBitVec + BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (lenOf m0) := by
    show s3.data.regs.X11.toBitVec + _ = _
    rw [x11, ← BitVec.ofNat_add, show lenOf m0 - 1 + 1 = lenOf m0 by omega]
  have hM : ((s3.data.regs.getXReg .X11).toBitVec + BitVec.ofNat 64 1 &&&
      BitVec.ofNat 64 2305843009213693948) = BitVec.ofNat 64 (4 * qOf m0) := by
    apply BitVec.eq_of_toNat_eq
    rw [hL, and_mask4 _ (by rw [toNat_ofNat_lt (by omega)]; omega), toNat_ofNat_lt (by omega),
      toNat_ofNat_lt (by unfold qOf; omega)]
    rfl
  refine goto hpc4 (from_rv_loop hp hpre h0 ⟨by simpa using hb4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by unfold qOf; omega, by omega⟩)
  · rw [show s4.data.regs.X2 = s3.data.regs.X2 from reg_kept hm4 (r := .X2) rfl]; exact x2
  · have h := hm4.regs .X11 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    rw [hL] at h
    exact toNat_of_eq h (toNat_ofNat_lt (by omega))
  · have h := hm4.regs .X12 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    rw [hM] at h
    exact toNat_of_eq h (toNat_ofNat_lt (by unfold qOf; omega))
  · have h := hm4.regs .X15 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    rw [hM] at h
    exact toNat_of_eq h (by rw [toNat_ofNat_lt (by unfold qOf; omega)]; omega)
  · have h := hm4.regs .X14 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    show (s4.data.regs.getXReg .X14).toBitVec = _
    rw [h]
    show s3.data.regs.X13.toBitVec + s3.data.regs.X1.toBitVec - _ = _
    rw [x13, show s3.data.regs.X1 = m0.regs.X1 from hb3.x1, BitVec.add_comm, sub_ofNat _ (by omega),
      show 8 * lenOf m0 - 16 = 8 * lenOf m0 - 16 - 32 * 0 by omega]
    rfl
  · have h := hm4.regs .X13 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    show (s4.data.regs.getXReg .X13).toBitVec = _
    rw [h]
    show s3.data.regs.X3.toBitVec + _ = m0.regs.X3.toBitVec + _
    rw [hb3.x3]
  · have h := hm4.regs .X8 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    show (s4.data.regs.getXReg .X8).toBitVec = _
    rw [h, hM, shl_apply, toNat_ofNat_lt (by unfold qOf; omega)]
    show s3.data.regs.X3.toBitVec + _ = m0.regs.X3.toBitVec + _
    rw [hb3.x3, show 2 ^ 4 * (4 * qOf m0) = 64 * qOf m0 by omega]
  · have h := hm4.regs .X10 _ rfl
    simp only [Sym.eval, BinOp.apply, Sym.low_W64, Sym.ext_W64, Env.ofMachine_regs] at h
    show (s4.data.regs.getXReg .X10).toBitVec = _
    rw [h, hM, shl_apply, toNat_ofNat_lt (by unfold qOf; omega)]
    show s3.data.regs.X10.toBitVec - _ = _
    rw [x10, sub_ofNat _ (by unfold qOf; omega),
      show 8 * lenOf m0 - 2 ^ 3 * (4 * qOf m0) = 8 * (lenOf m0 - 4 * qOf m0) by unfold qOf; omega]
  · rw [show s4.data.regs.X9 = s3.data.regs.X9 from reg_kept hm4 (r := .X9) rfl]
    show s3.data.regs.X9.toBitVec.toNat = _
    rw [x9, toNat_ofNat_lt (by omega)]

end

end

end NativeRustcVmArm.Whir.LanesOf
