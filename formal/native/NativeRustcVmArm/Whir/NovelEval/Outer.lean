module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.NovelEval.Inner

/-!
# `novel_eval`'s doubling loop

A turn (`outer_step`) from the head `b4` after `j` values (`OInv`): with no value left it goes to
`b9` (`Mid`); else `b5` loads value `j` and starts the inner loop (`inner_step`, by `Sym.loop`),
which writes the products after the basis; `b8` doubles the size and moves to the next value, back
to `b4` while the basis is shorter than the coefficients, else to `b9` (the model's later steps
keep the basis, `novelPre_stable`).
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm

public section

/-- `lsl x, x, #1`. -/
theorem lsl1_toNat (x : BitVec 64) :
    (evalUBFM (w := RegWidth.W64) x 63 62).toNat = x.toNat * 2 % 2 ^ 64 := by
  have := x.isLt
  simp [evalUBFM, RegWidth.bits, BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftLeft_eq]
  omega

/-- The `What`s' end is apart from every value before it. -/
theorem what_ne {m0 : MachineData} (hpre : NovelEvalPre m0) {j : Nat} (hj : j < wn m0) :
    (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)).toNat ≠
      (m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0)).toNat := by
  obtain ⟨hS, -, ⟨⟨-, hnw⟩, hoff⟩, -⟩ := hpre
  have hsp : novelEvalStack ≤ m0.regs.SP.toNat := hS.2.1
  have hst : (stackBelow m0 novelEvalStack).toNat = m0.regs.SP.toBitVec.toNat - novelEvalStack :=
    toNat_sub_ofNat hsp
  unfold OffStack Apart at hoff
  unfold NoWrap at hnw
  have h1 := m0.regs.SP.toBitVec.isLt
  have hw : wn m0 = m0.regs.X4.toNat := rfl
  have he : novelEvalStack = 1232 := rfl
  rw [hst, he] at hoff
  have hsp' : 1232 ≤ m0.regs.SP.toBitVec.toNat := hsp
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [← hw] at hnw hoff
  omega

variable [Host] {k : Nat}

/-- **A turn of the doubling loop.** -/
theorem outer_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {j : Nat}
    {st : MachineData} (hI : OInv m0 j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Mid m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset)) ∨
        (OInv m0 (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b4Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b4Offset)⟩ := by
  have hS : StackOk m0 novelEvalStack := hpre.1
  have hwin := hpre.2.2.1
  have hfr := hI.fr
  have hl7 : Labels.label NativeRustcVmArm.Vm.NovelEval.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset) := hp.label (j := NativeRustcVmArm.Vm.NovelEval.b9Offset) NativeRustcVmArm.Vm.NovelEval.label_7_at
  have hl3 : Labels.label NativeRustcVmArm.Vm.NovelEval.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b4Offset) := hp.label (j := NativeRustcVmArm.Vm.NovelEval.b4Offset) NativeRustcVmArm.Vm.NovelEval.label_3_at
  -- `b4`: any value left?
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk4 run_b4 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb4 := after_eq run_b4 ▸ regs_keeps b4 (.tail _ (.tail _ (.head _)))
  have hfr1 := hfr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb4.1 hb4.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb4.2
  have e1 : ∀ r, s1.data.regs.getXReg r = st.regs.getXReg r := fun r ↦
    Match.reg_eq (match_nil _) hm1 (r := r) (v := .reg r) (by cases r <;> rfl)
      (by cases r <;> rfl)
  have rg1 : Regs m0 s1.data :=
    ⟨(e1 .X19).trans hI.rg.x19, (e1 .X20).trans hI.rg.x20, (e1 .X21).trans hI.rg.x21⟩
  simp only [PcOk] at hpc1
  sym_simp at hpc1
  simp only [Env.ofMachine_regs, bv_beq_toNat] at hpc1
  have h22 : (st.regs.getXReg .X22).toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j) :=
    hI.x22
  have h25 : (st.regs.getXReg .X25).toBitVec =
      m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0) := hI.x25
  rw [h22, h25] at hpc1
  by_cases hjw : j = wn m0
  · -- no value left: the basis is complete
    subst hjw
    simp only [decide_true, ↓reduceIte, hl7] at hpc1
    refine .done _ (.inl ⟨⟨hfr1, rg1, ?_, hd1 ▸ hI.basis⟩, hpc1⟩)
    show (s1.data.regs.getXReg .X24).toBitVec.toNat = _
    rw [e1]
    exact hI.x24
  have hj : j < wn m0 := by have := hI.hj; omega
  simp only [what_ne hpre hj, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b5`: load value `j`
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b5Offset) := hpc1
  let a5 := m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j)
  have hrd : Readable s1.data a5 8 := hfr1.readable (Readable.sub hwin.1 (by
    have : wn m0 = m0.regs.X4.toNat := rfl
    omega))
  let env5 := Env.ofMachine s1.data [(a5, 8)]
  have hwf5 : env5.WF := wf_one hrd.1 hrd.2
  have hm5 : Match env5 ldS s1.data := match_one <| by
    rw [e1]
    simp [h22, a5]
  refine exec_at hk5 run_b5 hwf5 hpc1' hm5 fun s2 hm2 hpc2 ↦ ?_
  have hb5 := after_eq run_b5 ▸ b5_keeps
  have hfr2 := hfr1.of_regs hm5 hm2 hwf5 rfl hb5.1 hb5.2
  have hd2 : s2.data.dmem = st.dmem := (hm2.dmem_eq hwf5 hb5.2).trans hd1
  have e2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X24, .X25], s2.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    exact (Match.reg_eq hm5 hm2 rfl rfl).trans (e1 _)
  have hargs := hI.fr.get?_arg hS hwin (fun r hr ↦ absurd hr List.not_mem_nil)
  have hv : s2.data.regs.X23 = (whatOf m0).getD j 0 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm2.regs .X23 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [load8_eq, whatOf_getD m0 hj]
    show _ = (NativeRustcVm.wordOf m0.dmem a5).toBitVec
    rw [show env5.base 0 = a5 from rfl, NativeRustcVm.addr_add_zero]
    refine congrArg UInt64.toBitVec (NativeRustcVm.wordOf_congr fun i hi ↦ ?_)
    show s1.data.dmem.get? _ = _
    rw [hd1, addr_add]
    exact hargs _ (by have : wn m0 = m0.regs.X4.toNat := rfl; omega)
  have hsz := novelPre_size_pos (whatOf m0) (cnt m0) j
  have hI0 : IInv m0 j 0 s2.data := by
    refine ⟨hfr2, ⟨(e2 .X19 (by simp)).trans hI.rg.x19, (e2 .X20 (by simp)).trans hI.rg.x20,
      (e2 .X21 (by simp)).trans hI.rg.x21⟩, hj, hI.lt, ?_, ?_, ?_, hv, ?_, ?_, hd2 ▸ hI.basis, ?_⟩
    · refine (hm2.regs .X22 _ rfl).trans ?_
      simp [Sym.eval, env5, a5]
    · rw [show s2.data.regs.X25 = st.regs.X25 from e2 .X25 (by simp)]; exact hI.x25
    · rw [show s2.data.regs.X24 = st.regs.X24 from e2 .X24 (by simp)]; exact hI.x24
    · refine (hm2.regs .X26 _ rfl).trans ?_
      simp only [Sym.eval]
      rw [show env5.sp = s1.data.regs.SP.toBitVec from rfl, hfr1.sp]
      simp [fbOf]
    · show (s2.data.regs.getXReg .X27).toBitVec.toNat = _
      rw [hm2.regs .X27 _ rfl]
      show (s1.data.regs.getXReg .X24).toBitVec.toNat = _
      rw [e1]
      exact hI.x24
    · simp only [List.take_zero, List.map_nil]
      exact NativeRustcVm.wordsAt_nil _ _
  -- the inner loop
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Post8 m0 j s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b8Offset))
    (fun n s ↦ ∃ t, n = (basisOf m0 j).size - t ∧ t < (basisOf m0 j).size ∧
      s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b6Offset) ∧ IInv m0 j t s.data)
    (fun n s ⟨t, hn', ht, hpc, hI'⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (inner_step hp hkmul hS hc ht hI').mono fun s' h ↦ ?_
      rcases h with h | ⟨hI'', hpc', hlt⟩
      · exact .inl h
      · exact .inr ⟨(basisOf m0 j).size - (t + 1), by omega, t + 1, rfl, hlt, hpc', hI''⟩)
    (n := (basisOf m0 j).size) ⟨0, by omega, by unfold basisOf; omega, hpc2, hI0⟩
  refine hloop.bind fun s ⟨hP, hpc⟩ ↦ ?_
  -- `b8`: double, next value
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk8 run_b8 (Env.wf_nil _) hpc (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb8 := after_eq run_b8 ▸ regs_keeps b8 (.tail _ (.tail _ (.tail _ (.head _))))
  have hfr3 := hP.fr.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb8.1 hb8.2
  have hd3 : s3.data.dmem = s.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb8.2
  have e3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X25], s3.data.regs.getXReg r = s.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm3 rfl rfl
  have rg3 : Regs m0 s3.data :=
    ⟨(e3 .X19 (by simp)).trans hP.rg.x19, (e3 .X20 (by simp)).trans hP.rg.x20,
      (e3 .X21 (by simp)).trans hP.rg.x21⟩
  have h32 := basis_le_32 m0 j hc hI.lt
  have hsucc := basisOf_succ m0 hj hI.lt
  have hsz1 : (basisOf m0 (j + 1)).size = 2 * (basisOf m0 j).size := by
    rw [hsucc, Array.size_append, Array.size_map]; omega
  have h24 : (s3.data.regs.getXReg .X24).toBitVec.toNat = (basisOf m0 (j + 1)).size := by
    rw [hm3.regs .X24 _ rfl]
    sym_simp
    rw [lsl1_toNat, Env.ofMachine_regs, hsz1]
    show s.data.regs.X24.toNat * 2 % 2 ^ 64 = _
    rw [hP.x24]
    omega
  have h21 : (s.data.regs.getXReg .X21).toBitVec.toNat = cnt m0 := by
    show s.data.regs.X21.toNat = _
    rw [hP.rg.x21]; rfl
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [Env.ofMachine_regs, bv_beq_toNat, bv_ult_toNat] at hpc3
  rw [show (evalUBFM (s.data.regs.getXReg .X24).toBitVec 63 62).toNat =
      (basisOf m0 (j + 1)).size by
    rw [lsl1_toNat, hsz1]
    show s.data.regs.X24.toNat * 2 % 2 ^ 64 = _
    rw [hP.x24]
    omega, h21] at hpc3
  have x24' : s3.data.regs.X24.toNat = (basisOf m0 (j + 1)).size := h24
  by_cases hmore : (basisOf m0 (j + 1)).size < cnt m0
  · -- the basis still too short: the next value
    simp only [show ¬cnt m0 < (basisOf m0 (j + 1)).size by omega,
      show ¬cnt m0 = (basisOf m0 (j + 1)).size by omega, decide_false, Bool.not_false,
      Bool.and_self, ↓reduceIte, hl3] at hpc3
    refine .done _ (.inr ⟨⟨hfr3, rg3, by omega, hmore, ?_, ?_, x24', hd3 ▸ hP.basis⟩, hpc3⟩)
    · refine (hm3.regs .X22 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs]
      show s.data.regs.X22.toBitVec + _ = _
      rw [hP.x22, addr_add]
      rfl
    · rw [show s3.data.regs.X25 = s.data.regs.X25 from e3 .X25 (by simp)]; exact hP.x25
  · -- long enough: the basis is complete
    have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset) := by
      rw [hpc3]
      by_cases heq : cnt m0 = (basisOf m0 (j + 1)).size
      · simp [heq]; rfl
      · simp [show cnt m0 < (basisOf m0 (j + 1)).size by omega]; rfl
    have hst := novelPre_stable (whatOf m0) (count := cnt m0) (j := j + 1) (by unfold basisOf at hmore; omega)
      (wn m0) (by omega)
    have hst' : basisOf m0 (wn m0) = basisOf m0 (j + 1) := hst
    refine .done _ (.inl ⟨⟨hfr3, rg3, by rw [hst']; exact x24', ?_⟩, hpc3'⟩)
    rw [hst', hd3]
    exact hP.basis

end

end NativeRustcVmArm.Whir.NovelEval
