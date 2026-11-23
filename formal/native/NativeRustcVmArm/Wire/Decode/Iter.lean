module

public import NativeRustcVmArm.Code.Vm.PhaseM.Names
public import NativeRustcVmArm.Wire.Decode.Loop

/-!
# `decode`'s loop over the phases

One pass (`iter_spec`): no phase left (`done_spec`), or a slot (`b10`), `phase_m`'s call (`b11`,
its precondition `phaseM_pre`), its outcome (`b12`): the next phase (`LInv` one further) or
`None` (`b13`). The whole loop (`loop_spec`).
-/

namespace NativeRustcVmArm.Wire.Decode

open NativeRustcArm NativeRustcArm.Sym NativeRustcVm.Wire NativeVm NativeVm.Wire
open NativeVm.Model
open NativeRustcVmArm.Ring (Fr base)
open NativeRustcVm (WordAt WordsAt InAny Region)
open NativeRustcVm.Transcript (DecArea DecodedAt PhaseAt)
open NativeRustcVmArm.Vm.Decode
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

public section

variable {m0 : MachineData} {B : List UInt8} {n : Nat} {ws : List K} {p cs : Nat}

theorem disj6 {a1 a2 a3 a4 a5 a6 : BitVec 64} {n1 n2 n3 n4 n5 n6 : Nat}
    (h12 : NativeRustcVm.Apart a1 n1 a2 n2) (h13 : NativeRustcVm.Apart a1 n1 a3 n3)
    (h14 : NativeRustcVm.Apart a1 n1 a4 n4) (h15 : NativeRustcVm.Apart a1 n1 a5 n5)
    (h16 : NativeRustcVm.Apart a1 n1 a6 n6) (h23 : NativeRustcVm.Apart a2 n2 a3 n3)
    (h24 : NativeRustcVm.Apart a2 n2 a4 n4) (h25 : NativeRustcVm.Apart a2 n2 a5 n5)
    (h26 : NativeRustcVm.Apart a2 n2 a6 n6) (h34 : NativeRustcVm.Apart a3 n3 a4 n4)
    (h35 : NativeRustcVm.Apart a3 n3 a5 n5) (h36 : NativeRustcVm.Apart a3 n3 a6 n6)
    (h45 : NativeRustcVm.Apart a4 n4 a5 n5) (h46 : NativeRustcVm.Apart a4 n4 a6 n6)
    (h56 : NativeRustcVm.Apart a5 n5 a6 n6) :
    NativeRustcVm.Disjoint [⟨a1, n1⟩, ⟨a2, n2⟩, ⟨a3, n3⟩, ⟨a4, n4⟩, ⟨a5, n5⟩, ⟨a6, n6⟩] := by
  simp only [NativeRustcVm.Disjoint, List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
    implies_true]
  exact ⟨⟨h12, h13, h14, h15, h16⟩, ⟨h23, h24, h25, h26⟩, ⟨h34, h35, h36⟩, ⟨h45, h46⟩, h56⟩

theorem toNat_eq_of_bv {x : UInt64} {v : Nat} (h : x.toNat = v) : x.toBitVec.toNat = v := h

section
variable [Labels]

/-- **`phase_m`'s precondition** at its call, phase `k` at word `pb` of the decoded area. -/
theorem phaseM_pre (G : Geo m0 B) (F : Fix m0 B n ws p cs) {m : MachineData} (hfr : Frm m0 m)
    {pb ck : Nat} (hpb : pb + phaseWords ≤ lenW m0)
    (hR : ReaderAt m.dmem (rdr m0) (bpA m0) B ck) (hx0 : m.regs.X0.toBitVec = rdr m0)
    (hx1 : m.regs.X1.toBitVec = dw m0 pb) (hx2 : m.regs.X2.toBitVec = wk m0) :
    PhaseMPre m := by
  have hsb : stackBelow m 1184 = base m0 1280 := Ring.stackBelow_eq hfr.sp (by have := G.sp; omega)
  obtain ⟨hr, hbl⟩ := G.rdr_base
  have hD := G.dNw
  have hout := G.dw_toNat (i := pb) (by rw [phaseWords_eq] at hpb; omega)
  have hl := F.l_pos
  have hlen := G.len
  have hrc := G.rc.2.1
  have sC := G.sC
  have sD := G.sD
  have sW := G.sW
  have cD := G.cD
  have cW := G.cW
  have dW := G.dW
  have sB := G.sB hl
  have cB := G.cB hl
  have bD := G.bD hl
  have bW := G.bW hl
  have hwN := G.wNw
  have hbN := G.bNw
  unfold NativeRustcVm.Apart at sC sD sW cD cW dW sB cB bD bW
  unfold NoWrap at hrc hbN
  rw [phaseWords_eq] at hpb
  rw [workBytes_eq] at sW cW dW bW hwN
  have hdisj : NativeRustcVm.Disjoint [stackR m 1184, rcR, ⟨rdr m0, 24⟩, ⟨bpA m0, B.length⟩,
      ⟨dw m0 pb, phaseBytes⟩, ⟨wk m0, workBytes⟩] := by
    refine disj6 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [NativeRustcVm.Apart, hsb, hr, hout, hlen, phaseBytes_eq,
        workBytes_eq] <;> omega
  refine ⟨hfr.stackOk G.st (by decide) (by decide), G.rcAt hfr (by decide), ?_, ?_, bpA m0, B,
    ck, by rw [hx0]; exact hR, by rw [hx0, hx1, hx2]; exact hdisj⟩
  · rw [hx1]
    refine ⟨fun i hi ↦ ?_, by
      show (dw m0 pb).toNat + phaseBytes ≤ 2 ^ 64; rw [hout, phaseBytes_eq]; omega⟩
    have hi' : i < 395288 := hi
    rw [NativeRustcVm.addr_add_add]
    exact hfr.kept _ (G.dOk.1 _ (by show 8 * pb + i < 8 * lenW m0; omega))
  · rw [hx2]
    exact ⟨fun i hi ↦ hfr.kept _ (G.wOk.1 i hi), G.wOk.2⟩

/-- `phase_m`'s footprint: outside the decoded area, or phase `k`'s words. -/
theorem phaseM_out (G : Geo m0 B) {m : MachineData} (hfr : Frm m0 m) {pb : Nat}
    (hx0 : m.regs.X0.toBitVec = rdr m0) (hx1 : m.regs.X1.toBitVec = dw m0 pb)
    (hx2 : m.regs.X2.toBitVec = wk m0) {q : BitVec 64}
    (hq : InAny [⟨m.regs.X1.toBitVec, phaseBytes⟩, ⟨m.regs.X2.toBitVec, workBytes⟩,
      curRegion m.regs.X0.toBitVec, stackR m phaseMStack] q) :
    Out m0 q ∨ InRange (dw m0 pb) phaseBytes q := by
  obtain ⟨Rg, hRg, hq⟩ := hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
  rcases hRg with rfl | rfl | rfl | rfl
  · right
    have h : InRange m.regs.X1.toBitVec phaseBytes q := hq
    rwa [hx1] at h
  · left
    have h : InRange m.regs.X2.toBitVec workBytes q := hq
    rw [hx2] at h
    exact G.out_work h
  · left
    have h : InRange (NativeRustcVm.Transcript.off m.regs.X0.toBitVec 16) 8 q := hq
    rw [hx0, cur_eq] at h
    exact G.out_frame (by omega) h
  · left
    exact G.out_stack (stack_sub G hfr (by decide) hq)

/-- The decoder's facts with one more phase. -/
theorem DecF.snoc (G : Geo m0 B) (F : Fix m0 B n ws p cs) {d d' : Mem 64} {ps : List PhaseOut}
    {po : PhaseOut} (h : DecF m0 d n ws p ps) (hps : ps.length < wireMaxPhases)
    {R : BitVec 64 → Prop} (hs : SameOutside d d' R)
    (hR : ∀ q, R q → Out m0 q ∨ InRange (dw m0 (phaseBase (Ln m0) ps.length)) phaseBytes q)
    (hP : PhaseAt d' (dw m0 (phaseBase (Ln m0) ps.length)) (phaseW po)) :
    DecF m0 d' n ws p (ps ++ [po]) := by
  have hpb := phaseBase_le (Ln m0) (j := ps.length + 1) hps
  rw [phaseBase_add] at hpb
  have hdl := G.dLe
  have hk := h.keep G F.ws_len F.hn hps.le hs hR
    (by rw [phaseBytes]; omega) le_rfl
  refine ⟨hk.cnt, hk.words, hk.pc, fun j hj ↦ ?_⟩
  rw [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < ps.length
  · rw [List.getElem_append_left hjl]
    exact hk.phases j hjl
  · have hje : j = ps.length := by omega
    subst hje
    simp only [List.getElem_concat_length]
    exact hP

end

variable [Host] {k0 : Nat}

/-- **One pass of the loop**: done, or one more phase. -/
theorem iter_spec (hp : Placed code k0) (G : Geo m0 B) (F : Fix m0 B n ws p cs)
    (hpm : Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {k : Nat} {st : MachineState}
    (h : LInv k0 m0 B n ws p cs k st) :
    Eventually (step1 Host.exe) (fun s' ↦ Res m0 B s' ∨
      ∃ k', k < k' ∧ k' ≤ p ∧ LInv k0 m0 B n ws p cs k' s') st := by
  obtain ⟨hpc, hfr, x19, x20, x21, x22, x23, x24, ps, ck, hph, hR, hD⟩ := h
  have hst := G.st
  have hp8 : p ≤ 8 := F.p_le
  have hwf := frEnv_wf hst hfr
  have hm := frEnv_match hst hfr
  have e23 : (st.data.regs.getXReg .X23).toBitVec.toNat + k = p := x23
  have e22 : 9 ≤ (st.data.regs.getXReg .X22).toBitVec.toNat + k := x22
  have hlen := phasesM_length B k cs hph
  refine exec_at (infix_of b9_in_code (by simp [b9]) hp) run_b9 hwf hpc hm fun s1 hm1 hpc1 ↦ ?_
  have hfr1 : Frm m0 s1.data := Fr.ofBlock hfr hm hm1 hwf rfl rfl rfl (keepOk (by decide))
  have hd1 : s1.data.dmem = st.data.dmem := hm1.dmem_eq hwf rfl
  have r1 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24],
      s1.data.regs.getXReg x = st.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hc : (SBool.cmp .eq .W64 (.reg .X23) (.lit 0)).eval (frEnv m0 st.data) =
      decide (k = p) := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_lit _ 0 (by norm_num)]
    exact decide_eq_decide.mpr (by omega)
  simp only [PcOk, hc] at hpc1
  by_cases hkp : k = p
  · subst hkp
    simp only [decide_true, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b16Offset) NativeRustcVmArm.Vm.Decode.label_11_at] at hpc1
    exact Eventually.mono (done_spec hp G F hpc1 hfr1 (by rw [r1 .X20 (by simp)]; exact x20) hph
      (by rw [hd1]; exact hR) (by rw [hd1]; exact hD)) fun _ h ↦ .inl h
  have hkp' : k < p := by omega
  simp only [hkp, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  -- `b10`: a slot left
  have hwf1 := frEnv_wf hst hfr1
  have hm1' := frEnv_match hst hfr1
  refine exec_at (infix_of b10_in_code (by simp [b10]) hp) run_b10 hwf1
    (hpc1.trans (congrArg Host.addrOf rfl)) hm1' fun s2 hm2 hpc2 ↦ ?_
  have hfr2 : Frm m0 s2.data := Fr.ofBlock hfr1 hm1' hm2 hwf1 rfl rfl rfl (keepOk (by decide))
  have hd2 : s2.data.dmem = s1.data.dmem := hm2.dmem_eq hwf1 rfl
  have r2 : ∀ x ∈ [XReg.X19, .X20, .X21, .X23, .X24],
      s2.data.regs.getXReg x = st.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      rw [Match.reg_eq hm1' hm2 rfl rfl, r1 _ (by simp)]
  have f22 : (s1.data.regs.getXReg .X22).toBitVec.toNat =
      (st.data.regs.getXReg .X22).toBitVec.toNat := by rw [r1 .X22 (by simp)]
  have x22' : (s2.data.regs.getXReg .X22).toBitVec.toNat =
      (st.data.regs.getXReg .X22).toBitVec.toNat - 1 := by
    rw [hm2.regs .X22 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [toNat_sub_lit (by omega) (by norm_num), f22]
  have hc2 : (SBool.cmp .eq .W64 (.bin .sub .W64 (.reg .X22) (.lit 1)) (.lit 0)).eval
      (frEnv m0 s1.data) = false := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [eq_lit _ 0 (by norm_num), toNat_sub_lit (by omega) (by norm_num), f22]
    exact decide_eq_false (by omega)
  simp only [PcOk, hc2, Bool.false_eq_true, ↓reduceIte] at hpc2
  -- `b11`: `phase_m`'s call
  have hwf2 := frEnv_wf hst hfr2
  have hm2' := frEnv_match hst hfr2
  refine exec_at (infix_of b11_in_code (by simp [b11]) hp) run_b11 hwf2
    (hpc2.trans (congrArg Host.addrOf rfl)) hm2' fun s3 hm3 hpc3 ↦ ?_
  have hfr3 : Frm m0 s3.data := Fr.ofBlock hfr2 hm2' hm3 hwf2 rfl rfl rfl (keepOk (by decide))
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq hwf2 rfl
  have hpb : phaseBase (Ln m0) k + phaseWords ≤ lenW m0 := by
    have := phaseBase_le (Ln m0) (j := k + 1) (by show k + 1 ≤ 8; omega)
    rw [phaseBase_add] at this
    have := G.dLe
    omega
  have h24 : (st.data.regs.getXReg .X24).toBitVec = BitVec.ofNat 64 phaseBytes := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, phaseBytes_eq]
    exact x24
  have hadd : BinOp.apply .add .W64 (s2.data.regs.getXReg .X21).toBitVec
      (s2.data.regs.getXReg .X24).toBitVec = dw m0 (phaseBase (Ln m0) k) := by
    rw [r2 .X21 (by simp), r2 .X24 (by simp), h24, ← x21]
    simp [BinOp.apply]
  have hx0 : s3.data.regs.X0.toBitVec = rdr m0 := by
    rw [show s3.data.regs.X0 = s3.data.regs.getXReg .X0 from rfl, hm3.regs .X0 _ rfl]
    rfl
  have hx1 : s3.data.regs.X1.toBitVec = dw m0 (phaseBase (Ln m0) k) := by
    rw [show s3.data.regs.X1 = s3.data.regs.getXReg .X1 from rfl, hm3.regs .X1 _ rfl]
    exact hadd
  have hx2 : s3.data.regs.X2.toBitVec = wk m0 := by
    rw [show s3.data.regs.X2 = s3.data.regs.getXReg .X2 from rfl, hm3.regs .X2 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [r2 .X19 (by simp), x19]
  have x21' : (s3.data.regs.getXReg .X21).toBitVec = dw m0 (phaseBase (Ln m0) k) := by
    rw [hm3.regs .X21 _ rfl]; exact hadd
  have x23' : (s3.data.regs.getXReg .X23).toBitVec.toNat + (k + 1) = p := by
    rw [hm3.regs .X23 _ rfl]
    simp only [Sym.eval, Env.ofMachine_regs]
    rw [toNat_sub_lit (by rw [r2 .X23 (by simp)]; omega) (by norm_num), r2 .X23 (by simp)]
    omega
  have x22'' : (s3.data.regs.getXReg .X22) = s2.data.regs.getXReg .X22 :=
    Match.reg_eq hm2' hm3 rfl rfl
  have r3 : ∀ x ∈ [XReg.X19, .X20, .X24],
      s3.data.regs.getXReg x = st.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> rw [Match.reg_eq hm2' hm3 rfl rfl, r2 _ (by simp)]
  have hR3 : ReaderAt s3.data.dmem (rdr m0) (bpA m0) B ck := by rw [hd3, hd2, hd1]; exact hR
  have hD3 : DecF m0 s3.data.dmem n ws p ps := by rw [hd3, hd2, hd1]; exact hD
  have hpre := phaseM_pre G F hfr3 hpb hR3 hx0 hx1 hx2
  simp only [PcOk] at hpc3
  have hNs : 96 + phaseMStack ≤ 1280 := by decide
  have hQ : ∀ m', PhaseMPost s3.data m' → SameOutside s3.data.dmem m'.dmem (fun q ↦
      InRange (stackBelow s3.data phaseMStack) phaseMStack q ∨
      InRange (base m0 96 + BitVec.ofNat 64 24) 8 q ∨ W m0 q) ∧ Saved s3.data m' := by
    rintro m' ⟨-, hs, hsv⟩
    refine ⟨NativeRustcVm.SameOutside.mono hs fun q ⟨Rg, hRg, hq⟩ ↦ ?_, hsv⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hRg
    rcases hRg with rfl | rfl | rfl | rfl
    · have h : InRange s3.data.regs.X1.toBitVec phaseBytes q := hq
      rw [hx1] at h
      exact .inr (.inr (.inl (NativeRustcVm.InRange.of_sub h G.dNw
        (by rw [phaseBytes_eq]; rw [phaseWords_eq] at hpb; omega))))
    · have h : InRange s3.data.regs.X2.toBitVec workBytes q := hq
      rw [hx2] at h
      exact .inr (.inr (.inr h))
    · have h : InRange (NativeRustcVm.Transcript.off s3.data.regs.X0.toBitVec 16) 8 q := hq
      rw [hx0, cur_eq] at h
      exact .inr (.inl h)
    · exact .inl hq
  refine Fr.leafIn (N' := phaseMStack) (lo := 24) (n := 8) hfr3 G.sp hNs (by omega) (by decide)
    (by decide) G.notFrame hpm hpc3 hpre hQ fun m2 hfr4 hq2 hcs ↦ ?_
  obtain ⟨hpost, hs2, -⟩ := hq2
  have hpost' := hpost (bpA m0) B ck (by rw [hx0]; exact hR3)
  rw [hx0, hx1] at hpost'
  -- `b12`: the outcome
  have hwf4 := frEnv_wf hst hfr4
  have hm4 := frEnv_match hst hfr4
  refine exec_at (infix_of b12_in_code (by simp [b12]) hp) run_b12 hwf4
    (congrArg Host.addrOf rfl) hm4 fun s5 hm5 hpc5 ↦ ?_
  have hfr5 : Frm m0 s5.data := Fr.ofBlock hfr4 hm4 hm5 hwf4 rfl rfl rfl (keepOk (by decide))
  have hd5 : s5.data.dmem = m2.dmem := hm5.dmem_eq hwf4 rfl
  simp only [PcOk] at hpc5
  rcases hpo : phaseM B ck with _ | ⟨po, c'⟩
  · rw [hpo] at hpost'
    have hb : (SBool.bit .W32 (.un .trunc .W32 (.reg .X0)) 0).eval (frEnv m0 m2) = false := by
      simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
      rw [show m2.regs.getXReg .X0 = 0 from hpost']
      rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte] at hpc5
    -- `b13`: `None`
    have hwf6 := frEnv_wf hst hfr5
    have hm6 := frEnv_match hst hfr5
    refine exec_at (infix_of b13_in_code (by simp [b13]) hp) run_b13 hwf6
      (hpc5.trans (congrArg Host.addrOf rfl)) hm6 fun s6 hm7 hpc6 ↦ ?_
    have hfr6 : Frm m0 s6.data := Fr.ofBlock hfr5 hm6 hm7 hwf6 rfl rfl rfl (keepOk (by decide))
    simp only [PcOk, hp.label (j := NativeRustcVmArm.Vm.Decode.b15Offset) NativeRustcVmArm.Vm.Decode.label_10_at] at hpc6
    refine Eventually.mono (exit15 hp G hpc6 hfr6 ?_) fun _ h ↦ .inl h
    have hnone : decodeM B = none := by
      rw [F.dec, show p = k + (p - k - 1) + 1 by omega, phasesM_none B k hph hpo]
    rw [hnone]
    have e0 : s6.data.regs.getXReg .X0 = s5.data.regs.getXReg .X0 := Match.reg_eq hm6 hm7 rfl rfl
    apply UInt64.toBitVec_inj.mp
    rw [show s6.data.regs.X0 = s6.data.regs.getXReg .X0 from rfl, e0, hm5.regs .X0 _ rfl]
    rfl
  rw [hpo] at hpost'
  obtain ⟨h0, hPh, hR4⟩ := hpost'
  have hb : (SBool.bit .W32 (.un .trunc .W32 (.reg .X0)) 0).eval (frEnv m0 m2) = true := by
    simp only [SBool.eval, Sym.eval, Env.ofMachine_regs]
    rw [show m2.regs.getXReg .X0 = 1 from h0]
    rfl
  simp only [hb, ↓reduceIte, hp.label (j := NativeRustcVmArm.Vm.Decode.b9Offset) NativeRustcVmArm.Vm.Decode.label_6_at] at hpc5
  have r5 : ∀ x ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24],
      s5.data.regs.getXReg x = s3.data.regs.getXReg x := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [Match.reg_eq hm4 hm5 rfl rfl, hcs _ rfl]
  have hDn : DecF m0 m2.dmem n ws p (ps ++ [po]) :=
    DecF.snoc G F hD3 (by rw [hlen]; show k < 8; omega) hs2
      (fun q hq ↦ by rw [hlen]; exact phaseM_out G hfr3 hx0 hx1 hx2 hq) (by rw [hlen]; exact hPh)
  refine .done _ (.inr ⟨k + 1, by omega, by omega, hpc5, hfr5, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨ps ++ [po], c', phasesM_snoc B k hph hpo, by rw [hd5]; exact hR4, by rw [hd5]; exact hDn⟩⟩)
  · rw [r5 .X19 (by simp), r3 .X19 (by simp)]; exact x19
  · rw [r5 .X20 (by simp), r3 .X20 (by simp)]; exact x20
  · rw [r5 .X21 (by simp), x21', phaseBase_add, NativeRustcVm.addr_add_add]
    show _ = decA m0 + BitVec.ofNat 64 (8 * (phaseBase (Ln m0) k + phaseWords))
    rw [Nat.mul_add, phaseBytes]
  · show 9 ≤ (s5.data.regs.getXReg .X22).toBitVec.toNat + (k + 1)
    rw [r5 .X22 (by simp), x22'', x22']
    omega
  · show (s5.data.regs.getXReg .X23).toBitVec.toNat + (k + 1) = p
    rw [r5 .X23 (by simp)]
    exact x23'
  · rw [r5 .X24 (by simp), r3 .X24 (by simp)]; exact x24

/-- **The loop** from `k` phases read. -/
theorem loop_spec (hp : Placed code k0) (G : Geo m0 B) (F : Fix m0 B n ws p cs)
    (hpm : Spec (Labels.label NativeRustcVmArm.Vm.PhaseM.entryLabel) PhaseMPre PhaseMPost) {k : Nat} {st : MachineState}
    (h : LInv k0 m0 B n ws p cs k st) : Eventually (step1 Host.exe) (Res m0 B) st := by
  have hk : k ≤ p := by have := h.x23; omega
  refine Sym.loop (tr := step1 Host.exe) (Q := Res m0 B)
    (fun j s ↦ ∃ k, k ≤ p ∧ j = p - k ∧ LInv k0 m0 B n ws p cs k s) ?_ ⟨k, hk, rfl, h⟩
  rintro j s ⟨k, -, rfl, hI⟩
  exact Eventually.mono (iter_spec hp G F hpm hI) fun s' h' ↦ h'.elim .inl
    fun ⟨k', hkk, hk'p, hI'⟩ ↦ .inr ⟨p - k', by omega, k', hk'p, rfl, hI'⟩

end

end NativeRustcVmArm.Wire.Decode
