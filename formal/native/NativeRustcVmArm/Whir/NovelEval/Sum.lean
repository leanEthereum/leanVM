module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.NovelEval.Outer

/-!
# `novel_eval`'s sum

From the complete basis (`Mid`, at `b9`): `b9` takes `min size count` (`lenOf`); none goes by
`b16` with the sum `0` (`Done`), else `b10` starts the sum (`SInv 0`). A turn (`sum_step`): `b11`
loads coefficient `t` and basis word `t` and calls `kmul` (`b·c₀`), `b12` calls `kmul` (`b·c₁`),
`b13` adds the product and counts; after the last, `b14` goes to `b17`.
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm

public section

theorem ite_ult_toNat (a b : BitVec 64) :
    (if a.ult b = true then a else b).toNat = min a.toNat b.toNat := by
  by_cases h : a.ult b = true
  · simp only [h, ↓reduceIte]
    simp only [BitVec.ult, decide_eq_true_eq] at h
    omega
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    simp only [BitVec.ult, decide_eq_true_eq] at h
    omega

/-- Coefficient `t` in a body. -/
theorem coef_eq {m0 st : MachineData} (hpre : NovelEvalPre m0) (hfr : NFrame m0 st) {t : Nat}
    (ht : t < cnt m0) :
    NativeRustcVm.ewOf st.dmem (m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * t)) =
      (csOf m0)[t]'(by rw [csOf_size]; exact ht) := by
  rw [csOf_get]
  refine NativeRustcVm.ewOf_congr fun i hi ↦ ?_
  rw [addr_add]
  exact hfr.get?_arg hpre.1 hpre.2.1 (fun r hr ↦ absurd hr List.not_mem_nil) _
    (by unfold cnt at ht; omega)

variable [Host] {k : Nat}

/-- **The basis complete**: to the sum's head, or with no product to the end. -/
theorem mid_sum (hp : Placed code k) {m0 : MachineData} {st : MachineData} (hM : Mid m0 st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b17Offset)) ∨
        (SInv m0 0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b11Offset) ∧ 0 < lenOf m0))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset)⟩ := by
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk9 run_b9 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb9 := after_eq run_b9 ▸ regs_keeps b9 (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
  have hfr1 := hM.fr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb9.1 hb9.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb9.2
  have e19 : s1.data.regs.X19 = st.regs.X19 := Match.reg_eq (r := .X19) (match_nil _) hm1 rfl rfl
  have e20 : s1.data.regs.X20 = st.regs.X20 := Match.reg_eq (r := .X20) (match_nil _) hm1 rfl rfl
  have h24 : (st.regs.getXReg .X24).toBitVec.toNat = (basisOf m0 (wn m0)).size := hM.x24
  have h21 : (st.regs.getXReg .X21).toBitVec.toNat = cnt m0 := by
    show st.regs.X21.toNat = _
    rw [hM.rg.x21]; rfl
  have h25 : (s1.data.regs.getXReg .X25).toBitVec.toNat = lenOf m0 := by
    rw [hm1.regs .X25 _ rfl]
    sym_simp
    rw [Env.ofMachine_regs, Env.ofMachine_regs, ite_ult_toNat, h24, h21]
    rfl
  have hcond : (SBool.cmp .eq .W64 (Sym.ite (SBool.cmp .ult .W64 (.reg .X24) (.reg .X21))
      (.reg .X24) (.reg .X21)) (.lit 0)).eval (Env.ofMachine st []) = decide (lenOf m0 = 0) := by
    sym_simp
    rw [bv_beq_toNat, ite_ult_toNat, Env.ofMachine_regs, Env.ofMachine_regs, h24, h21]
    simp [lenOf]
  simp only [PcOk] at hpc1
  rw [hcond] at hpc1
  have hsz := novelPre_size_pos (whatOf m0) (cnt m0) (wn m0)
  by_cases h0 : lenOf m0 = 0
  · -- no product: `b16`, the sum `0`
    simp only [h0, decide_true, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.NovelEval.label_11 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b16Offset) from hp.label (j := NativeRustcVmArm.Vm.NovelEval.b16Offset) NativeRustcVmArm.Vm.NovelEval.label_11_at] at hpc1
    have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk16 run_b16 (Env.wf_nil _) hpc1 (match_nil _) fun s2 hm2 hpc2 ↦ .done _ (.inl ?_)
    have hb16 := after_eq run_b16 ▸ regs_keeps b16
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.tail _ (.head _)))))))))))
    have hfr2 := hfr1.of_regs (match_nil _) hm2 (Env.wf_nil _) rfl hb16.1 hb16.2
    refine ⟨⟨hfr2, ?_, ?_, ?_⟩, hpc2⟩
    · show s2.data.regs.getXReg .X19 = _
      exact (Match.reg_eq (r := .X19) (match_nil _) hm2 rfl rfl).trans (e19.trans hM.rg.x19)
    · apply UInt64.toBitVec_inj.mp
      rw [show s2.data.regs.X24.toBitVec = _ from hm2.regs .X24 _ rfl, h0, novelAcc_zero]
      rfl
    · apply UInt64.toBitVec_inj.mp
      rw [show s2.data.regs.X23.toBitVec = _ from hm2.regs .X23 _ rfl, h0, novelAcc_zero]
      rfl
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
    have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b10Offset) := hpc1
    refine exec_at hk10 run_b10 (Env.wf_nil _) hpc1' (match_nil _) fun s2 hm2 hpc2 ↦
      .done _ (.inr ⟨?_, hpc2, by omega⟩)
    have hb10 := after_eq run_b10 ▸ regs_keeps b10
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    have hfr2 := hfr1.of_regs (match_nil _) hm2 (Env.wf_nil _) rfl hb10.1 hb10.2
    have hd2 : s2.data.dmem = st.dmem := (hm2.dmem_eq (Env.wf_nil _) hb10.2).trans hd1
    refine ⟨hfr2, ?_, ?_, ?_, ?_, ?_, ?_, hd2 ▸ hM.basis⟩
    · show s2.data.regs.getXReg .X19 = _
      exact (Match.reg_eq (r := .X19) (match_nil _) hm2 rfl rfl).trans (e19.trans hM.rg.x19)
    · show (s2.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [Match.reg_eq (r := .X25) (match_nil _) hm2 rfl rfl, h25, Nat.sub_zero]
    · refine (hm2.regs .X26 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs, Match.reg_eq (r := .X20) (match_nil _) hm1 rfl rfl]
      show st.regs.X20.toBitVec + _ = _
      rw [hM.rg.x20]
    · refine (hm2.regs .X27 _ rfl).trans ?_
      simp only [Sym.eval]
      show s1.data.regs.SP.toBitVec = _
      rw [hfr1.sp]
      simp [fbOf]
    · apply UInt64.toBitVec_inj.mp
      rw [show s2.data.regs.X24.toBitVec = _ from hm2.regs .X24 _ rfl, novelAcc_zero]
      rfl
    · apply UInt64.toBitVec_inj.mp
      rw [show s2.data.regs.X23.toBitVec = _ from hm2.regs .X23 _ rfl, novelAcc_zero]
      rfl

/-- **A turn of the sum.** -/
theorem sum_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {t : Nat}
    (ht : t < lenOf m0) {st : MachineData} (hI : SInv m0 t st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b17Offset)) ∨
        (SInv m0 (t + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b11Offset) ∧ t + 1 < lenOf m0))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b11Offset)⟩ := by
  have hS : StackOk m0 novelEvalStack := hpre.1
  have hcs := hpre.2.1
  have hF : 1120 ≤ novelEvalStack := by decide
  have hkle : 1120 + kmulStack ≤ novelEvalStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  let B := basisOf m0 (wn m0)
  have hlen : lenOf m0 = min B.size (cnt m0) := rfl
  have htB : t < B.size := by omega
  have htc : t < cnt m0 := by omega
  have htc' : t < (csOf m0).size := by rw [csOf_size]; exact htc
  have hx2 : cnt m0 = m0.regs.X2.toNat := rfl
  let ca := m0.regs.X1.toBitVec + BitVec.ofNat 64 (16 * t)
  let ba := fbOf m0 + BitVec.ofNat 64 (8 * t)
  have hcrd : Readable st ca 16 := hfr.readable (Readable.sub hcs.1 (by omega))
  have hbrd : Readable st ba 8 := hfr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  have hap0 := apart_frame hcs.2 hF hS.2.1
  have hcnw : m0.regs.X1.toBitVec.toNat + 16 * m0.regs.X2.toNat ≤ 2 ^ 64 := hcs.1.2
  have hfnw' : (m0.regs.SP.toBitVec - BitVec.ofNat 64 1120).toNat + 1120 ≤ 2 ^ 64 := hfnw
  have hcaN : ca.toNat = m0.regs.X1.toBitVec.toNat + 16 * t := toNat_add_ofNat' (by omega)
  have hfbe : (fbOf m0).toNat = (m0.regs.SP.toBitVec - BitVec.ofNat 64 1120).toNat := rfl
  have hbaN : ba.toNat = (m0.regs.SP.toBitVec - BitVec.ofNat 64 1120).toNat + 8 * t := by
    rw [← hfbe]
    exact toNat_add_ofNat' (by omega)
  have hap : Apart ca 16 ba 8 := by
    unfold Apart at hap0 ⊢
    rw [hcaN, hbaN]
    omega
  let env := Env.ofMachine st [(ca, 16), (ba, 8)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hcrd.1, hcrd.2⟩, ⟨hbrd.1, hbrd.2⟩, trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match env sumS st :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl
      ⟨by
        show st.regs.X26.toBitVec = ca + BitVec.ofInt 64 8
        rw [hI.x26, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add],
       by
        show st.regs.X27.toBitVec = ba + BitVec.ofInt 64 0
        rw [hI.x27, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero],
       trivial⟩
      trivial trivial trivial
  -- `b11`: load coefficient and basis word, `kmul(b, c₀)`
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk11 run_b11 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb11 := after_eq run_b11 ▸ b11_keeps
  have hfr1 := hfr.of_regs hm hm1 hwf rfl hb11.1 hb11.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf hb11.2
  have hcoef := coef_eq hpre hfr htc
  have hbw : NativeRustcVm.WordAt env.mem0 (env.base 1 + BitVec.ofNat 64 0) (B[t]'htB) := by
    rw [NativeRustcVm.addr_add_zero]
    exact NativeRustcVm.wordsAt_getElem hI.basis (by simpa using htB)
  have hb0 : s1.data.regs.X0 = B[t]'htB :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X0 _ rfl).trans (load_word hbw))
  have hb21 : s1.data.regs.X21 = B[t]'htB :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X21 _ rfl).trans (load_word hbw))
  have hc0 : s1.data.regs.X1 = ((csOf m0)[t]'htc').c0 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X1 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [load8_eq, ← hcoef, NativeRustcVm.addr_add_zero]
    rfl
  have hc1 : s1.data.regs.X20 = ((csOf m0)[t]'htc').c1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X20 _ rfl).trans ?_
    simp only [Sym.eval]
    rw [load8_eq, ← hcoef]
    rfl
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hx0, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hlenB : (B.toList.flatMap NativeRustcVm.wordBytes).length = 8 * B.size := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList]
  have hB64 : B.size ≤ 64 := novelPre_size_le _ hc _
  have hbasis2 : NativeRustcVm.WordsAt s2.data.dmem (fbOf m0) B.toList := by
    have := hfr1.bytes_call hS hkle hsame2 (o := 0) (by rw [hlenB]; omega)
      (by rw [NativeRustcVm.addr_add_zero, hd1]; exact hI.basis)
    rwa [NativeRustcVm.addr_add_zero] at this
  -- `b12`: `kmul(b, c₁)`
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b12Offset) := hpc2
  refine exec_at hk12 run_b12 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb12 := after_eq run_b12 ▸ regs_keeps b12
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb12.1 hb12.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb12.2
  have h3_0 : s3.data.regs.X0 = B[t]'htB :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)).trans ((hsv2.1 .X21 rfl).trans hb21)
  have h3_1 : s3.data.regs.X1 = ((csOf m0)[t]'htc').c1 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)).trans ((hsv2.1 .X20 rfl).trans hc1)
  have h3_22 : s3.data.regs.X22 = kmul (B[t]'htB) ((csOf m0)[t]'htc').c0 := by
    show s3.data.regs.getXReg .X22 = _
    rw [UInt64.toBitVec_inj.mp (hm3.regs .X22 _ rfl)]
    show s2.data.regs.X0 = _
    rw [hx0, hb0, hc0]
  refine call_then hpc3 hkmul (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hx0', hsame4, hsv4⟩ ↦ ?_
  have hfr4 := hfr3.call hS hkle slots_le hsame4 hsv4
  have hbasis4 : NativeRustcVm.WordsAt s4.data.dmem (fbOf m0) B.toList := by
    have := hfr3.bytes_call hS hkle hsame4 (o := 0) (by rw [hlenB]; omega)
      (by rw [NativeRustcVm.addr_add_zero, hd3]; exact hbasis2)
    rwa [NativeRustcVm.addr_add_zero] at this
  -- `b13`: add, count
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b13Offset) := hpc4
  refine exec_at hk13 run_b13 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have hb13 := after_eq run_b13 ▸ regs_keeps b13
    (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))
  have hfr5 := hfr4.of_regs (match_nil _) hm5 (Env.wf_nil _) rfl hb13.1 hb13.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq (Env.wf_nil _) hb13.2
  -- the registers through the block and the calls
  have k4 : ∀ r ∈ [XReg.X19, .X23, .X24, .X25], s4.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
    exact (hsv4.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans
      ((hsv2.1 _ rfl).trans (Match.reg_eq hm hm1 rfl rfl)))
  have k26 : s4.data.regs.X26 = s1.data.regs.X26 :=
    (hsv4.1 .X26 rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans (hsv2.1 .X26 rfl))
  have k27 : s4.data.regs.X27 = s1.data.regs.X27 :=
    (hsv4.1 .X27 rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans (hsv2.1 .X27 rfl))
  have k22 : s4.data.regs.X22 = kmul (B[t]'htB) ((csOf m0)[t]'htc').c0 :=
    (hsv4.1 .X22 rfl).trans h3_22
  have hx0'' : s4.data.regs.X0 = kmul (B[t]'htB) ((csOf m0)[t]'htc').c1 := by
    rw [hx0', h3_0, h3_1]
  have hacc : novelAcc (csOf m0) B (t + 1) =
      ⟨(novelAcc (csOf m0) B t).c0 ^^^ kmul (B[t]'htB) ((csOf m0)[t]'htc').c0,
        (novelAcc (csOf m0) B t).c1 ^^^ kmul (B[t]'htB) ((csOf m0)[t]'htc').c1⟩ := by
    rw [novelAcc_succ _ _ htc' htB]
    rfl
  have x19 : s5.data.regs.X19 = m0.regs.X0 :=
    (Match.reg_eq (r := .X19) (match_nil _) hm5 rfl rfl).trans ((k4 .X19 (by simp)).trans hI.x19)
  have x24 : s5.data.regs.X24 = (novelAcc (csOf m0) B (t + 1)).c0 := by
    rw [hacc]
    apply UInt64.toBitVec_inj.mp
    refine (hm5.regs .X24 _ rfl).trans ?_
    sym_simp
    simp only [Env.ofMachine_regs]
    show s4.data.regs.X22.toBitVec ^^^ s4.data.regs.X24.toBitVec = _
    rw [k22, show s4.data.regs.X24 = st.regs.X24 from k4 .X24 (by simp), hI.x24, ← UInt64.toBitVec_xor,
      UInt64.xor_comm]
  have x23 : s5.data.regs.X23 = (novelAcc (csOf m0) B (t + 1)).c1 := by
    rw [hacc]
    apply UInt64.toBitVec_inj.mp
    refine (hm5.regs .X23 _ rfl).trans ?_
    sym_simp
    simp only [Env.ofMachine_regs]
    show s4.data.regs.X0.toBitVec ^^^ s4.data.regs.X23.toBitVec = _
    rw [hx0'', show s4.data.regs.X23 = st.regs.X23 from k4 .X23 (by simp), hI.x23,
      ← UInt64.toBitVec_xor, UInt64.xor_comm]
  have hbasis5 : NativeRustcVm.WordsAt s5.data.dmem (fbOf m0) B.toList := hd5 ▸ hbasis4
  have h25 : (s4.data.regs.getXReg .X25).toBitVec.toNat = lenOf m0 - t := by
    rw [k4 .X25 (by simp)]; exact hI.x25
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [Env.ofMachine_regs, bv_beq_toNat, h25, BitVec.toNat_ofNat] at hpc5
  by_cases hlast : lenOf m0 - t = 1
  · simp only [hlast, Nat.one_mod, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpc5
    have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b14Offset) := hpc5
    refine exec_at hk14 run_b14 (Env.wf_nil _) hpc5' (match_nil _) fun s6 hm6 hpc6 ↦
      .done _ (.inl ⟨?_, ?_⟩)
    · have hb14 := after_eq run_b14 ▸ regs_keeps b14
        (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
          (.head _)))))))))
      refine ⟨hfr5.of_regs (match_nil _) hm6 (Env.wf_nil _) rfl hb14.1 hb14.2,
        (Match.reg_eq (r := .X19) (match_nil _) hm6 rfl rfl).trans x19, ?_, ?_⟩
      · show s6.data.regs.getXReg .X24 = _
        rw [Match.reg_eq (r := .X24) (match_nil _) hm6 rfl rfl, show lenOf m0 = t + 1 by omega]
        exact x24
      · show s6.data.regs.getXReg .X23 = _
        rw [Match.reg_eq (r := .X23) (match_nil _) hm6 rfl rfl, show lenOf m0 = t + 1 by omega]
        exact x23
    · simp only [PcOk] at hpc6
      rw [hpc6]
      exact hp.label (j := NativeRustcVmArm.Vm.NovelEval.b17Offset) NativeRustcVmArm.Vm.NovelEval.label_12_at
  · simp only [show ¬lenOf m0 - t = 1 % 2 ^ 64 by simpa using hlast, decide_false, Bool.not_false,
      ↓reduceIte] at hpc5
    refine .done _ (.inr ⟨⟨hfr5, x19, ?_, ?_, ?_, x24, x23, hbasis5⟩,
      hpc5.trans (hp.label (j := NativeRustcVmArm.Vm.NovelEval.b11Offset) NativeRustcVmArm.Vm.NovelEval.label_9_at), by omega⟩)
    · show (s5.data.regs.getXReg .X25).toBitVec.toNat = _
      rw [hm5.regs .X25 _ rfl]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_sub, h25]
      show (2 ^ 64 - 1 % 2 ^ 64 + (lenOf m0 - t)) % 2 ^ 64 = _
      omega
    · refine (hm5.regs .X26 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs]
      show s4.data.regs.X26.toBitVec + _ = _
      rw [k26]
      show (s1.data.regs.getXReg .X26).toBitVec + _ = _
      rw [hm1.regs .X26 _ rfl]
      show ca + BitVec.ofInt 64 8 + BitVec.ofNat 64 16 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add, addr_add]
      rfl
    · show (s5.data.regs.getXReg .X27).toBitVec = _
      rw [Match.reg_eq (r := .X27) (match_nil _) hm5 rfl rfl]
      show s4.data.regs.X27.toBitVec = _
      rw [k27]
      show (s1.data.regs.getXReg .X27).toBitVec = _
      rw [hm1.regs .X27 _ rfl]
      show ba + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
      rfl

end

end NativeRustcVmArm.Whir.NovelEval
