module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.Memset.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.NovelEval.Sum

/-!
# `novel_eval`

`b0` saves the callee-saved registers in its 1120-byte frame and zeroes the basis (`memset`);
more than 64 coefficients (`b1`) go by `b15` to `b18`, which stores `None`. Else `b2` sets
`basis[0] = 1`; for fewer than two coefficients the basis is complete (`b9`), else `b3` starts the
doubling loop (`outer_step`, by `Sym.loop`). The sum (`mid_sum`, `sum_step`) ends at `b17`, which
stores the sum, and `b18` the tag `1`; the output holds `novelEval` (`novelEval_eq`).
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm.Transcript (off OptEWAt)

public section

theorem shl3_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The sum `Done` holds is `novelEval`. -/
theorem novelEval_done (m0 : MachineData) :
    novelEval (slice m0 m0.regs.X1 m0.regs.X2) (wordSlice m0 m0.regs.X3.toBitVec m0.regs.X4.toNat) =
      novelAcc (csOf m0) (basisOf m0 (wn m0)) (lenOf m0) := by
  show novelEval (csOf m0) (whatOf m0) = _
  rw [novelEval_eq, csOf_size, whatOf_size]
  rfl

variable [Host] {k : Nat}

/-- The output region and the frame, for `b17`, `b18`. -/
theorem out_env {m0 st : MachineData} (hpre : NovelEvalPre m0) (hfr : NFrame m0 st)
    (h19 : st.regs.X19 = m0.regs.X0) :
    (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)]).WF ∧
      Match (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)]) outS st := by
  obtain ⟨hS, -, -, hout⟩ := hpre
  have hF : 1120 ≤ novelEvalStack := by decide
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  refine ⟨Env.wf_of ⟨⟨(hfr.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨(hfr.readable hout.1).1, hout.1.2⟩,
      trivial⟩ (List.pairwise_pair.mpr (apart_frame hout.2 hF hS.2.1).symm), ?_⟩
  exact match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl,
      fun h ↦ absurd h (by decide), trivial⟩
    (by rw [hfr.sp]; simp [Sym.eval, fbOf])
    ⟨by
      show st.regs.X19.toBitVec = m0.regs.X0.toBitVec + BitVec.ofInt 64 0
      rw [h19]; simp, trivial⟩ trivial trivial trivial

/-- What `b18` keeps: memory outside the output and the stack. -/
theorem out_same {m0 st st' : MachineData} {S : SState} (hpre : NovelEvalPre m0)
    (hfr : NFrame m0 st)
    (hwf : (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)]).WF)
    (hm : Match (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)]) S st')
    (hS : ∀ w ∈ S.mem, w.r = 1 ∧ w.off + w.n ≤ 24) :
    ChangesIn m0 st' novelEvalStack [⟨m0.regs.X0.toBitVec, 24⟩] := by
  intro a ha
  rw [hm.get?_mem0 hwf fun hw ↦ ha (.inl ⟨_, List.mem_singleton_self _,
    Written.inRange (r := 1) rfl hpre.2.2.2.1.2 hS hw⟩)]
  exact hfr.same a fun h ↦ ha (h.elim (fun ⟨_, hr, _⟩ ↦ absurd hr List.not_mem_nil) .inr)

/-- **After the sum**: `Some` of the sum, the epilogue. -/
theorem finish (hp : Placed code k) {m0 : MachineData} (hpre : NovelEvalPre m0)
    (hc : cnt m0 ≤ 64) {st : MachineData} (hD : Done m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ NovelEvalPost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b17Offset)⟩ := by
  obtain ⟨hwf, hm⟩ := out_env hpre hD.fr hD.x19
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk17 run_b17 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b18Offset) := hpc1
  refine exec_at hk18 run_b18 hwf hpc1' hm1 fun s2 hm2 hpc2 ↦ .done _ ?_
  have hb18 := after_eq run_b18 ▸ b18_restores
  obtain ⟨hsaved, hx30⟩ := hD.fr.ret hm2 hwf x30_mem hb18.1
  have hb1 : (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)]).regions[1]? =
      some (m0.regs.X0.toBitVec, 24) := rfl
  refine ⟨hpc2.trans (by simp only [retOf, hx30]), ?_, out_same hpre hD.fr hwf hm2 hb18.2, hsaved⟩
  show OptEWAt _ _ (if m0.regs.X2.toNat ≤ laneCap then _ else _)
  simp only [show m0.regs.X2.toNat ≤ laneCap from hc, ↓reduceIte]
  rw [novelEval_done]
  refine ⟨?_, ?_⟩
  · have := Match.wordAt_write hm2 hb1 (o := 0) (by decide) (v := .lit 1) (by decide)
    rwa [NativeRustcVm.addr_add_zero] at this
  · rw [NativeRustcVm.ewAt_iff]
    refine ⟨?_, ?_⟩
    · have := Match.wordAt_write hm2 hb1 (o := 8) (by decide) (v := .reg .X24) (by decide)
      rw [show UInt64.ofBitVec ((Sym.reg .X24).eval
          (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)])) = st.regs.X24 from rfl,
        hD.x24] at this
      exact this
    · have := Match.wordAt_write hm2 hb1 (o := 16) (by decide) (v := .reg .X23) (by decide)
      rw [show UInt64.ofBitVec ((Sym.reg .X23).eval
          (Env.ofMachine st [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)])) = st.regs.X23 from rfl,
        hD.x23] at this
      rwa [off, addr_add]

/-- **The basis complete**: the sum, then `finish`. -/
theorem from_mid (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : NovelEvalPre m0) (hc : cnt m0 ≤ 64) {st : MachineData}
    (hM : Mid m0 st) :
    Eventually (step1 Host.exe) (fun s ↦ s.pc = retOf m0 ∧ NovelEvalPost m0 s.data)
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset)⟩ := by
  refine (mid_sum hp hM).bind fun s h ↦ ?_
  rcases h with ⟨hD, hpc⟩ | ⟨hI, hpc, hlt⟩
  · obtain ⟨d, pc⟩ := s
    simp only at hpc
    subst hpc
    exact finish hp hpre hc hD
  · have hloop := Sym.loop (tr := step1 Host.exe)
      (Q := fun s ↦ Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b17Offset))
      (fun n s ↦ ∃ t, n = lenOf m0 - t ∧ t < lenOf m0 ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b11Offset) ∧
        SInv m0 t s.data)
      (fun n s ⟨t, hn', ht, hpc, hI'⟩ ↦ by
        obtain ⟨d, pc⟩ := s
        simp only at hpc
        subst hpc
        refine (sum_step hp hkmul hpre hc ht hI').mono fun s' h ↦ ?_
        rcases h with h | ⟨hI'', hpc', hlt'⟩
        · exact .inl h
        · exact .inr ⟨lenOf m0 - (t + 1), by omega, t + 1, rfl, hlt', hpc', hI''⟩)
      (n := lenOf m0) ⟨0, by omega, hlt, hpc, hI⟩
    refine hloop.bind fun s ⟨hD, hpc⟩ ↦ ?_
    obtain ⟨d, pc⟩ := s
    simp only at hpc
    subst hpc
    exact finish hp hpre hc hD

/-- **`novel_eval`'s contract.** -/
theorem novelEval_spec (hp : Placed code k)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmemset : Spec (label NativeRustcVmArm.Vm.Memset.entryLabel) MemsetPre MemsetPost) :
    Spec (label NativeRustcVmArm.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost := by
  intro m0 hpre
  have hpre' := hpre
  obtain ⟨hS, hcs, hwin, hout⟩ := hpre'
  have hF : 1120 ≤ novelEvalStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  rw [show Labels.label NativeRustcVmArm.Vm.NovelEval.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b0Offset) from hp.label NativeRustcVmArm.Vm.NovelEval.entry_at]
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let fb := fbOf m0
  let env0 := Env.ofMachine m0 [(fb, 1120)]
  have hwf0 : env0.WF := wf_one hfmap hfnw
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_then hk0 run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb0 := after_eq run_b0 ▸ b0_frame
  have hfr1 : NFrame m0 s1.data := Frame.of_entry hS hF hwf0 hm1 rfl hb0.1 hb0.2.2 hb0.2.1
  -- `memset` of the basis
  have hx0 : s1.data.regs.X0.toBitVec = fb + BitVec.ofNat 64 8 := (hm1.regs .X0 _ rfl).trans rfl
  have hx2 : s1.data.regs.X2.toNat = 1016 := by
    show (s1.data.regs.getXReg .X2).toBitVec.toNat = _
    rw [hm1.regs .X2 _ rfl]
    rfl
  have hpre1 : MemsetPre s1.data := by
    unfold MemsetPre
    rw [hx0, hx2]
    exact hfr1.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  refine call_then hpc1 hmemset hpre1 fun s2 hpc2 ⟨_, _, hsame2, hsv2⟩ ↦ ?_
  rw [hx0, hx2] at hsame2
  have hfr2 := hfr1.change hsame2 (fun p h ↦ .inr (inRange_frame_sub hS hF (by omega) h))
    (fun q hq j hj ↦ not_inRange_slot hS hF (by omega) (slots_le q hq) hj
      (.inl (by have := slots_ge q hq; omega)))
    (fun r hr _ ↦ hsv2.1 r hr) hsv2.2.1 hsv2.2.2
  have e2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23], s2.data.regs.getXReg r =
      s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hsv2.1 _ rfl
  have f19 : s2.data.regs.getXReg .X19 = m0.regs.getXReg .X0 :=
    (e2 .X19 (by simp)).trans (UInt64.toBitVec_inj.mp (hm1.regs .X19 _ rfl))
  have f20 : s2.data.regs.getXReg .X20 = m0.regs.getXReg .X1 :=
    (e2 .X20 (by simp)).trans (UInt64.toBitVec_inj.mp (hm1.regs .X20 _ rfl))
  have f21 : s2.data.regs.getXReg .X21 = m0.regs.getXReg .X2 :=
    (e2 .X21 (by simp)).trans (UInt64.toBitVec_inj.mp (hm1.regs .X21 _ rfl))
  have f22 : s2.data.regs.getXReg .X22 = m0.regs.getXReg .X3 :=
    (e2 .X22 (by simp)).trans (UInt64.toBitVec_inj.mp (hm1.regs .X22 _ rfl))
  have f23 : s2.data.regs.getXReg .X23 = m0.regs.getXReg .X4 :=
    (e2 .X23 (by simp)).trans (UInt64.toBitVec_inj.mp (hm1.regs .X23 _ rfl))
  have rg2 : Regs m0 s2.data := ⟨f19, f20, f21⟩
  have h21 : (s2.data.regs.getXReg .X21).toBitVec.toNat = cnt m0 := by
    rw [f21]
    rfl
  -- `b1`: more than 64 coefficients?
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b1Offset) := hpc2
  refine exec_at hk1 run_b1 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb1 := after_eq run_b1 ▸ regs_keeps b1 (.head _)
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb1.1 hb1.2
  have e3 : ∀ r, s3.data.regs.getXReg r = s2.data.regs.getXReg r := fun r ↦
    Match.reg_eq (match_nil _) hm3 (r := r) (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  have rg3 : Regs m0 s3.data :=
    ⟨(e3 .X19).trans rg2.x19, (e3 .X20).trans rg2.x20, (e3 .X21).trans rg2.x21⟩
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb1.2
  have hc1 : ((SBool.cmp .ult .W64 (.reg .X21) (.lit 64)).not.and
      (SBool.cmp .eq .W64 (.reg .X21) (.lit 64)).not).eval (Env.ofMachine s2.data []) =
      decide (64 < cnt m0) := by
    sym_simp
    rw [bv_ult_toNat, bv_beq_toNat, Env.ofMachine_regs, h21]
    by_cases h : 64 < cnt m0
    · simp [h]; omega
    · simp [h]; omega
  simp only [PcOk] at hpc3
  rw [hc1] at hpc3
  by_cases hc : 64 < cnt m0
  · -- too many coefficients: `None`
    simp only [hc, decide_true, ↓reduceIte] at hpc3
    rw [show Labels.label NativeRustcVmArm.Vm.NovelEval.label_10 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b15Offset) from hp.label (j := NativeRustcVmArm.Vm.NovelEval.b15Offset) NativeRustcVmArm.Vm.NovelEval.label_10_at] at hpc3
    have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk15 run_b15 (Env.wf_nil _) hpc3 (match_nil _) fun s4 hm4 hpc4 ↦ ?_
    have hb15 := after_eq run_b15 ▸ regs_keeps b15
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _
        (.head _))))))))))
    have hfr4 := hfr3.of_regs (match_nil _) hm4 (Env.wf_nil _) rfl hb15.1 hb15.2
    have h19 : s4.data.regs.X19 = m0.regs.X0 :=
      (Match.reg_eq (r := .X19) (match_nil _) hm4 rfl rfl).trans rg3.x19
    have h8 : s4.data.regs.X8 = 0 := UInt64.toBitVec_inj.mp (hm4.regs .X8 _ rfl)
    simp only [PcOk] at hpc4
    rw [show Labels.label NativeRustcVmArm.Vm.NovelEval.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b18Offset) from hp.label (j := NativeRustcVmArm.Vm.NovelEval.b18Offset) NativeRustcVmArm.Vm.NovelEval.label_13_at] at hpc4
    obtain ⟨hwf, hm⟩ := out_env hpre hfr4 h19
    have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk18 run_b18' hwf hpc4 hm fun s5 hm5 hpc5 ↦ .done _ ?_
    have hb18 := after_eq run_b18' ▸ b18'_restores
    obtain ⟨hsaved, hx30⟩ := hfr4.ret hm5 hwf x30_mem hb18.1
    refine ⟨hpc5.trans (by simp only [retOf, hx30]), ?_, out_same hpre hfr4 hwf hm5 hb18.2,
      hsaved⟩
    show OptEWAt _ _ (if m0.regs.X2.toNat ≤ laneCap then _ else _)
    simp only [show ¬m0.regs.X2.toNat ≤ laneCap from by unfold cnt at hc; unfold laneCap; omega,
      ↓reduceIte]
    have := Match.wordAt_write hm5 (r := 1) rfl (o := 0) (by decide) (v := .reg .X8) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    rw [show UInt64.ofBitVec ((Sym.reg .X8).eval
        (Env.ofMachine s4.data [(fbOf m0, 1120), (m0.regs.X0.toBitVec, 24)])) = s4.data.regs.X8
      from rfl, h8] at this
    exact this
  have hc64 : cnt m0 ≤ 64 := by omega
  simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc3
  -- `b2`: `basis[0] = 1`
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b2Offset) := hpc3
  let env4 := Env.ofMachine s3.data [(fb, 1120)]
  have hwf4 : env4.WF := wf_one (hfr3.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm4 : Match env4 frameS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr3.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk2 run_b2 hwf4 hpc3' hm4 fun s4 hm5 hpc4 ↦ ?_
  have hb2 := after_eq run_b2 ▸ b2_keeps
  have hfr4 := hfr3.of_block hm4 hm5 hwf4 rfl hb2.1 (r := 0) rfl (by decide) hb2.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 8) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq j hj ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 8) (by omega) (slots_le q hq) hj
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hbasis : NativeRustcVm.WordsAt s4.data.dmem (fbOf m0) (basisOf m0 0).toList := by
    rw [basisOf, novelPre_zero]
    have := Match.wordAt_write hm5 (r := 0) rfl (o := 0) (by decide) (v := .lit 1) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    exact NativeRustcVm.wordsAt_singleton.mpr this
  have e4 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23], s4.data.regs.getXReg r =
      s3.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm4 hm5 rfl rfl
  have rg4 : Regs m0 s4.data :=
    ⟨(e4 .X19 (by simp)).trans rg3.x19, (e4 .X20 (by simp)).trans rg3.x20,
      (e4 .X21 (by simp)).trans rg3.x21⟩
  have h24 : s4.data.regs.X24.toNat = (basisOf m0 0).size := by
    show (s4.data.regs.getXReg .X24).toBitVec.toNat = _
    rw [hm5.regs .X24 _ rfl, basisOf, novelPre_zero]
    rfl
  have hc2 : (SBool.cmp .ult .W64 (.reg .X21) (.lit 2)).eval env4 = decide (cnt m0 < 2) := by
    sym_simp
    rw [bv_ult_toNat, Env.ofMachine_regs, e3, h21]
    rfl
  simp only [PcOk] at hpc4
  rw [hc2] at hpc4
  have hsz0 : (basisOf m0 0).size = 1 := by rw [basisOf, novelPre_zero]; rfl
  by_cases hc1 : cnt m0 < 2
  · -- the basis `[1]` is complete
    simp only [hc1, decide_true, ↓reduceIte] at hpc4
    rw [show Labels.label NativeRustcVmArm.Vm.NovelEval.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset) from hp.label (j := NativeRustcVmArm.Vm.NovelEval.b9Offset) NativeRustcVmArm.Vm.NovelEval.label_7_at] at hpc4
    have hst : basisOf m0 (wn m0) = basisOf m0 0 :=
      novelPre_stable (whatOf m0) (count := cnt m0) (j := 0) (by unfold basisOf at hsz0; omega)
        (wn m0) (Nat.zero_le _)
    obtain ⟨d, pc⟩ := s4
    simp only at hpc4
    subst hpc4
    exact from_mid hp hkmul hpre hc64 ⟨hfr4, rg4, by rw [hst]; exact h24, by rw [hst]; exact hbasis⟩
  simp only [hc1, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b3`: the `What`s' end
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b3Offset) := hpc4
  refine exec_at hk3 run_b3 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm6 hpc5 ↦ ?_
  have hb3 := after_eq run_b3 ▸ regs_keeps b3 (.tail _ (.head _))
  have hfr5 := hfr4.of_regs (match_nil _) hm6 (Env.wf_nil _) rfl hb3.1 hb3.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm6.dmem_eq (Env.wf_nil _) hb3.2
  have e5 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22], s5.data.regs.getXReg r =
      s4.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm6 rfl rfl
  have hI0 : OInv m0 0 s5.data := by
    refine ⟨hfr5, ⟨(e5 .X19 (by simp)).trans rg4.x19, (e5 .X20 (by simp)).trans rg4.x20,
      (e5 .X21 (by simp)).trans rg4.x21⟩, Nat.zero_le _, by omega, ?_, ?_, ?_, hd5 ▸ hbasis⟩
    · show (s5.data.regs.getXReg .X22).toBitVec = _
      rw [e5 .X22 (by simp), e4 .X22 (by simp), e3, f22]
      show m0.regs.X3.toBitVec = _
      simp
    · refine (hm6.regs .X25 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs, Env.ofMachine_regs, e4 .X22 (by simp), e4 .X23 (by simp), e3, e3,
        f22, f23, shl3_eq]
      rfl
    · show (s5.data.regs.getXReg .X24).toBitVec.toNat = _
      rw [hm6.regs .X24 _ rfl, hsz0]
      rfl
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b4Offset) := hpc5
  -- the doubling loop
  have hloop := Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Mid m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b9Offset))
    (fun n s ↦ ∃ j, n = wn m0 - j ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b4Offset) ∧ OInv m0 j s.data)
    (fun n s ⟨j, hn', hpc, hI'⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (outer_step hp hkmul hpre hc64 hI').mono fun s' h ↦ ?_
      rcases h with h | ⟨hI'', hpc'⟩
      · exact .inl h
      · exact .inr ⟨wn m0 - (j + 1), by have := hI''.hj; omega, j + 1, rfl, hpc', hI''⟩)
    (n := wn m0) ⟨0, by omega, hpc5', hI0⟩
  refine hloop.bind fun s ⟨hM, hpc⟩ ↦ ?_
  obtain ⟨d, pc⟩ := s
  simp only at hpc
  subst hpc
  exact from_mid hp hkmul hpre hc64 hM

end

end NativeRustcVmArm.Whir.NovelEval
