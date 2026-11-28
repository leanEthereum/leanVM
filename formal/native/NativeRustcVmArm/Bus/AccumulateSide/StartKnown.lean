module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Bus.AccumulateSide.StartKit

/-!
# `accumulate_side` up to the table loop: the entry and the known part

`b0` saves the registers and the arguments and branches on the known part's count `cK` (the
fewer of the framework blocks and the fingerprints): `start0`. For each of the first `cK`
framework blocks, its selector (`eq_eval_fn`) times `side_beta` plus its fingerprint (`EW::mul`)
added to the known part: `b1` to `b14` (`known`), leaving the known part in X19, X28 at `b15`.
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

theorem ev_ite [Labels] (env : Env) (c : SBool) (a b : Sym) :
    (Sym.ite c a b).eval env = if c.eval env then a.eval env else b.eval env := rfl

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

theorem wfE (h : Pre L rows bl Fm SL m0) : (Env.ofMachine m0 (rsE m0)).WF :=
  wfB h (m := m0) (fun _ h ↦ h) (.inr rfl) (rs := [(m0.regs.X6.toBitVec, busLayoutBytes)])
    (fun e he ↦ by
      rw [List.mem_singleton.mp he]
      exact ⟨by show 0 < busLayoutBytes; decide, h.slOk.1, h.slOk.2, fun _ ↦ h.slArgs⟩)
    (List.pairwise_singleton _ _)

theorem matchE (h : Pre L rows bl Fm SL m0) : Match (Env.ofMachine m0 (rsE m0)) s0 m0 :=
  match_ofMachine (sregions := [(12168, true), (888, false)]) (regions := rsE m0)
    ⟨rfl, fun _ ↦ Bus.base_aligned h.stack (by decide) rfl, busLayoutBytes_eq.symm, nofun,
      trivial⟩
    (by rw [ptr_eval (rs := rsE m0) (oi := 12096) (o := 12096) rfl rfl]
        exact (base_add_eq (m0 := m0) (F := F)).symm)
    ⟨by dsimp only; rw [ptr_eval (rs := rsE m0) (oi := 0) (o := 0) rfl rfl, add_zero']; rfl,
      trivial⟩
    trivial trivial trivial

omit [Labels] in
/-- The known part over one framework block. -/
theorem kn_one : kn SL m0 1 = 0 + term SL m0 0 := knownN_succ _ _ _ _ 0

omit [Labels] in
theorem kn_two : kn SL m0 2 = kn SL m0 1 + term SL m0 1 := knownN_succ _ _ _ _ 1

omit [Labels] in
theorem kn_three : kn SL m0 3 = kn SL m0 2 + term SL m0 2 := knownN_succ _ _ _ _ 2

theorem cK_le (h : Pre L rows bl Fm SL m0) : cK SL m0 ≤ 3 :=
  Nat.le_trans (Nat.min_le_left _ _) (fw_le h)

end

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-! ## `b0` -/

/-- **`b0`**: the prologue; the arguments kept; `cK` zero or not. -/
theorem start0 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) {R : MachineState → Prop}
    (c1 : ∀ m, St m0 (TT SL m0 L rows bl Fm 0) QA m →
      FormsAt m.dmem m0.regs.X1.toBitVec Fm → 0 < cK SL m0 →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b1Offset)⟩)
    (c5 : ∀ m, St m0 (TT SL m0 L rows bl Fm 0) QA m →
      FormsAt m.dmem m0.regs.X1.toBitVec Fm → cK SL m0 = 0 →
      Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b5Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b0Offset)⟩ := by
  have hwf := wfE h
  refine exec_then (b0_in_code.trans hp.1 (by simp [b0])) run_b0 hwf (matchE h)
    fun st hm' hpc ↦ ?_
  have hfr : Fr m0 F N slots keep (outs m0) st.data :=
    Bus.Fr.ofPrologue' (A := 72) h.stack.2.1 (by decide) hm' hwf rfl (by decide) slots_le
      (by decide) (fun _ h ↦ nomatch h)
  have ev8 : (Sym.load 1 8 8).eval (Env.ofMachine m0 (rsE m0)) = (sv m0 17).toBitVec := by
    rw [load_rk rfl]
    rfl
  have ev0 : (Sym.load 0 12096 8).eval (Env.ofMachine m0 (rsE m0)) = (sv m0 16).toBitVec :=
    congrArg UInt64.toBitVec (argT (st := m0) [(m0.regs.X6.toBitVec, busLayoutBytes)] 0
      fun _ _ ↦ rfl)
  have hlt4 : SBool.eval (Env.ofMachine m0 (rsE m0)) (.cmp .ult .W64 (.load 1 8 8) (.lit 4)) =
      true := by
    rw [cmp_ult_lit _ ev8 (by decide)]
    have := sv17 h
    have := fw_le h
    simp only [decide_eq_true_eq]
    omega
  have x22 : (Sym.ite (.cmp .ult .W64 (.load 1 8 8) (.lit 4)) (.load 1 8 8) (.lit 0)).eval
      (Env.ofMachine m0 (rsE m0)) = (sv m0 17).toBitVec := by
    rw [ev_ite, hlt4, ite_eq_left_of_eq_true _ _ (eq_true rfl), ev8]
  have x21 : (Sym.ite (.cmp .ult .W64 (.load 1 8 8) (.lit 4)) (.ptr 1 16) (.lit 8)).eval
      (Env.ofMachine m0 (rsE m0)) = (sv m0 18).toBitVec := by
    rw [ev_ite, hlt4, ite_eq_left_of_eq_true _ _ (eq_true rfl), ptr_eval (rs := rsE m0) (oi := 16) (o := 16) rfl rfl]
    rfl
  have x20 : (Sym.ite (.cmp .ult .W64 (.load 0 12096 8)
      (.ite (.cmp .ult .W64 (.load 1 8 8) (.lit 4)) (.load 1 8 8) (.lit 0))) (.load 0 12096 8)
      (.ite (.cmp .ult .W64 (.load 1 8 8) (.lit 4)) (.load 1 8 8) (.lit 0))).eval
      (Env.ofMachine m0 (rsE m0)) = (sv m0 19).toBitVec := by
    rw [ev_ite, cmp_ult _ ev0 x22, x22, ev0]
    show (if decide ((stackArg m0 0).toNat < (sv m0 17).toNat) = true then
      (stackArg m0 0).toBitVec else (sv m0 17).toBitVec) =
      (if (stackArg m0 0).toNat < (sv m0 17).toNat then stackArg m0 0 else sv m0 17).toBitVec
    by_cases hc : (stackArg m0 0).toNat < (sv m0 17).toNat <;> simp [hc]
  have hA : Holds (rsE m0) (sv m0) (QAr ++ QAe) st.data := by
    refine Holds.append (Holds.after (sz := [12168, 888])
      (by show [F + 72, busLayoutBytes] = [12168, 888]; rw [busLayoutBytes_eq]) holds_QE hm'
      (by decide)) ?_
    intro p hp
    simp only [QAe, List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · rw [tval_reg_of hm' rfl, x20, UInt64.ofBitVec_toBitVec]
    · rw [tval_reg_of hm' rfl, x21, UInt64.ofBitVec_toBitVec]
    · rw [tval_reg_of hm' rfl, x22, UInt64.ofBitVec_toBitVec]
  have hlt : ∀ p ∈ QA, p.2 < 30 := by decide
  have hst : St m0 (TT SL m0 L rows bl Fm 0) QA st.data :=
    ⟨hfr, Holds.congrV (Holds.reg0 hA (by decide) rfl) fun p hp ↦ (TT_sv (hlt p hp)).symm⟩
  have hF := forms_block h (.inr rfl) hm' hwf (by decide) h.forms
  have he := cmp_eq_lit _ x20 (by decide : 0 < 2 ^ 64)
  rw [sv19 h] at he
  simp only [PcOk, he] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b5Offset) NativeRustcVmArm.Vm.AccumulateSide.label_3_at,
    show k + NativeRustcVmArm.Vm.AccumulateSide.b0Offset + b0.length = k + NativeRustcVmArm.Vm.AccumulateSide.b1Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b0_next]] at hpc
  by_cases hc : cK SL m0 = 0
  · exact Gkr.at_pc (by simpa [hc] using hpc) (c5 st.data hst hF hc)
  · exact Gkr.at_pc (by simpa [hc] using hpc) (c1 st.data hst hF (by omega))

/-! ## The known part -/

/-- **`b1`**: framework block `0`'s selector. -/
theorem k1 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hc : 0 < cK SL m0) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QA m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q2 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b2Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b1Offset)⟩ := by
  have hfr := hst.fr
  have hn : 0 < nA m0 := Nat.lt_of_lt_of_le hc (Nat.min_le_right _ _)
  have hfw : 0 < SL.framework.size := Nat.lt_of_lt_of_le hc (Nat.min_le_left _ _)
  have hwf := wf2 h hfr.kept (rok_sl h (n := 64) (by decide) (by decide))
    (rok_fp h (c := 1) (by omega) (by decide) : ROk m0 0 (m0.regs.X7.toBitVec, 16))
    (ap_sl_fp h (n := 64) (c := 1) (by decide) (by omega) (by decide))
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 16)]) (TT SL m0 L rows bl Fm 0)
      ((.ptr 1 16, 18) :: (.ptr 2 0, 7) :: QA) m := by
    refine Holds.cons (Holds.cons (St.lift hst (by decide) 0 _) ?_) ?_
    · unfold tval
      rw [ptr_eval (oi := 0) (o := 0) rfl rfl, add_zero', TT_sv (by decide)]
      rfl
    · unfold tval
      rw [ptr_eval (oi := 16) (o := 16) rfl rfl, TT_sv (by decide)]
      rfl
  have h21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 16 := by
    rw [Holds.regv hst.hd (r := .X21) (i := 18) (by decide), TT_sv (by decide)]
    rfl
  have h7 : (m.regs.getXReg .X7).toBitVec = m0.regs.X7.toBitVec := by
    rw [Holds.regv hst.hd (r := .X7) (i := 7) (by decide), TT_sv (by decide)]
    rfl
  obtain ⟨hv1, hv2, hw0, hw1⟩ := fw_p h (i := 0) hfw
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw0 hw1
  refine St.eqCall h hee (.inl rfl) (rs := [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 16)])
    (sz := [12096, 64, 16]) rfl (b1_in_code.trans hp.1 (by simp [b1])) run_b1 hfr hH0 hwf
    (matchRR h hfr.sp h21 h7) rfl (by decide) (D' := Q1r) (E := Q1e) (by decide) (by decide)
    (fun st hm' ↦ ?_) (by decide) (n := .reg .X25) (pa := .reg .X28) (z := .lit 8)
    (vs := .load 1 16 8) (is := .load 1 24 8) (p := SL.framework[0]'hfw) rfl rfl rfl rfl ?_ ?_
    rfl ?_ ?_ fun m2 hst2 hret hKF _ ↦ ?_
  · intro p hp'
    simp only [Q1e, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl, load_rk rfl, UInt64.ofBitVec_toBitVec,
        fp_word h hfr hn (o := 0) (by omega)]
      exact fp_c0 (i := 0) hn
    · rw [tval_reg_of hm' rfl, load_rk rfl, UInt64.ofBitVec_toBitVec,
        fp_word h hfr hn (o := 8) (by omega)]
      exact fp_c1 (i := 0) hn
  · rw [Holds.evc hH0 (s := .reg .X25) (i := 13) (by decide), TT_sv (by decide)]
    rfl
  · rw [Holds.evc hH0 (s := .reg .X28) (i := 12) (by decide), TT_sv (by decide)]
    rfl
  · rw [load_rk rfl, sl_word h hfr (o := 16) (by decide), hw0, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv1]
  · rw [load_rk rfl, sl_word h hfr (o := 24) (by decide), hw1, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv2]
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b1Offset + b1.length = k + NativeRustcVmArm.Vm.AccumulateSide.b2Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b1_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 40) (x := sel SL m0 0) ?_
      rfl rfl) (by decide)⟩ (hKF _ hF)
    rw [hret]
    show _ = eqAbove (SL.framework.getD 0 default) (ptA m0)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfw, Option.getD_some]

/-- **`b2`**: term `0`. -/
theorem k2 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q2 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q3 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b3Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b2Offset)⟩ := by
  have hH0 := St.lift (D := Q2) hst (by decide) 0 []
  refine St.mulCall h hmul (.inl rfl) (rs := []) (sz := [12096]) rfl
    (b2_in_code.trans hp.1 (by simp [b2])) run_b2 hst.fr hH0 (wf0 h hst.fr.kept)
    (matchF h hst.fr.sp) rfl (by decide) (D' := Q1r) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) (by decide) fun st m2 hm' hst2 hret hKF _ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b2Offset + b2.length = k + NativeRustcVmArm.Vm.AccumulateSide.b3Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b2_next]]
  have e0 := argv (sz := [12096]) rfl hH0 hm' (r := .X0) (a := 40) (by decide)
  have e1 := argv (sz := [12096]) rfl hH0 hm' (r := .X1) (a := 41) (by decide)
  have e2 := reg_eor hH0 hm' (r := .X2) rfl (i := 30) (j := 10) (by decide) (by decide)
  have e3 := reg_eor hH0 hm' (r := .X3) rfl (i := 31) (j := 11) (by decide) (by decide)
  refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 50) (x := term SL m0 0) ?_
    rfl rfl) (by decide)⟩ (hKF _ hF)
  rw [hret]
  exact mul_eq e0 e1 e2 e3

/-- **`b3`**: the known part over one block; `cK` one or more. -/
theorem k3 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q3 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (c4 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q4 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → cK SL m0 = 1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b4Offset)⟩)
    (c7 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q4 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → cK SL m0 ≠ 1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b7Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b3Offset)⟩ := by
  have hH0 := St.lift (D := Q3) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b3_in_code.trans hp.1 (by simp [b3])) run_b3 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q3r) (E := [(.reg .X19, 60), (.reg .X28, 61)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X19 = _
      refine (reg_of hH0 hm' rfl (i := 50) (by decide)).trans ?_
      show (term SL m0 0).c0 = (kn SL m0 1).c0
      rw [kn_one, add_c0, c0_zero, UInt64.zero_xor]
    · change st.regs.getXReg .X28 = _
      refine (reg_of hH0 hm' rfl (i := 51) (by decide)).trans ?_
      show (term SL m0 0).c1 = (kn SL m0 1).c1
      rw [kn_one, add_c1, c1_zero, UInt64.zero_xor]
  · have he := cmp_eq_lit _ (Holds.evc hH0 (s := .reg .X20) (i := 19) (by decide))
      (by decide : 1 < 2 ^ 64)
    rw [TT_sv (by decide), sv19 h] at he
    have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)])
        (.not (.cmp .eq .W64 (.reg .X20) (.lit 1))) = !decide (cK SL m0 = 1) := by
      show (!SBool.eval _ _) = _
      rw [he]
    simp only [PcOk, hc] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b7Offset) NativeRustcVmArm.Vm.AccumulateSide.label_5_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b3Offset + b3.length = k + NativeRustcVmArm.Vm.AccumulateSide.b4Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b3_next]] at hpc
    have hF' := forms_wrOk h (.inl rfl) hm' hwf (by decide) hF
    have hst2 : St m0 (TT SL m0 L rows bl Fm 0) Q4 st.data := ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    by_cases h1 : cK SL m0 = 1
    · exact Gkr.at_pc (by simpa [h1] using hpc) (c4 _ hst2 hF' h1)
    · exact Gkr.at_pc (by simpa [h1] using hpc) (c7 _ hst2 hF' h1)

/-- **`b4`**: one block: on to `b15`. -/
theorem k4 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (h1 : cK SL m0 = 1)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q4 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q15 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b4Offset)⟩ := by
  have hH0 : Holds [(base m0 F, F + 0)] (TT SL m0 L rows bl Fm 0)
      ((.reg .X19, 66) :: (.reg .X28, 67) :: Q4) m := by
    refine Holds.dup (Holds.dup (St.lift hst (by decide) 0 []) (i := 61) (by decide) ?_)
      (i := 60) (by decide) ?_
    · show (kn SL m0 1).c1 = (kn SL m0 (cK SL m0)).c1
      rw [h1]
    · show (kn SL m0 1).c0 = (kn SL m0 (cK SL m0)).c0
      rw [h1]
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b4_in_code.trans hp.1 (by simp [b4])) run_b4 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q15) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  simp only [PcOk] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b15Offset) NativeRustcVmArm.Vm.AccumulateSide.label_9_at] at hpc
  exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **`b7`**: framework block `1`'s selector. -/
theorem k7 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hc : 2 ≤ cK SL m0) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q4 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q8 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b8Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b7Offset)⟩ := by
  have hfr := hst.fr
  have hn : 2 ≤ nA m0 := Nat.le_trans hc (Nat.min_le_right _ _)
  have hfw : 1 < SL.framework.size := Nat.lt_of_lt_of_le hc (Nat.min_le_left _ _)
  have hwf := wf2 h hfr.kept (rok_sl h (n := 64) (by decide) (by decide))
    (rok_fp h (c := 2) hn (by decide) : ROk m0 0 (m0.regs.X7.toBitVec, 32))
    (ap_sl_fp h (n := 64) (c := 2) (by decide) hn (by decide))
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 32)]) (TT SL m0 L rows bl Fm 0)
      ((.ptr 1 16, 18) :: (.ptr 2 0, 7) :: Q4) m := by
    refine Holds.cons (Holds.cons (St.lift hst (by decide) 0 _) ?_) ?_
    · unfold tval
      rw [ptr_eval (oi := 0) (o := 0) rfl rfl, add_zero', TT_sv (by decide)]
      rfl
    · unfold tval
      rw [ptr_eval (oi := 16) (o := 16) rfl rfl, TT_sv (by decide)]
      rfl
  have h21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 16 := by
    rw [Holds.regv hst.hd (r := .X21) (i := 18) (by decide), TT_sv (by decide)]
    rfl
  have h26 : (m.regs.getXReg .X26).toBitVec = m0.regs.X7.toBitVec := by
    rw [Holds.regv hst.hd (r := .X26) (i := 7) (by decide), TT_sv (by decide)]
    rfl
  obtain ⟨hv1, hv2, hw0, hw1⟩ := fw_p h (i := 1) hfw
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw0 hw1
  refine St.eqCall h hee (.inl rfl) (rs := [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 32)])
    (sz := [12096, 64, 32]) rfl (b7_in_code.trans hp.1 (by simp [b7])) run_b7 hfr hH0 hwf
    (matchRR h hfr.sp h21 h26) rfl (by decide) (D' := Q7r) (E := Q7e) (by decide) (by decide)
    (fun st hm' ↦ ?_) (by decide) (n := .reg .X25) (pa := .reg .X24) (z := .lit 8)
    (vs := .load 1 32 8) (is := .load 1 40 8) (p := SL.framework[1]'hfw) rfl rfl rfl rfl ?_ ?_
    rfl ?_ ?_ fun m2 hst2 hret hKF _ ↦ ?_
  · intro p hp'
    simp only [Q7e, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl, load_rk rfl, UInt64.ofBitVec_toBitVec,
        fp_word h hfr (by omega) (o := 24) (by omega)]
      exact fp_c1 (i := 1) (by omega)
    · rw [tval_write hm' rfl rfl (by decide) (v := .load 2 16 8) (by decide), load_rk rfl,
        UInt64.ofBitVec_toBitVec, fp_word h hfr (by omega) (o := 16) (by omega)]
      exact fp_c0 (i := 1) (by omega)
  · rw [Holds.evc hH0 (s := .reg .X25) (i := 13) (by decide), TT_sv (by decide)]
    rfl
  · rw [Holds.evc hH0 (s := .reg .X24) (i := 12) (by decide), TT_sv (by decide)]
    rfl
  · rw [load_rk rfl, sl_word h hfr (o := 32) (by decide), hw0, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv1]
  · rw [load_rk rfl, sl_word h hfr (o := 40) (by decide), hw1, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv2]
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b7Offset + b7.length = k + NativeRustcVmArm.Vm.AccumulateSide.b8Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b7_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 42) (x := sel SL m0 1) ?_
      rfl rfl) (by decide)⟩ (hKF _ hF)
    rw [hret]
    show _ = eqAbove (SL.framework.getD 1 default) (ptA m0)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfw, Option.getD_some]

/-- **`b8`**: term `1`. -/
theorem k8 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q8 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q9 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b9Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b8Offset)⟩ := by
  have hH0 := St.lift (D := Q8) hst (by decide) 0 []
  refine St.mulCall h hmul (.inl rfl) (rs := []) (sz := [12096]) rfl
    (b8_in_code.trans hp.1 (by simp [b8])) run_b8 hst.fr hH0 (wf0 h hst.fr.kept)
    (matchF h hst.fr.sp) rfl (by decide) (D' := Q7r) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) (by decide) fun st m2 hm' hst2 hret hKF _ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b8Offset + b8.length = k + NativeRustcVmArm.Vm.AccumulateSide.b9Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b8_next]]
  have e0 := argv (sz := [12096]) rfl hH0 hm' (r := .X0) (a := 42) (by decide)
  have e1 := argv (sz := [12096]) rfl hH0 hm' (r := .X1) (a := 43) (by decide)
  have e2 := reg_eor hH0 hm' (r := .X2) rfl (i := 32) (j := 10) (by decide) (by decide)
  have e3 := reg_eor hH0 hm' (r := .X3) rfl (i := 33) (j := 11) (by decide) (by decide)
  refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 52) (x := term SL m0 1) ?_
    rfl rfl) (by decide)⟩ (hKF _ hF)
  rw [hret]
  exact mul_eq e0 e1 e2 e3

/-- **`b9`**: the known part over two blocks; `cK` two or three. -/
theorem k9 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q9 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (c10 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q10 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → cK SL m0 = 2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b10Offset)⟩)
    (c11 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q10 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → cK SL m0 ≠ 2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b11Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b9Offset)⟩ := by
  have hH0 := St.lift (D := Q9) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b9_in_code.trans hp.1 (by simp [b9])) run_b9 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q9r) (E := [(.reg .X19, 62), (.reg .X28, 63)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X19 = _
      refine (reg_eor hH0 hm' rfl (i := 52) (j := 60) (by decide) (by decide)).trans ?_
      show (term SL m0 1).c0 ^^^ (kn SL m0 1).c0 = (kn SL m0 2).c0
      rw [kn_two, add_c0]
      exact UInt64.xor_comm _ _
    · change st.regs.getXReg .X28 = _
      refine (reg_eor hH0 hm' rfl (i := 53) (j := 61) (by decide) (by decide)).trans ?_
      show (term SL m0 1).c1 ^^^ (kn SL m0 1).c1 = (kn SL m0 2).c1
      rw [kn_two, add_c1]
      exact UInt64.xor_comm _ _
  · have he := cmp_eq_lit _ (Holds.evc hH0 (s := .reg .X20) (i := 19) (by decide))
      (by decide : 2 < 2 ^ 64)
    rw [TT_sv (by decide), sv19 h] at he
    have hc : SBool.eval (Env.ofMachine m [(base m0 F, F + 0)])
        (.not (.cmp .eq .W64 (.reg .X20) (.lit 2))) = !decide (cK SL m0 = 2) := by
      show (!SBool.eval _ _) = _
      rw [he]
    simp only [PcOk, hc] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b11Offset) NativeRustcVmArm.Vm.AccumulateSide.label_7_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b9Offset + b9.length = k + NativeRustcVmArm.Vm.AccumulateSide.b10Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b9_next]] at hpc
    have hF' := forms_wrOk h (.inl rfl) hm' hwf (by decide) hF
    have hst2 : St m0 (TT SL m0 L rows bl Fm 0) Q10 st.data :=
      ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    by_cases h2 : cK SL m0 = 2
    · exact Gkr.at_pc (by simpa [h2] using hpc) (c10 _ hst2 hF' h2)
    · exact Gkr.at_pc (by simpa [h2] using hpc) (c11 _ hst2 hF' h2)

/-- **`b10`**: two blocks: on to `b14`. -/
theorem k10 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (h2 : cK SL m0 = 2)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q10 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q14 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b14Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b10Offset)⟩ := by
  have hH0 : Holds [(base m0 F, F + 0)] (TT SL m0 L rows bl Fm 0)
      ((.reg .X19, 66) :: (.reg .X28, 67) :: Q10) m := by
    refine Holds.dup (Holds.dup (St.lift hst (by decide) 0 []) (i := 63) (by decide) ?_)
      (i := 62) (by decide) ?_
    · show (kn SL m0 2).c1 = (kn SL m0 (cK SL m0)).c1
      rw [h2]
    · show (kn SL m0 2).c0 = (kn SL m0 (cK SL m0)).c0
      rw [h2]
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b10_in_code.trans hp.1 (by simp [b10])) run_b10 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q14) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  simp only [PcOk] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b14Offset) NativeRustcVmArm.Vm.AccumulateSide.label_8_at] at hpc
  exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **`b11`**: framework block `2`'s selector. -/
theorem k11 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hc : 3 ≤ cK SL m0) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q10 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q12 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b12Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b11Offset)⟩ := by
  have hfr := hst.fr
  have hn : 3 ≤ nA m0 := Nat.le_trans hc (Nat.min_le_right _ _)
  have hfw : 2 < SL.framework.size := Nat.lt_of_lt_of_le hc (Nat.min_le_left _ _)
  have hwf := wf2 h hfr.kept (rok_sl h (n := 64) (by decide) (by decide))
    (rok_fp h (c := 3) hn (by decide) : ROk m0 0 (m0.regs.X7.toBitVec, 48))
    (ap_sl_fp h (n := 64) (c := 3) (by decide) hn (by decide))
  have hH0 : Holds ((base m0 F, F + 0) ::
      [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 48)]) (TT SL m0 L rows bl Fm 0)
      ((.ptr 1 16, 18) :: Q10) m := by
    refine Holds.cons (St.lift hst (by decide) 0 _) ?_
    unfold tval
    rw [ptr_eval (oi := 16) (o := 16) rfl rfl, TT_sv (by decide)]
    rfl
  have h21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 16 := by
    rw [Holds.regv hst.hd (r := .X21) (i := 18) (by decide), TT_sv (by decide)]
    rfl
  have h26 : (m.regs.getXReg .X26).toBitVec = m0.regs.X7.toBitVec := by
    rw [Holds.regv hst.hd (r := .X26) (i := 7) (by decide), TT_sv (by decide)]
    rfl
  obtain ⟨hv1, hv2, hw0, hw1⟩ := fw_p h (i := 2) hfw
  simp only [Nat.reduceMul, Nat.reduceAdd] at hw0 hw1
  refine St.eqCall h hee (.inl rfl) (rs := [(m0.regs.X6.toBitVec, 64), (m0.regs.X7.toBitVec, 48)])
    (sz := [12096, 64, 48]) rfl (b11_in_code.trans hp.1 (by simp [b11])) run_b11 hfr hH0 hwf
    (matchRR h hfr.sp h21 h26) rfl (by decide) (D' := Q11r) (E := Q11e) (by decide)
    (by decide) (fun st hm' ↦ ?_) (by decide) (n := .reg .X25) (pa := .reg .X24) (z := .lit 8)
    (vs := .load 1 48 8) (is := .load 1 56 8) (p := SL.framework[2]'hfw) rfl rfl rfl rfl ?_ ?_
    rfl ?_ ?_ fun m2 hst2 hret hKF _ ↦ ?_
  · intro p hp'
    simp only [Q11e, List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl, load_rk rfl, UInt64.ofBitVec_toBitVec,
        fp_word h hfr (by omega) (o := 32) (by omega)]
      exact fp_c0 (i := 2) (by omega)
    · rw [tval_reg_of hm' rfl, load_rk rfl, UInt64.ofBitVec_toBitVec,
        fp_word h hfr (by omega) (o := 40) (by omega)]
      exact fp_c1 (i := 2) (by omega)
  · rw [Holds.evc hH0 (s := .reg .X25) (i := 13) (by decide), TT_sv (by decide)]
    rfl
  · rw [Holds.evc hH0 (s := .reg .X24) (i := 12) (by decide), TT_sv (by decide)]
    rfl
  · rw [load_rk rfl, sl_word h hfr (o := 48) (by decide), hw0, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv1]
  · rw [load_rk rfl, sl_word h hfr (o := 56) (by decide), hw1, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv2]
  · rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b11Offset + b11.length = k + NativeRustcVmArm.Vm.AccumulateSide.b12Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b11_next]]
    refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 44) (x := sel SL m0 2) ?_
      rfl rfl) (by decide)⟩ (hKF _ hF)
    rw [hret]
    show _ = eqAbove (SL.framework.getD 2 default) (ptA m0)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hfw, Option.getD_some]

/-- **`b12`**: term `2`. -/
theorem k12 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q12 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q13 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b13Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b12Offset)⟩ := by
  have hH0 := St.lift (D := Q12) hst (by decide) 0 []
  refine St.mulCall h hmul (.inl rfl) (rs := []) (sz := [12096]) rfl
    (b12_in_code.trans hp.1 (by simp [b12])) run_b12 hst.fr hH0 (wf0 h hst.fr.kept)
    (matchF h hst.fr.sp) rfl (by decide) (D' := Q12r) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) (by decide) fun st m2 hm' hst2 hret hKF _ ↦ ?_
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b12Offset + b12.length = k + NativeRustcVmArm.Vm.AccumulateSide.b13Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b12_next]]
  have e0 := argv (sz := [12096]) rfl hH0 hm' (r := .X0) (a := 44) (by decide)
  have e1 := argv (sz := [12096]) rfl hH0 hm' (r := .X1) (a := 45) (by decide)
  have e2 := reg_eor hH0 hm' (r := .X2) rfl (i := 34) (j := 10) (by decide) (by decide)
  have e3 := reg_eor hH0 hm' (r := .X3) rfl (i := 35) (j := 11) (by decide) (by decide)
  refine cont m2 ⟨hst2.fr, Holds.sub (holds_ewRet hst2.hd (r0 := 54) (x := term SL m0 2) ?_
    rfl rfl) (by decide)⟩ (hKF _ hF)
  rw [hret]
  exact mul_eq e0 e1 e2 e3

/-- **`b13`**: the known part over three blocks. -/
theorem k13 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (h3 : cK SL m0 = 3)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q13 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q14 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b14Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b13Offset)⟩ := by
  have hH0 := St.lift (D := Q13) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b13_in_code.trans hp.1 (by simp [b13])) run_b13 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q13r) (E := [(.reg .X19, 66), (.reg .X28, 67)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X19 = _
      refine (reg_eor hH0 hm' rfl (i := 54) (j := 62) (by decide) (by decide)).trans ?_
      show (term SL m0 2).c0 ^^^ (kn SL m0 2).c0 = (kn SL m0 (cK SL m0)).c0
      rw [h3, kn_three, add_c0]
      exact UInt64.xor_comm _ _
    · change st.regs.getXReg .X28 = _
      refine (reg_eor hH0 hm' rfl (i := 55) (j := 63) (by decide) (by decide)).trans ?_
      show (term SL m0 2).c1 ^^^ (kn SL m0 2).c1 = (kn SL m0 (cK SL m0)).c1
      rw [h3, kn_three, add_c1]
      exact UInt64.xor_comm _ _
  · simp only [PcOk] at hpc
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b13Offset + b13.length = k + NativeRustcVmArm.Vm.AccumulateSide.b14Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b13_next]] at hpc
    exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **`b14`**: the tree's high limb back in X29. -/
theorem k14 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q14 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q15 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b14Offset)⟩ := by
  have hH0 := St.lift (D := Q14) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b14_in_code.trans hp.1 (by simp [b14])) run_b14 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := Q15) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  simp only [PcOk] at hpc
  rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b14Offset + b14.length = k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b14_next]] at hpc
  exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **The known part**: from `b1` to `b15`, `cK` blocks. -/
theorem known (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hmul : Spec (Labels.label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    (hc : 0 < cK SL m0) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QA m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q15 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b1Offset)⟩ := by
  have h3 := cK_le h
  refine k1 hp h hee hc hst hF fun m2 hs2 hF2 ↦ k2 hp h hmul hs2 hF2 fun m3 hs3 hF3 ↦
    k3 hp h hs3 hF3 (fun m4 hs4 hF4 h1 ↦ k4 hp h h1 hs4 hF4 cont)
      fun m4 hs4 hF4 h1 ↦ k7 hp h hee (by omega) hs4 hF4 fun m5 hs5 hF5 ↦
        k8 hp h hmul hs5 hF5 fun m6 hs6 hF6 ↦ k9 hp h hs6 hF6
          (fun m7 hs7 hF7 h2 ↦ k10 hp h h2 hs7 hF7 fun m8 hs8 hF8 ↦ k14 hp h hs8 hF8 cont)
          fun m7 hs7 hF7 h2 ↦ k11 hp h hee (by omega) hs7 hF7 fun m8 hs8 hF8 ↦
            k12 hp h hmul hs8 hF8 fun m9 hs9 hF9 ↦ k13 hp h (by omega) hs9 hF9
              fun m10 hs10 hF10 ↦ k14 hp h hs10 hF10 cont

end

end NativeRustcVmArm.Bus.AccumulateSide
