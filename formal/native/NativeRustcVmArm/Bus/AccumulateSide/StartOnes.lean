module

public import NativeRustcVmArm.Code.Vm.AccumulateSide.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Bus.AccumulateSide.StartKnown

/-!
# `accumulate_side` up to the table loop: the tree's value plus the known part, the ones

`b15` (after the known part) and `b5` (none) leave the tree's value plus the known part in X29
and the frame word at `32`, the weights at `88`, `96` (`QO`), and branch on the framework's
count. For each framework block, its selector added to the ones (`b6`, `b16` to `b21`): the ones
over the framework in X25, X20 at `b22` (`QZ`).
-/

namespace NativeRustcVmArm.Bus.AccumulateSide

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.AccumulateSide
open NativeVm.Model NativeRustcVmArm.Ring NativeRustcVm.Bus NativeRustcVm.Layout

public section

section
variable [Labels] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW}

/-- The frame and the stack arguments in a state of the body. -/
theorem wfA' (h : Pre L rows bl Fm SL m0) {m : MachineData} (hk : Kept m0.dmem m.dmem) :
    (Env.ofMachine m ((base m0 F, F + 72) :: [])).WF :=
  wfB h hk (.inr rfl) (fun _ h ↦ nomatch h) List.Pairwise.nil

/-- The framework's count as X22 holds it. -/
theorem x22_eq {rs : List (BitVec 64 × Nat)} {D : List (Sym × Nat)} {m : MachineData}
    (h : Pre L rows bl Fm SL m0) (hH : Holds rs (TT SL m0 L rows bl Fm 0) D m)
    (hp : D.contains (.reg .X22, 17) = true) (c : Nat) (hc : c < 2 ^ 64) :
    SBool.eval (Env.ofMachine m rs) (.cmp .eq .W64 (.reg .X22) (.lit c)) =
      decide (SL.framework.size = c) := by
  have he := cmp_eq_lit _ (Holds.evc hH hp) hc
  rw [TT_sv (by decide), sv17 h] at he
  exact he

end

variable [Host] {m0 : MachineData} {L : LayoutW} {rows : Array Nat}
  {bl : List NativeRustcVm.Data.Block} {Fm : Array (Array FormW)} {SL : BusLayoutW} {k : Nat}

/-- The ones' start: the framework's first block, or none. -/
abbrev onesPc (SL : BusLayoutW) (k : Nat) : Int64 :=
  if SL.framework.size = 0 then Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b6Offset) else Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b16Offset)

/-! ## The tree's value plus the known part -/

/-- **`b15`**: the tree's value plus the known part; the weights in the frame. -/
theorem k15 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q15 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QO m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, onesPc SL k⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset)⟩ := by
  have hH0 : Holds ((base m0 F, F + 72) :: []) (TT SL m0 L rows bl Fm 0) (Q15 ++ QArgs) m :=
    Holds.append (St.lift hst (by decide) 72 []) (holds_QArgs h hst.fr)
  have hwf := wfA' h hst.fr.kept
  refine St.run h.stack (A := 72) (rs := []) (sz := [12168]) rfl
    (b15_in_code.trans hp.1 (by simp [b15])) run_b15 hst.fr hH0 hwf (matchA h hst.fr.sp)
    rfl (by decide) (D' := QOr) (E := [(.reg .X29, 81), (.load 0 32 8, 80)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X29 = _
      refine (reg_eor hH0 hm' rfl (i := 67) (j := 15) (by decide) (by decide)).trans ?_
      show (kn SL m0 (cK SL m0)).c1 ^^^ stackArg m0 64 = (treeA m0 + kn SL m0 (cK SL m0)).c1
      rw [add_c1]
      exact UInt64.xor_comm _ _
    · rw [tval_write hm' rfl rfl (by decide) (v := .bin .eor .W64 (.reg .X19) (.load 0 32 8))
        (by decide), ofBitVec_eor, Holds.evc hH0 (s := .reg .X19) (i := 66) (by decide),
        Holds.evc hH0 (s := .load 0 32 8) (i := 14) (by decide), UInt64.ofBitVec_toBitVec,
        UInt64.ofBitVec_toBitVec]
      show (kn SL m0 (cK SL m0)).c0 ^^^ stackArg m0 56 = (treeA m0 + kn SL m0 (cK SL m0)).c0
      rw [add_c0]
      exact UInt64.xor_comm _ _
  · have he := x22_eq h hH0 (by decide) 0 (by decide)
    simp only [PcOk, he] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b6Offset) NativeRustcVmArm.Vm.AccumulateSide.label_4_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b15Offset + b15.length = k + NativeRustcVmArm.Vm.AccumulateSide.b16Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b15_next]] at hpc
    exact Gkr.at_pc (by simpa [onesPc] using hpc) (cont _ ⟨hst'.fr, Holds.sub hst'.hd
      (by decide)⟩ (forms_wrOk h (.inr rfl) hm' hwf (by decide) hF))

/-- **`b5`**: no known part: the tree's value; the weights in the frame. -/
theorem k5 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (hc0 : cK SL m0 = 0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QA m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QO m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, onesPc SL k⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b5Offset)⟩ := by
  have hH0 : Holds ((base m0 F, F + 72) :: []) (TT SL m0 L rows bl Fm 0)
      ((.reg .X29, 81) :: (.load 0 32 8, 80) :: (QA ++ QArgs)) m := by
    refine Holds.dup (Holds.dup (Holds.append (St.lift hst (by decide) 72 [])
      (holds_QArgs h hst.fr)) (i := 14) (by decide) ?_) (i := 15) (by decide) ?_
    · show stackArg m0 56 = (treeA m0 + kn SL m0 (cK SL m0)).c0
      rw [hc0, add_c0]
      exact UInt64.xor_zero.symm
    · show stackArg m0 64 = (treeA m0 + kn SL m0 (cK SL m0)).c1
      rw [hc0, add_c1]
      exact UInt64.xor_zero.symm
  have hwf := wfA' h hst.fr.kept
  refine St.run h.stack (A := 72) (rs := []) (sz := [12168]) rfl
    (b5_in_code.trans hp.1 (by simp [b5])) run_b5 hst.fr hH0 hwf (matchA h hst.fr.sp)
    rfl (by decide) (D' := QO) (E := []) (by decide) (by decide)
    (fun _ _ ↦ holds_nil _ _ _) fun st hm' hpc hst' ↦ ?_
  have he := x22_eq h hH0 (by decide) 0 (by decide)
  have hc : SBool.eval (Env.ofMachine m ((base m0 F, F + 72) :: []))
      (.not (.cmp .eq .W64 (.reg .X22) (.lit 0))) = !decide (SL.framework.size = 0) := by
    show (!SBool.eval _ _) = _
    rw [he]
  simp only [PcOk, hc] at hpc
  rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b16Offset) NativeRustcVmArm.Vm.AccumulateSide.label_10_at,
    show k + NativeRustcVmArm.Vm.AccumulateSide.b5Offset + b5.length = k + NativeRustcVmArm.Vm.AccumulateSide.b6Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b5_next]] at hpc
  exact Gkr.at_pc (by by_cases h0 : SL.framework.size = 0 <;> simpa [onesPc, h0] using hpc)
    (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inr rfl) hm' hwf (by decide) hF))

/-! ## The ones -/

/-- **`b6`**: no framework block: the ones are `1`. -/
theorem o6 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (h0 : SL.framework.size = 0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QO m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b6Offset)⟩ := by
  have hH0 := St.lift (D := QO) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b6_in_code.trans hp.1 (by simp [b6])) run_b6 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := QO) (E := [(.reg .X25, 78), (.reg .X20, 79)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl]
      show (1 : UInt64) = (onesF SL (ptA m0) SL.framework.size).c0
      rw [h0]
      rfl
    · rw [tval_reg_of hm' rfl]
      show (0 : UInt64) = (onesF SL (ptA m0) SL.framework.size).c1
      rw [h0]
      rfl
  · simp only [PcOk] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b22Offset) NativeRustcVmArm.Vm.AccumulateSide.label_13_at] at hpc
    exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- A framework block's selector, as `b16`, `b18`, `b20` call `eq_eval_fn`. -/
theorem oSel (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    {i : Nat} (hi : i < SL.framework.size) {ds : List Directive} {j : Nat}
    (hk : ds.IsInfixAt Host.prog (k + j)) {S' : SState}
    (hrun : exec ds sW = some (S', .call NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel)) (hsp : S'.sp = .ptr 0 0)
    (hw : wrOk S' = true)
    (h0 : S'.reg .X0 = some (.ite (.cmp .ult .W64 (.reg .X26) (.load 1 (16 + 16 * i) 8)) (.lit 0)
      (.bin .sub .W64 (.reg .X26) (.load 1 (16 + 16 * i) 8))))
    (h1 : S'.reg .X1 = some (.ite (.and (.not (.cmp .ult .W64 (.load 1 (16 + 16 * i) 8)
      (.lit 63))) (.not (.cmp .eq .W64 (.load 1 (16 + 16 * i) 8) (.lit 63)))) (.lit 0)
      (.bin .lsrv .W64 (.load 1 (24 + 16 * i) 8) (.load 1 (16 + 16 * i) 8))))
    (h2 : S'.reg .X2 = some (.ite (.cmp .ult .W64 (.reg .X26) (.load 1 (16 + 16 * i) 8))
      (.lit 8) (.bin .add .W64 (.reg .X28) (.un (.shift .LSL 4) .W64
        (.load 1 (16 + 16 * i) 8)))))
    (h3 : S'.reg .X3 = some (.ite (.cmp .ult .W64 (.reg .X26) (.load 1 (16 + 16 * i) 8)) (.lit 0)
      (.bin .sub .W64 (.reg .X26) (.load 1 (16 + 16 * i) 8))))
    {D : List (Sym × Nat)} (hDl : D.all (fun p ↦ loc0 p.1) = true)
    (hD : trackOk [12096, 64] S' ((.ptr 1 16, 18) :: D) D = true)
    (hDc : D.all (fun p ↦ callOk 0 0 p.1) = true)
    (hD13 : D.contains (.reg .X26, 13) = true) (hD12 : D.contains (.reg .X28, 12) = true)
    (hD18 : D.contains (.reg .X21, 18) = true)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) D m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) D m2 → ewRet m2 = sel SL m0 i →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + j + ds.length)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + j)⟩ := by
  have hfr := hst.fr
  have hi3 : i < 3 := Nat.lt_of_lt_of_le hi (fw_le h)
  have hwf := wf1 h hfr.kept (rok_sl h (n := 64) (by decide) (by decide))
  have hH0 : Holds ((base m0 F, F + 0) :: [(m0.regs.X6.toBitVec, 64)])
      (TT SL m0 L rows bl Fm 0) ((.ptr 1 16, 18) :: D) m := by
    refine Holds.cons (St.lift hst hDl 0 _) ?_
    unfold tval
    rw [ptr_eval (oi := 16) (o := 16) rfl rfl, TT_sv (by decide)]
    rfl
  have h21 : (m.regs.getXReg .X21).toBitVec = m0.regs.X6.toBitVec + BitVec.ofNat 64 16 := by
    rw [Holds.regv hst.hd (r := .X21) (i := 18) hD18, TT_sv (by decide)]
    rfl
  obtain ⟨hv1, hv2, hw0, hw1⟩ := fw_p h hi
  refine St.eqCall h hee (.inl rfl) (rs := [(m0.regs.X6.toBitVec, 64)]) (sz := [12096, 64]) rfl
    hk hrun hfr hH0 hwf (matchR h hfr.sp h21) hsp hw (D' := D) (E := [])
    (by rw [List.append_nil]; exact hDl) hD (fun _ _ ↦ holds_nil _ _ _)
    (by rw [List.append_nil]; exact hDc)
    (p := SL.framework[i]) h0 h1 h2 h3 ?_ ?_ rfl ?_ ?_ fun m2 hst2 hret hKF _ ↦ ?_
  · rw [Holds.evc (St.lift hst hDl 0 [(m0.regs.X6.toBitVec, 64)]) hD13, TT_sv (by decide)]
    rfl
  · rw [Holds.evc (St.lift hst hDl 0 [(m0.regs.X6.toBitVec, 64)]) hD12, TT_sv (by decide)]
    rfl
  · rw [load_rk rfl, sl_word h hfr (o := 16 + 16 * i) (by omega), hw0, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv1]
  · rw [load_rk rfl, sl_word h hfr (o := 24 + 16 * i) (by omega), hw1, UInt64.toNat_toBitVec,
      Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hv2]
  · refine cont m2 ⟨hst2.fr, by have := hst2.hd; rwa [List.append_nil] at this⟩ ?_ (hKF _ hF)
    rw [hret]
    show _ = eqAbove (SL.framework.getD i default) (ptA m0)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]

/-- **`b16`**: framework block `0`'s selector. -/
theorem o16 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hfw : 0 < SL.framework.size) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QO m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q17 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b17Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b16Offset)⟩ :=
  oSel h hee (i := 0) hfw (b16_in_code.trans hp.1 (by simp [b16])) run_b16 rfl (by decide) rfl rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hst hF fun m2 hst2 hret hF2 ↦
      cont m2 ⟨hst2.fr, holds_ewRet hst2.hd (r0 := 40) hret rfl rfl⟩ hF2

/-- **`b17`**: the ones over one block; the framework's count one or more. -/
theorem o17 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q17 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (c22 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q18 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → SL.framework.size = 1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩)
    (c18 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q18 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → SL.framework.size ≠ 1 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b18Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b17Offset)⟩ := by
  have hH0 := St.lift (D := Q17) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b17_in_code.trans hp.1 (by simp [b17])) run_b17 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := QO) (E := [(.reg .X25, 72), (.reg .X20, 73)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · rw [tval_reg_of hm' rfl, ofBitVec_eor, Holds.evc hH0 (s := .reg .X0) (i := 40) (by decide),
        UInt64.ofBitVec_toBitVec]
      show (sel SL m0 0).c0 ^^^ 1 = (onesF SL (ptA m0) 1).c0
      rw [onesF_succ, onesF_zero, add_c0, c0_one]
      exact UInt64.xor_comm _ _
    · rw [tval_reg_of hm' rfl, Holds.evc hH0 (s := .reg .X1) (i := 41) (by decide),
        UInt64.ofBitVec_toBitVec]
      show (sel SL m0 0).c1 = (onesF SL (ptA m0) 1).c1
      rw [onesF_succ, onesF_zero, add_c1, c1_one, UInt64.zero_xor]
  · have he := x22_eq h hH0 (by decide) 1 (by decide)
    simp only [PcOk, he] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b22Offset) NativeRustcVmArm.Vm.AccumulateSide.label_13_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b17Offset + b17.length = k + NativeRustcVmArm.Vm.AccumulateSide.b18Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b17_next]] at hpc
    have hF' := forms_wrOk h (.inl rfl) hm' hwf (by decide) hF
    have hst2 : St m0 (TT SL m0 L rows bl Fm 0) Q18 st.data :=
      ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    by_cases h1 : SL.framework.size = 1
    · exact Gkr.at_pc (by simpa [h1] using hpc) (c22 _ hst2 hF' h1)
    · exact Gkr.at_pc (by simpa [h1] using hpc) (c18 _ hst2 hF' h1)

/-- **`b18`**: framework block `1`'s selector. -/
theorem o18 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hfw : 1 < SL.framework.size) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q18 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q19 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b19Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b18Offset)⟩ :=
  oSel h hee (i := 1) hfw (b18_in_code.trans hp.1 (by simp [b18])) run_b18 rfl (by decide) rfl rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hst hF fun m2 hst2 hret hF2 ↦
      cont m2 ⟨hst2.fr, holds_ewRet hst2.hd (r0 := 42) hret rfl rfl⟩ hF2

/-- **`b19`**: the ones over two blocks; the framework's count two or three. -/
theorem o19 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q19 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (c22 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q20 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → SL.framework.size = 2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩)
    (c20 : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q20 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm → SL.framework.size ≠ 2 →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b20Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b19Offset)⟩ := by
  have hH0 := St.lift (D := Q19) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b19_in_code.trans hp.1 (by simp [b19])) run_b19 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := QO) (E := [(.reg .X25, 74), (.reg .X20, 75)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X25 = _
      refine (reg_eor hH0 hm' rfl (i := 42) (j := 72) (by decide) (by decide)).trans ?_
      show (sel SL m0 1).c0 ^^^ (onesF SL (ptA m0) 1).c0 = (onesF SL (ptA m0) 2).c0
      rw [onesF_succ SL (ptA m0) 1, add_c0]
      exact UInt64.xor_comm _ _
    · change st.regs.getXReg .X20 = _
      refine (reg_eor hH0 hm' rfl (i := 43) (j := 73) (by decide) (by decide)).trans ?_
      show (sel SL m0 1).c1 ^^^ (onesF SL (ptA m0) 1).c1 = (onesF SL (ptA m0) 2).c1
      rw [onesF_succ SL (ptA m0) 1, add_c1]
      exact UInt64.xor_comm _ _
  · have he := x22_eq h hH0 (by decide) 2 (by decide)
    simp only [PcOk, he] at hpc
    rw [hp.label (j := NativeRustcVmArm.Vm.AccumulateSide.b22Offset) NativeRustcVmArm.Vm.AccumulateSide.label_13_at,
      show k + NativeRustcVmArm.Vm.AccumulateSide.b19Offset + b19.length = k + NativeRustcVmArm.Vm.AccumulateSide.b20Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b19_next]] at hpc
    have hF' := forms_wrOk h (.inl rfl) hm' hwf (by decide) hF
    have hst2 : St m0 (TT SL m0 L rows bl Fm 0) Q20 st.data :=
      ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
    by_cases h2 : SL.framework.size = 2
    · exact Gkr.at_pc (by simpa [h2] using hpc) (c22 _ hst2 hF' h2)
    · exact Gkr.at_pc (by simpa [h2] using hpc) (c20 _ hst2 hF' h2)

/-- **`b20`**: framework block `2`'s selector. -/
theorem o20 (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    (hfw : 2 < SL.framework.size) {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q20 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) Q21 m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b21Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b20Offset)⟩ :=
  oSel h hee (i := 2) hfw (b20_in_code.trans hp.1 (by simp [b20])) run_b20 rfl (by decide) rfl rfl rfl rfl (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hst hF fun m2 hst2 hret hF2 ↦
      cont m2 ⟨hst2.fr, holds_ewRet hst2.hd (r0 := 44) hret rfl rfl⟩ hF2

/-- **`b21`**: the ones over three blocks, the framework's. -/
theorem o21 (hp : Placed code k) (h : Pre L rows bl Fm SL m0) (h3 : SL.framework.size = 3)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) Q21 m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b21Offset)⟩ := by
  have hH0 := St.lift (D := Q21) hst (by decide) 0 []
  have hwf := wf0 h hst.fr.kept
  refine St.run h.stack (A := 0) (rs := []) (sz := [12096]) rfl
    (b21_in_code.trans hp.1 (by simp [b21])) run_b21 hst.fr hH0 hwf (matchF h hst.fr.sp)
    rfl (by decide) (D' := QO) (E := [(.reg .X25, 78), (.reg .X20, 79)]) (by decide)
    (by decide) (fun st hm' p hp' ↦ ?_) fun st hm' hpc hst' ↦ ?_
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp'
    rcases hp' with rfl | rfl
    · change st.regs.getXReg .X25 = _
      refine (reg_eor hH0 hm' rfl (i := 44) (j := 74) (by decide) (by decide)).trans ?_
      show (sel SL m0 2).c0 ^^^ (onesF SL (ptA m0) 2).c0 =
        (onesF SL (ptA m0) SL.framework.size).c0
      rw [h3, onesF_succ SL (ptA m0) 2, add_c0]
      exact UInt64.xor_comm _ _
    · change st.regs.getXReg .X20 = _
      refine (reg_eor hH0 hm' rfl (i := 45) (j := 75) (by decide) (by decide)).trans ?_
      show (sel SL m0 2).c1 ^^^ (onesF SL (ptA m0) 2).c1 =
        (onesF SL (ptA m0) SL.framework.size).c1
      rw [h3, onesF_succ SL (ptA m0) 2, add_c1]
      exact UInt64.xor_comm _ _
  · simp only [PcOk] at hpc
    rw [show k + NativeRustcVmArm.Vm.AccumulateSide.b21Offset + b21.length = k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset from by rw [Nat.add_assoc, NativeRustcVmArm.Vm.AccumulateSide.b21_next]] at hpc
    exact Gkr.at_pc hpc (cont _ ⟨hst'.fr, Holds.sub hst'.hd (by decide)⟩
      (forms_wrOk h (.inl rfl) hm' hwf (by decide) hF))

/-- **The ones**: from `b6` or `b16` to `b22`, the framework's blocks. -/
theorem ones (hp : Placed code k) (h : Pre L rows bl Fm SL m0)
    (hee : Spec (Labels.label NativeRustcVmArm.Vm.EqEvalFnOfEqAbove.entryLabel) EqEvalFnOfEqAbovePre
      EqEvalFnOfEqAbovePost)
    {m : MachineData} (hst : St m0 (TT SL m0 L rows bl Fm 0) QO m)
    (hF : FormsAt m.dmem m0.regs.X1.toBitVec Fm) {R : MachineState → Prop}
    (cont : ∀ m2, St m0 (TT SL m0 L rows bl Fm 0) QZ m2 →
      FormsAt m2.dmem m0.regs.X1.toBitVec Fm →
      Eventually (step1 Host.exe) R ⟨m2, Host.addrOf (k + NativeRustcVmArm.Vm.AccumulateSide.b22Offset)⟩) :
    Eventually (step1 Host.exe) R ⟨m, onesPc SL k⟩ := by
  have h3 := fw_le h
  have dupQZ : ∀ {m2 : MachineData} {a b : Nat},
      TT SL m0 L rows bl Fm 0 a = TT SL m0 L rows bl Fm 0 78 →
      TT SL m0 L rows bl Fm 0 b = TT SL m0 L rows bl Fm 0 79 →
      St m0 (TT SL m0 L rows bl Fm 0) ([(.reg .X25, a), (.reg .X20, b)] ++ QO) m2 →
      St m0 (TT SL m0 L rows bl Fm 0) QZ m2 := fun ha hb hs ↦
    ⟨hs.fr, fun p hp ↦ by
      simp only [QZ, List.cons_append, List.nil_append, List.mem_cons] at hp
      rcases hp with rfl | rfl | hp
      · exact (hs.hd _ (List.mem_cons_self ..)).trans ha
      · exact (hs.hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hb
      · exact hs.hd _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))⟩
  unfold onesPc
  by_cases h0 : SL.framework.size = 0
  · simp only [h0, ↓reduceIte]
    exact o6 hp h h0 hst hF cont
  · simp only [h0, ↓reduceIte]
    refine o16 hp h hee (by omega) hst hF fun m2 hs2 hF2 ↦ o17 hp h hs2 hF2
      (fun m3 hs3 hF3 h1 ↦ cont m3 (dupQZ (by
        show (onesF SL (ptA m0) 1).c0 = (onesF SL (ptA m0) SL.framework.size).c0; rw [h1])
        (by show (onesF SL (ptA m0) 1).c1 = (onesF SL (ptA m0) SL.framework.size).c1; rw [h1])
        hs3) hF3) fun m3 hs3 hF3 h1 ↦ ?_
    refine o18 hp h hee (by omega) hs3 hF3 fun m4 hs4 hF4 ↦ o19 hp h hs4 hF4
      (fun m5 hs5 hF5 h2 ↦ cont m5 (dupQZ (by
        show (onesF SL (ptA m0) 2).c0 = (onesF SL (ptA m0) SL.framework.size).c0; rw [h2])
        (by show (onesF SL (ptA m0) 2).c1 = (onesF SL (ptA m0) SL.framework.size).c1; rw [h2])
        hs5) hF5) fun m5 hs5 hF5 h2 ↦ ?_
    exact o20 hp h hee (by omega) hs5 hF5 fun m6 hs6 hF6 ↦ o21 hp h (by omega) hs6 hF6 cont

end

end NativeRustcVmArm.Bus.AccumulateSide
