module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Whir.FoldRow.Common

/-!
# `fold_row`'s round 6

The last round the unrolled code has (`b46` to `b54`), its registers renamed: `head6` (`b46` to
`b49`, or `b54` with no turn, X26 zero), `turn6` (`b51` to `b53`), `inc6` (`b50`). After it, the
end (`b55`) unconditionally: there are at most six rounds.
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

theorem rn_six {m0 : MachineData} (hpre : FoldRowPre m0) (h : 5 < rnOf m0) : rnOf m0 = 6 := by
  have := (pre_parts hpre).2.2.2.2
  omega

variable [Host] {k : Nat}

/-- **Round 6's head.** -/
theorem head6 (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {st : MachineData} (hH : Head m0 5 st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Fin m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)) ∨
        (Loop6 m0 0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b46Offset)⟩ := by
  obtain ⟨hS, hvin, hrin, hap, hR6⟩ := pre_parts hpre
  have hF : 128 ≤ foldRowStack := by decide
  have hkle : 128 + kmulStack ≤ foldRowStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hH.fr
  have hr6 : rnOf m0 = 6 := rn_six hpre hH.hr
  have hr : 6 ≤ rnOf m0 := by omega
  let ra := m0.regs.X3.toBitVec
  let fb := fbOf m0
  have hrd : Readable st ra 192 := hfr.readable (Readable.mono hrin.1 (by omega))
  have hfrd : Readable st fb 128 := hfr.readable ⟨hfmap, hfnw⟩
  have hapf : Apart fb 128 ra 192 := by
    have := apart_frame hrin.2 hF hS.2.1
    have hfb : fb.toNat = m0.regs.SP.toBitVec.toNat - 128 := hfe
    have hra : ra.toNat = m0.regs.X3.toBitVec.toNat := rfl
    unfold Apart at this ⊢
    rw [hfe] at this
    omega
  -- `b46`: the round's words, `kmul(x, β₀)`
  let env1 := Env.ofMachine st [(fb, 128), (ra, 192)]
  have hwf1 : env1.WF :=
    Env.wf_of ⟨⟨hfrd.1, hfrd.2⟩, ⟨hrd.1, hrd.2⟩, trivial⟩ (List.pairwise_pair.mpr hapf)
  have hm1 : Match env1 (hdS 6) st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fb, fbOf])
      ⟨by
        show st.regs.X22.toBitVec = ra + BitVec.ofInt 64 0
        rw [hH.x22]; simp [ra], trivial⟩ trivial trivial trivial
  have hk46 : b46.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b46Offset) := b46_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk46 run_b46 hwf1 hm1 fun s1 hm2 hpc1 ↦ ?_
  have hb46 := after_eq run_b46 ▸ b46_keeps
  have hfr1 := hfr.of_regs hm1 hm2 hwf1 rfl hb46.1 hb46.2
  have hd1 : s1.data.dmem = st.dmem := hm2.dmem_eq hwf1 hb46.2
  obtain ⟨wa0, wa1, wb0, wb1⟩ := rd_words hpre hfr (r := 5) (by omega)
  have hx := spill_word hH.sp (i := 0) (by decide)
  have lx : env1.load 0 0 8 = m0.regs.X2.toBitVec :=
    load_word (show NativeRustcVm.WordAt st.dmem (fb + BitVec.ofNat 64 0) _ from by simpa using hx)
  have lr : ∀ o, env1.load 1 o 8 = (wordOf st.dmem (ra + BitVec.ofNat 64 o)).toBitVec :=
    fun o ↦ load8_eq env1 1 o
  have e0 : s1.data.regs.X0 = m0.regs.X2 := UInt64.toBitVec_inj.mp ((hm2.regs .X0 _ rfl).trans lx)
  have e1 : s1.data.regs.X1 = (rdOf m0 5).beta.c0 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X1 _ rfl).trans ((lr 176).trans (by rw [← wb0])))
  have e19 : s1.data.regs.X19 = m0.regs.X2 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X19 _ rfl).trans lx)
  have e23 : s1.data.regs.X23 = (rdOf m0 5).beta.c1 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X23 _ rfl).trans ((lr 184).trans (by rw [← wb1])))
  have e24 : s1.data.regs.X24 = (rdOf m0 5).alpha.c0 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X24 _ rfl).trans ((lr 160).trans (by rw [← wa0])))
  have e25 : s1.data.regs.X25 = (rdOf m0 5).alpha.c1 :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X25 _ rfl).trans ((lr 168).trans (by rw [← wa1])))
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hk0, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hsp2 := (hH.sp.of_dmem hd1).call hfr1 hS hkle hsame2
  have hl2 := lanes_call hpre hfr1 hkle hsame2 (show LanesAt s1.data.dmem _ _ from hd1 ▸ hH.lanes)
  -- `b47`: `kmul(x, β₁)`
  have hk47 : b47.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b47Offset) := b47_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b47Offset) := hpc2
  refine exec_at hk47 run_b47 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb47 := after_eq run_b47 ▸ b47_keeps
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb47.1 hb47.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb47.2
  have f22 : s3.data.regs.X22 = kmul m0.regs.X2 (rdOf m0 5).beta.c0 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X22 _ rfl)).trans (hk0.trans (by rw [e0, e1]))
  have f0 : s3.data.regs.X0 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)).trans ((hsv2.1 .X19 rfl).trans e19)
  have f1 : s3.data.regs.X1 = (rdOf m0 5).beta.c1 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)).trans ((hsv2.1 .X23 rfl).trans e23)
  refine call_then hpc3 hkmul (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hk1, hsame4, hsv4⟩ ↦ ?_
  have hfr4 := hfr3.call hS hkle slots_le hsame4 hsv4
  have hsp4 := (hsp2.of_dmem hd3).call hfr3 hS hkle hsame4
  have hl4 := lanes_call hpre hfr3 hkle hsame4 (show LanesAt s3.data.dmem _ _ from hd3 ▸ hl2)
  have g0 : s4.data.regs.X0 = kmul m0.regs.X2 (rdOf m0 5).beta.c1 := hk1.trans (by rw [f0, f1])
  have c4 : ∀ r ∈ [XReg.X24, .X25], s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
    exact (hsv4.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans (hsv2.1 _ rfl))
  -- `b48`: the turns' count
  have hk48 : b48.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b48Offset) := b48_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b48Offset) := hpc4
  let env5 := Env.ofMachine s4.data [(fb, 128)]
  have hwf5 : env5.WF := wf_one (hfr4.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm5 : Match env5 frS s4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr4.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk48 run_b48 hwf5 hpc4' hm5 fun s5 hm6 hpc5 ↦ ?_
  have hb48 := after_eq run_b48 ▸ b48_keeps
  have hfr5 := hfr4.of_regs hm5 hm6 hwf5 rfl hb48.1 hb48.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm6.dmem_eq hwf5 hb48.2
  have ln : env5.load 0 8 8 = m0.regs.X1.toBitVec :=
    load_word (show NativeRustcVm.WordAt s4.data.dmem (fb + BitVec.ofNat 64 8) m0.regs.X1 from
      spill_word hsp4 (i := 1) (by decide))
  have h21 : (s5.data.regs.getXReg .X21).toBitVec.toNat = nOf m0 >>> 6 := by
    rw [hm6.regs .X21 _ rfl]
    sym_simp
    rw [lsr_toNat _ (by decide), ln]
    rfl
  have hc : (SBool.cmp .eq .W64 (.un (.ubfm 6 63) .W64 (.load 0 8 8)) (.lit 0)).eval env5 =
      decide (nOf m0 >>> 6 = 0) := by
    sym_simp
    rw [bv_beq_toNat, lsr_toNat _ (by decide), ln]
    exact decide_eq_decide.mpr (by simp [nOf])
  simp only [PcOk] at hpc5
  rw [hc] at hpc5
  have hv : NativeRustcVm.WordAt s5.data.dmem (fbOf m0 + BitVec.ofNat 64 24) m0.regs.X0 :=
    hd5 ▸ spill_word hsp4 (i := 3) (by decide)
  by_cases hz : nOf m0 >>> 6 = 0
  · -- no turn: `b54`, X26 zero
    simp only [hz, decide_true, ↓reduceIte] at hpc5
    rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_36 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b54Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b54Offset) NativeRustcVmArm.Vm.FoldRow.label_36_at] at hpc5
    have hk54 : b54.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b54Offset) := b54_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk54 run_b54 (Env.wf_nil _) hpc5 (match_nil _) fun s6 hm7 hpc6 ↦ ?_
    have hb54 := after_eq run_b54 ▸ b54_keeps
    have hfr6 := hfr5.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb54.1 hb54.2
    have hd6 : s6.data.dmem = s5.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb54.2
    refine .done _ (.inl ⟨⟨hfr6, hd6 ▸ hv, ?_, ?_⟩, hpc6⟩)
    · rw [hr6, hz]
      exact iff_of_true (UInt64.toBitVec_inj.mp (hm7.regs .X26 _ rfl)) rfl
    · rw [hr6, memOf_succ, hz, foldPart_zero, hd6, hd5]
      exact hl4
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc5
  -- `b49`: the pointers
  have hk49 : b49.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b49Offset) := b49_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b49Offset) := hpc5
  let env6 := Env.ofMachine s5.data [(fb, 128)]
  have hwf6 : env6.WF := wf_one (hfr5.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm7 : Match env6 frS s5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr5.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk49 run_b49 hwf6 hpc5' hm7 fun s6 hm8 hpc6 ↦ ?_
  have hb49 := after_eq run_b49 ▸ b49_keeps
  have hfr6 := hfr5.of_regs hm7 hm8 hwf6 rfl hb49.1 hb49.2
  have hd6 : s6.data.dmem = s5.data.dmem := hm8.dmem_eq hwf6 hb49.2
  have lv : env6.load 0 24 8 = m0.regs.X0.toBitVec := load_word hv
  have c6 : ∀ r ∈ [XReg.X21, .X22, .X24, .X25], s6.data.regs.getXReg r =
      s5.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm7 hm8 rfl rfl
  have c5 : ∀ r ∈ [XReg.X22, .X24, .X25], s5.data.regs.getXReg r =
      s4.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm5 hm6 rfl rfl
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset) := by
    simp only [PcOk] at hpc6
    rw [hpc6]
    exact hp.label (j := NativeRustcVmArm.Vm.FoldRow.b51Offset) NativeRustcVmArm.Vm.FoldRow.label_34_at
  refine .done _ (.inr ⟨⟨hfr6, (hsp4.of_dmem hd5).of_dmem hd6, ?_, ?_, ?_, ?_, by omega, ?_, ?_,
    ?_, hr⟩, hpc6'⟩)
  · -- the factor
    have h22 : s6.data.regs.X22 = kmul m0.regs.X2 (rdOf m0 5).beta.c0 :=
      ((c6 .X22 (by simp)).trans ((c5 .X22 (by simp)).trans (hsv4.1 .X22 rfl))).trans f22
    have h20 : s6.data.regs.X20 = kmul m0.regs.X2 (rdOf m0 5).beta.c1 :=
      (UInt64.toBitVec_inj.mp (hm8.regs .X20 _ rfl)).trans
        ((Match.reg_eq (r := .X0) hm5 hm6 rfl rfl).trans g0)
    have h24 : s6.data.regs.X24 = (rdOf m0 5).alpha.c0 :=
      ((c6 .X24 (by simp)).trans ((c5 .X24 (by simp)).trans (c4 .X24 (by simp)))).trans e24
    have h25 : s6.data.regs.X25 = (rdOf m0 5).alpha.c1 :=
      ((c6 .X25 (by simp)).trans ((c5 .X25 (by simp)).trans (c4 .X25 (by simp)))).trans e25
    rw [h24, h25]
    exact fac_eq h22 h20
  · show (s6.data.regs.getXReg .X21).toBitVec.toNat = _
    rw [c6 .X21 (by simp)]
    exact h21
  · exact UInt64.toBitVec_inj.mp (hm8.regs .X26 _ rfl)
  · show (s6.data.regs.getXReg .X23).toBitVec.toNat = _
    rw [hm8.regs .X23 _ rfl]
    rfl
  · refine (hm8.regs .X27 _ rfl).trans ?_
    sym_simp
    rw [lv]
    rfl
  · refine (hm8.regs .X28 _ rfl).trans ?_
    sym_simp
    rw [lv]
    rfl
  · rw [foldPart_zero, hd6, hd5]
    exact hl4

/-- **Round 6's count** (`b50`): the next turn, or the end. -/
theorem inc6 (hp : Placed code k) {m0 : MachineData} (hpre : FoldRowPre m0) {i : Nat}
    {st : MachineData} (hT : Turned6 m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Fin m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)) ∨
        (Loop6 m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b50Offset)⟩ := by
  have hk : b50.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b50Offset) := b50_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk run_b50 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb := after_eq run_b50 ▸ b50_keeps
  have hfr1 := hT.fr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb.1 hb.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb.2
  have e : ∀ r ∈ [XReg.X20, .X21, .X22, .X24, .X25, .X26], s1.data.regs.getXReg r =
      st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Match.reg_eq (match_nil _) hm1 rfl rfl
  have hlt : nOf m0 >>> 6 < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.shiftRight_le _ _) m0.regs.X1.toNat_lt
  have hi := hT.hi
  have h23 : (st.regs.getXReg .X23).toBitVec.toNat = i := hT.x23
  have h21 : (st.regs.getXReg .X21).toBitVec.toNat = nOf m0 >>> 6 := hT.x21
  have hc : (SBool.cmp .eq .W64 (.reg .X21) (.bin .add .W64 (.reg .X23) (.lit 1))).eval
      (Env.ofMachine st []) = decide (nOf m0 >>> 6 = i + 1) := by
    sym_simp
    rw [bv_beq_toNat, Env.ofMachine_regs, Env.ofMachine_regs, BitVec.toNat_add, h21, h23]
    exact decide_eq_decide.mpr (by simp; omega)
  simp only [PcOk] at hpc1
  rw [hc] at hpc1
  by_cases hl : nOf m0 >>> 6 = i + 1
  · simp only [show decide (nOf m0 >>> 6 = i + 1) = true from decide_eq_true hl,
      ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_37 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b55Offset) NativeRustcVmArm.Vm.FoldRow.label_37_at] at hpc1
    have hr6 : rnOf m0 = 6 := by have := (pre_parts hpre).2.2.2.2; have := hT.hr; omega
    refine .done _ (.inl ⟨⟨hfr1, ?_, ?_, ?_⟩, hpc1⟩)
    · exact hd1 ▸ (spill_word hT.sp (i := 3) (by decide) :
        NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) m0.regs.X0)
    · rw [show s1.data.regs.X26 = st.regs.X26 from e .X26 (by simp), hT.x26, hr6, hl]
      exact iff_of_false (by decide) (by omega)
    · rw [hr6, memOf_succ, hl, hd1]
      exact hT.lanes
  · simp only [show decide (nOf m0 >>> 6 = i + 1) = false from decide_eq_false hl,
      Bool.false_eq_true, ↓reduceIte] at hpc1
    have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset) := hpc1
    refine .done _ (.inr ⟨⟨hfr1, hT.sp.of_dmem hd1, ?_, ?_, ?_, ?_, by omega, ?_, ?_,
      hd1 ▸ hT.lanes, hT.hr⟩, hpc1'⟩)
    · rw [show s1.data.regs.X20 = st.regs.X20 from e .X20 (by simp),
        show s1.data.regs.X22 = st.regs.X22 from e .X22 (by simp),
        show s1.data.regs.X24 = st.regs.X24 from e .X24 (by simp),
        show s1.data.regs.X25 = st.regs.X25 from e .X25 (by simp)]
      exact hT.fac
    · show (s1.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [e .X21 (by simp)]
      exact h21
    · rw [show s1.data.regs.X26 = st.regs.X26 from e .X26 (by simp)]
      exact hT.x26
    · show (s1.data.regs.getXReg .X23).toBitVec.toNat = _
      rw [hm1.regs .X23 _ rfl]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_add, h23]
      simp
      omega
    · refine (hm1.regs .X27 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs]
      show st.regs.X27.toBitVec + _ = _
      rw [hT.x27, addr_add, show 16 * i + 8 + 16 = 16 * (i + 1) + 8 by omega]
    · refine (hm1.regs .X28 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs]
      show st.regs.X28.toBitVec + _ = _
      rw [hT.x28, addr_add, show 32 * i + 16 + 32 = 32 * (i + 1) + 16 by omega]

/-- **A turn of round 6** (`b51` to `b53`), then the count. -/
theorem turn6 (hp : Placed code k) (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) {i : Nat} {st : MachineData}
    (hL : Loop6 m0 i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Fin m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)) ∨
        (Loop6 m0 (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b51Offset)⟩ := by
  obtain ⟨hS, hvin, -, -, -⟩ := pre_parts hpre
  have hmle : 128 + ewMulStack ≤ foldRowStack := by decide
  have hk51 : b51.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b51Offset) := b51_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk51 run_b51 (Env.wf_nil _) (match_nil _) fun s1 hm1 hpc1 ↦ ?_
  have hb51 := after_eq run_b51 ▸ b51_keeps
  have hfr1 := hL.fr.of_regs (match_nil _) hm1 (Env.wf_nil _) rfl hb51.1 hb51.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq (Env.wf_nil _) hb51.2
  have e1 : ∀ r, s1.data.regs.getXReg r = st.regs.getXReg r := fun r ↦
    Match.reg_eq (match_nil _) hm1 (r := r) (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
  have h23 : (st.regs.getXReg .X23).toBitVec.toNat = i := hL.x23
  have hc : ((SBool.cmp .ult .W64 (.reg .X23) (.lit 31)).not.and
      (SBool.cmp .eq .W64 (.reg .X23) (.lit 31)).not).eval (Env.ofMachine st []) =
      decide (31 < i) := by
    sym_simp
    rw [bv_ult_toNat, bv_beq_toNat, Env.ofMachine_regs, h23]
    by_cases h : 31 < i
    · simp [h]; omega
    · simp [h]; omega
  simp only [PcOk] at hpc1
  rw [hc] at hpc1
  have hl1 : LanesAt s1.data.dmem (vOf m0)
      (foldPart m0.regs.X2 (rdOf m0 5) i (memOf m0 5)) := hd1 ▸ hL.lanes
  by_cases hbig : 31 < i
  · -- past lane 31: nothing written
    simp only [show decide (31 < i) = true from decide_eq_true hbig, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_33 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b50Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b50Offset) NativeRustcVmArm.Vm.FoldRow.label_33_at] at hpc1
    obtain ⟨d, pc⟩ := s1
    simp only at hpc1
    subst hpc1
    refine inc6 hp hpre ⟨hfr1, hL.sp.of_dmem hd1, ?_,
      by rw [← hL.x21]; exact congrArg (·.toBitVec.toNat) (e1 .X21), (e1 .X26).trans hL.x26,
      ?_, hL.hi, ?_, ?_, ?_, hL.hr⟩
    · rw [show d.regs.X20 = st.regs.X20 from e1 .X20, show d.regs.X22 = st.regs.X22 from e1 .X22,
        show d.regs.X24 = st.regs.X24 from e1 .X24, show d.regs.X25 = st.regs.X25 from e1 .X25]
      exact hL.fac
    · rw [← hL.x23]; exact congrArg (·.toBitVec.toNat) (e1 .X23)
    · rw [← hL.x27]; exact congrArg (·.toBitVec) (e1 .X27)
    · rw [← hL.x28]; exact congrArg (·.toBitVec) (e1 .X28)
    · rw [foldPart_succ_of_le _ _ _ (by omega)]
      exact hl1
  simp only [show decide (31 < i) = false from decide_eq_false hbig, Bool.false_eq_true,
    ↓reduceIte] at hpc1
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b52Offset) := hpc1
  -- `b52`: lanes `2i`, `2i + 1`, `EW::mul`
  let x := m0.regs.X2
  let rd := rdOf m0 5
  let old := memOf m0 5
  let a := vOf m0 + BitVec.ofNat 64 (32 * i)
  have hrd : Readable s1.data a 32 := hfr1.readable (Readable.sub hvin.1 (by omega))
  let env2 := Env.ofMachine s1.data [(a, 32)]
  have hwf2 : env2.WF := wf_one hrd.1 hrd.2
  have hm2 : Match env2 ldS6 s1.data := match_one <| by
    rw [e1]
    show st.regs.X28.toBitVec = _
    rw [hL.x28, show BitVec.ofInt 64 16 = BitVec.ofNat 64 16 from rfl, addr_add]
  have hk52 : b52.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b52Offset) := b52_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk52 run_b52 hwf2 hpc1' hm2 fun s2 hm3 hpc2 ↦ ?_
  have hb52 := after_eq run_b52 ▸ b52_keeps
  have hfr2 := hfr1.of_regs hm2 hm3 hwf2 rfl hb52.1 hb52.2
  have hd2 : s2.data.dmem = s1.data.dmem := hm3.dmem_eq hwf2 hb52.2
  have hf : ewOf s1.data.dmem a = old (2 * i) := by
    have := hl1 (2 * i) (by omega)
    rw [foldPart_old _ _ _ (by omega), show 16 * (2 * i) = 32 * i by omega] at this
    exact this
  have hg : ewOf s1.data.dmem (a + BitVec.ofNat 64 16) = old (2 * i + 1) := by
    have := hl1 (2 * i + 1) (by omega)
    rw [foldPart_old _ _ _ (by omega), show 16 * (2 * i + 1) = 32 * i + 16 by omega,
      ← addr_add] at this
    exact this
  have lw : ∀ o, env2.load 0 o 8 = (wordOf s1.data.dmem (a + BitVec.ofNat 64 o)).toBitVec :=
    fun o ↦ load8_eq env2 0 o
  have x2 : s2.data.regs.X2 = (old (2 * i)).c0 := UInt64.toBitVec_inj.mp <|
    (hm3.regs .X2 _ rfl).trans ((lw 0).trans (by rw [NativeRustcVm.addr_add_zero, ← hf]; rfl))
  have x3 : s2.data.regs.X3 = (old (2 * i)).c1 := UInt64.toBitVec_inj.mp <|
    (hm3.regs .X3 _ rfl).trans ((lw 8).trans (by rw [← hf]; rfl))
  have g0 : s2.data.regs.X19 = (old (2 * i + 1)).c0 := UInt64.toBitVec_inj.mp <|
    (hm3.regs .X19 _ rfl).trans ((lw 16).trans (by rw [← hg]; rfl))
  have g1 : s2.data.regs.X29 = (old (2 * i + 1)).c1 := UInt64.toBitVec_inj.mp <|
    (hm3.regs .X29 _ rfl).trans ((lw 24).trans (by
      rw [← hg]
      show (wordOf s1.data.dmem (vOf m0 + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 24)).toBitVec =
        (wordOf s1.data.dmem (vOf m0 + BitVec.ofNat 64 (32 * i) + BitVec.ofNat 64 16 +
          BitVec.ofNat 64 8)).toBitVec
      rw [addr_add, addr_add, addr_add, show 32 * i + 16 + 8 = 32 * i + 24 by omega]))
  have hfac0 : st.regs.X22 ^^^ st.regs.X24 = (foldFactor x rd).c0 := congrArg EW.c0 hL.fac
  have hfac1 : st.regs.X20 ^^^ st.regs.X25 = (foldFactor x rd).c1 := congrArg EW.c1 hL.fac
  have x0 : s2.data.regs.X0 = (foldFactor x rd).c0 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm3.regs .X0 _ rfl).trans ?_
    sym_simp
    show (s1.data.regs.getXReg .X22).toBitVec ^^^ (s1.data.regs.getXReg .X24).toBitVec = _
    rw [e1, e1, ← UInt64.toBitVec_xor]
    exact congrArg UInt64.toBitVec hfac0
  have x1 : s2.data.regs.X1 = (foldFactor x rd).c1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm3.regs .X1 _ rfl).trans ?_
    sym_simp
    show (s1.data.regs.getXReg .X20).toBitVec ^^^ (s1.data.regs.getXReg .X25).toBitVec = _
    rw [e1, e1, ← UInt64.toBitVec_xor]
    exact congrArg UInt64.toBitVec hfac1
  refine call_then hpc2 hmul (hfr2.stackOk hS rfl hmle) fun s3 hpc3 ⟨hp0, hp1, hsame3, hsv3⟩ ↦ ?_
  have hfr3 := hfr2.call hS hmle slots_le hsame3 hsv3
  have hsp3 := ((hL.sp.of_dmem hd1).of_dmem hd2).call hfr2 hS hmle hsame3
  have hl3 := lanes_call hpre hfr2 hmle hsame3 (show LanesAt s2.data.dmem _ _ from hd2 ▸ hl1)
  have hF : (⟨s2.data.regs.X0, s2.data.regs.X1⟩ : EW) = foldFactor x rd := by rw [x0, x1]
  have hFv : (⟨s2.data.regs.X2, s2.data.regs.X3⟩ : EW) = old (2 * i) := by rw [x2, x3]
  rw [hF, hFv] at hp0 hp1
  -- `b53`: store lane `i`
  let a7 := vOf m0 + BitVec.ofNat 64 (16 * i)
  have hrd7 : Readable s3.data a7 16 := hfr3.readable (Readable.sub hvin.1 (by omega))
  let env4 := Env.ofMachine s3.data [(a7, 16)]
  have hwf4 : env4.WF := wf_one hrd7.1 hrd7.2
  have hm4 : Match env4 stS6 s3.data := match_one <| by
    rw [hsv3.1 .X27 rfl, Match.reg_eq hm2 hm3 rfl rfl, e1]
    show st.regs.X27.toBitVec = _
    rw [hL.x27, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add]
  have hk53 : b53.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b53Offset) := b53_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b53Offset) := hpc3
  refine exec_at hk53 run_b53 hwf4 hpc3' hm4 fun s4 hm5 hpc4 ↦ ?_
  have hb53 := after_eq run_b53 ▸ b53_keeps
  have hfr4 := hfr3.of_block hm4 hm5 hwf4 rfl hb53.1 (r := 0) rfl le_rfl hb53.2
    (fun p h ↦ .inl ⟨_, List.mem_singleton_self _,
      (show InRange (vOf m0) 1024 p from NativeRustcVm.InRange.of_sub h hvin.1.2 (by omega))⟩)
    (fun q hq j hj ↦ by
      rw [addr_add]
      exact frame_not_lane hpre (i := i) (by omega) _ (by have := slots_le q hq; omega))
  have hsame4 := same_region hm5 hwf4 (r := 0) rfl hb53.2
  let new := old (2 * i + 1) + foldFactor x rd * old (2 * i)
  have h19 : s3.data.regs.X19 = (old (2 * i + 1)).c0 := (hsv3.1 .X19 rfl).trans g0
  have h29 : s3.data.regs.X29 = (old (2 * i + 1)).c1 := (hsv3.1 .X29 rfl).trans g1
  have heAt : NativeRustcVm.EWAt s4.data.dmem a7 new := by
    rw [NativeRustcVm.ewAt_iff]
    constructor
    · have := Match.wordAt_write hm5 (r := 0) (o := 0) rfl (by decide)
        (v := .bin .eor .W64 (.reg .X0) (.reg .X19)) (by decide)
      rw [NativeRustcVm.addr_add_zero] at this
      sym_simp at this
      convert this using 1
      show _ = UInt64.ofBitVec ((s3.data.regs.getXReg .X0).toBitVec ^^^
        (s3.data.regs.getXReg .X19).toBitVec)
      rw [← UInt64.toBitVec_xor, UInt64.ofBitVec_toBitVec]
      show (old (2 * i + 1)).c0 ^^^ (EW.mul (foldFactor x rd) (old (2 * i))).c0 = _
      rw [UInt64.xor_comm]
      exact congrArg₂ (· ^^^ ·) hp0.symm h19.symm
    · have := Match.wordAt_write hm5 (r := 0) (o := 8) rfl (by decide)
        (v := .bin .eor .W64 (.reg .X1) (.reg .X29)) (by decide)
      sym_simp at this
      convert this using 1
      show _ = UInt64.ofBitVec ((s3.data.regs.getXReg .X1).toBitVec ^^^
        (s3.data.regs.getXReg .X29).toBitVec)
      rw [← UInt64.toBitVec_xor, UInt64.ofBitVec_toBitVec]
      show (old (2 * i + 1)).c1 ^^^ (EW.mul (foldFactor x rd) (old (2 * i))).c1 = _
      rw [UInt64.xor_comm]
      exact congrArg₂ (· ^^^ ·) hp1.symm h29.symm
  have hl4 : LanesAt s4.data.dmem (vOf m0) (foldPart x rd (i + 1) old) := by
    rw [foldPart_succ _ _ _ (by omega)]
    exact hl3.store hvin.1.2 (by omega) hsame4 heAt
  have hsp4 := hsp3.of_same hsame4 fun j hj ↦ frame_not_lane hpre (i := i) (by omega) j (by omega)
  -- the registers
  have ch : ∀ r ∈ [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28],
      s4.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (Match.reg_eq hm4 hm5 rfl rfl).trans ((hsv3.1 _ rfl).trans
      ((Match.reg_eq hm2 hm3 rfl rfl).trans (e1 _)))
  simp only [PcOk] at hpc4
  rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_33 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b50Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b50Offset) NativeRustcVmArm.Vm.FoldRow.label_33_at] at hpc4
  obtain ⟨d, pc⟩ := s4
  simp only at hpc4
  subst hpc4
  refine inc6 hp hpre ⟨hfr4, hsp4, ?_, ?_, (ch .X26 (by simp)).trans hL.x26, ?_, hL.hi, ?_, ?_,
    hl4, hL.hr⟩
  · rw [show d.regs.X20 = st.regs.X20 from ch .X20 (by simp),
      show d.regs.X22 = st.regs.X22 from ch .X22 (by simp),
      show d.regs.X24 = st.regs.X24 from ch .X24 (by simp),
      show d.regs.X25 = st.regs.X25 from ch .X25 (by simp)]
    exact hL.fac
  · rw [← hL.x21]; exact congrArg (·.toBitVec.toNat) (ch .X21 (by simp))
  · rw [← hL.x23]; exact congrArg (·.toBitVec.toNat) (ch .X23 (by simp))
  · rw [← hL.x27]; exact congrArg (·.toBitVec) (ch .X27 (by simp))
  · rw [← hL.x28]; exact congrArg (·.toBitVec) (ch .X28 (by simp))

end

end NativeRustcVmArm.Whir.FoldRow
