module

public import NativeRustcVmArm.Code.Vm.FoldRow.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Whir.FoldRow.Common

/-!
# `fold_row`'s entry and round 1's head

`b0` saves the callee-saved registers, spills the rounds' count and `values`, and with no round
goes to the end (`Fin`). Else `b1` loads round 1's words and calls `kmul` (`β₀·x`), `b2` spills
`x` and calls `kmul` (`β₁·x`), `b3` spills `n` and computes the turns' count `n >>> 1`: none goes
to round 1's end (`Chk 1`), else `b4` sets the pointers (`Loop 1 0`).
-/

namespace NativeRustcVmArm.Whir.FoldRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRow NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

/-- A word whose bytes a step kept. -/
theorem wordAt_keep {d d' : DataMem} {b : BitVec 64} {o : Nat} {w : UInt64}
    (h : NativeRustcVm.WordAt d (b + BitVec.ofNat 64 o) w)
    (hk : ∀ i < 8, d'.get? (b + BitVec.ofNat 64 (o + i)) = d.get? (b + BitVec.ofNat 64 (o + i))) :
    NativeRustcVm.WordAt d' (b + BitVec.ofNat 64 o) w := fun i hi ↦ by
  have hi' : i < 8 := by rwa [NativeRustcVm.length_wordBytes] at hi
  rw [addr_add, hk i hi', ← addr_add]
  exact h i hi

/-- The spills from their four words. -/
theorem spills_of {m0 st : MachineData}
    (h0 : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 0) m0.regs.X2)
    (h1 : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 8) m0.regs.X1)
    (h2 : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 16) m0.regs.X4)
    (h3 : NativeRustcVm.WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 24) m0.regs.X0) :
    Spills m0 st := by
  unfold Spills
  rw [NativeRustcVm.addr_add_zero] at h0
  refine NativeRustcVm.wordsAt_cons_iff.mpr ⟨h0, NativeRustcVm.wordsAt_cons_iff.mpr ⟨?_,
    NativeRustcVm.wordsAt_cons_iff.mpr ⟨?_, NativeRustcVm.wordsAt_cons_iff.mpr ⟨?_,
      NativeRustcVm.wordsAt_nil _ _⟩⟩⟩⟩
  · exact h1
  · rw [addr_add]; exact h2
  · rw [addr_add, addr_add]; exact h3

variable [Host] {k : Nat}

/-- **The entry and round 1's head.** -/
theorem entry (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hpre : FoldRowPre m0) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Fin m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset)) ∨
        (Chk m0 1 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b9Offset)) ∨
        (Loop m0 1 0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b6Offset)))
      ⟨m0, Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b0Offset)⟩ := by
  obtain ⟨hS, hvin, hrin, hap, hR6⟩ := pre_parts hpre
  have hF : 128 ≤ foldRowStack := by decide
  have hkle : 128 + kmulStack ≤ foldRowStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  let fb := fbOf m0
  have hk0 : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b0Offset) := b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
  let env0 := Env.ofMachine m0 [(fb, 128)]
  have hwf0 : env0.WF := wf_one hfmap hfnw
  have hm0 : Match env0 entryS m0 :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_then hk0 run_b0 hwf0 hm0 fun s1 hm1 hpc1 ↦ ?_
  have hb0 := after_eq run_b0 ▸ b0_frame
  have hfr1 : Fr m0 s1.data := Frame.of_entry hS hF hwf0 hm1 rfl hb0.1 hb0.2.2 hb0.2.1
  have hsame1 := same_region hm1 hwf0 (r := 0) rfl hb0.2.1
  have hl1 : LanesAt s1.data.dmem (vOf m0) (memOf m0 0) :=
    LanesAt.of_same (d := m0.dmem) (fun _ _ ↦ rfl) hsame1 fun i hi ↦
      not_inRange_of_apart (apart_frame hvin.2 hF hS.2.1) hvin.1.2 hfnw hi
  have w16 : NativeRustcVm.WordAt s1.data.dmem (fb + BitVec.ofNat 64 16) m0.regs.X4 :=
    Match.wordAt_write hm1 (r := 0) (o := 16) rfl (by decide) (v := .reg .X4) (by decide)
  have w24 : NativeRustcVm.WordAt s1.data.dmem (fb + BitVec.ofNat 64 24) m0.regs.X0 :=
    Match.wordAt_write hm1 (r := 0) (o := 24) rfl (by decide) (v := .reg .X0) (by decide)
  have x26 : s1.data.regs.X26 = m0.regs.X1 := UInt64.toBitVec_inj.mp (hm1.regs .X26 _ rfl)
  have hc0 : (SBool.cmp .eq .W64 (.reg .X4) (.lit 0)).eval env0 = decide (rnOf m0 = 0) := by
    sym_simp
    rw [bv_beq_toNat, Env.ofMachine_regs]
    exact decide_eq_decide.mpr (by simp [rnOf]; exact Iff.rfl)
  simp only [PcOk] at hpc1
  rw [hc0] at hpc1
  by_cases hr0 : rnOf m0 = 0
  · -- no round
    simp only [hr0, decide_true, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_37 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b55Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b55Offset) NativeRustcVmArm.Vm.FoldRow.label_37_at] at hpc1
    refine .done _ (.inl ⟨⟨hfr1, w24, ?_, by rw [hr0]; exact hl1⟩, hpc1⟩)
    rw [x26, hr0, Nat.shiftRight_zero]
    exact ⟨fun h ↦ by rw [nOf, h]; rfl, fun h ↦ UInt64.toNat.inj h⟩
  simp only [hr0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  have hpc1' : s1.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b1Offset) := hpc1
  -- `b1`: round 1's words, `kmul(x, β₀)`
  have hrd : Readable s1.data m0.regs.X3.toBitVec 32 :=
    hfr1.readable (Readable.mono hrin.1 (by omega))
  let env1 := Env.ofMachine s1.data [(m0.regs.X3.toBitVec, 32)]
  have hwf1 : env1.WF := wf_one hrd.1 hrd.2
  have hm2 : Match env1 hd1S s1.data := match_one <| by
    rw [hm1.regs .X3 _ rfl]
    simp [Sym.eval, env0]
    rfl
  have hk1 : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b1Offset) := b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_at hk1 run_b1 hwf1 hpc1' hm2 fun s2 hm3 hpc2 ↦ ?_
  have hb1 := after_eq run_b1 ▸ b1_keeps
  have hfr2 := hfr1.of_regs hm2 hm3 hwf1 rfl hb1.1 hb1.2
  have hd2 : s2.data.dmem = s1.data.dmem := hm3.dmem_eq hwf1 hb1.2
  obtain ⟨wa0, wa1, wb0, wb1⟩ := rd_words hpre hfr1 (r := 0) (by omega)
  have lr : ∀ o, env1.load 0 o 8 =
      (wordOf s1.data.dmem (m0.regs.X3.toBitVec + BitVec.ofNat 64 o)).toBitVec :=
    fun o ↦ load8_eq env1 0 o
  have e1 : ∀ r, r ∉ [XReg.X0, .X1, .X3, .X19, .X22, .X25, .X27, .X28, .X30] →
      s2.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    cases r <;> simp at hr <;> exact Match.reg_eq hm2 hm3 rfl rfl
  have f0 : s2.data.regs.X0 = m0.regs.X2 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X0 _ rfl).trans (hm1.regs .X2 _ rfl))
  have f1 : s2.data.regs.X1 = (rdOf m0 0).beta.c0 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X1 _ rfl).trans ((lr 16).trans (by rw [← wb0])))
  have f19 : s2.data.regs.X19 = m0.regs.X2 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X19 _ rfl).trans (hm1.regs .X2 _ rfl))
  have f22 : s2.data.regs.X22 = m0.regs.X3 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X22 _ rfl).trans (by simp [Sym.eval, env1]))
  have f25 : s2.data.regs.X25 = (rdOf m0 0).beta.c1 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X25 _ rfl).trans ((lr 24).trans (by rw [← wb1])))
  have f27 : s2.data.regs.X27 = (rdOf m0 0).alpha.c0 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X27 _ rfl).trans ((lr 0).trans (by rw [← wa0])))
  have f28 : s2.data.regs.X28 = (rdOf m0 0).alpha.c1 :=
    UInt64.toBitVec_inj.mp ((hm3.regs .X28 _ rfl).trans ((lr 8).trans (by rw [← wa1])))
  have f26 : s2.data.regs.X26 = m0.regs.X1 := (e1 .X26 (by simp)).trans x26
  refine call_then hpc2 hkmul (hfr2.stackOk hS rfl hkle) fun s3 hpc3 ⟨hk0, hsame3, hsv3⟩ ↦ ?_
  have hfr3 := hfr2.call hS hkle slots_le hsame3 hsv3
  have hl3 := lanes_call hpre hfr2 hkle hsame3 (show LanesAt s2.data.dmem _ _ from hd2 ▸ hl1)
  have w16' := hfr2.bytes_call hS hkle hsame3 (o := 16)
    (by rw [NativeRustcVm.length_wordBytes]; omega) (show NativeRustcVm.WordAt _ _ _ from hd2 ▸ w16)
  have w24' := hfr2.bytes_call hS hkle hsame3 (o := 24)
    (by rw [NativeRustcVm.length_wordBytes]; omega) (show NativeRustcVm.WordAt _ _ _ from hd2 ▸ w24)
  have g24 : s3.data.regs.X0 = kmul m0.regs.X2 (rdOf m0 0).beta.c0 := hk0.trans (by rw [f0, f1])
  -- `b2`: spill `x`, `kmul(x, β₁)`
  have hk2 : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b2Offset) := b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b2Offset) := hpc3
  let env3 := Env.ofMachine s3.data [(fb, 128)]
  have hwf3 : env3.WF := wf_one (hfr3.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm4 : Match env3 frS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr3.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk2 run_b2 hwf3 hpc3' hm4 fun s4 hm5 hpc4 ↦ ?_
  have hb2 := after_eq run_b2 ▸ b2_keeps
  have hb2' : ∀ w ∈ (after b2 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := hb2.2
  have hfr4 := hfr3.of_block hm4 hm5 hwf3 rfl hb2.1 (r := 0) rfl (by decide) hb2'
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 8) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq j hj ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 8) (by omega) (slots_le q hq) hj
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hsame4 := same_region_le hm5 hwf3 (r := 0) rfl (by decide) hb2'
  have hl4 := lanes_frame hpre hl3 (st' := s4.data) fun p hp' ↦ hsame4 p fun h ↦ hp' <| by
    have := NativeRustcVm.InRange.of_sub (o := 0) (by rwa [NativeRustcVm.addr_add_zero]) hfnw
      (show 0 + 8 ≤ 128 by omega)
    exact this
  have hkeep4 : ∀ o, 8 ≤ o → o + 8 ≤ 128 → ∀ i < 8,
      s4.data.dmem.get? (fb + BitVec.ofNat 64 (o + i)) =
        s3.data.dmem.get? (fb + BitVec.ofNat 64 (o + i)) :=
    fun o h1 h2 ↦ Match.keep hm5 hwf3 (r := 0) rfl (o := o) (len := 8) h2 fun w hw ↦
      ⟨(hb2' w hw).1, .inl (by have := (hb2' w hw).2; omega)⟩
  have w0 : NativeRustcVm.WordAt s4.data.dmem (fb + BitVec.ofNat 64 0) m0.regs.X2 := by
    have := Match.wordAt_write hm5 (r := 0) (o := 0) rfl (by decide) (v := .reg .X19) (by decide)
    convert this using 1
    show _ = s3.data.regs.X19
    exact ((hsv3.1 .X19 rfl).trans f19).symm
  have g0 : s4.data.regs.X0 = m0.regs.X2 :=
    (UInt64.toBitVec_inj.mp (hm5.regs .X0 _ rfl)).trans ((hsv3.1 .X19 rfl).trans f19)
  have g1 : s4.data.regs.X1 = (rdOf m0 0).beta.c1 :=
    (UInt64.toBitVec_inj.mp (hm5.regs .X1 _ rfl)).trans ((hsv3.1 .X25 rfl).trans f25)
  have g24 : s4.data.regs.X24 = kmul m0.regs.X2 (rdOf m0 0).beta.c0 :=
    (UInt64.toBitVec_inj.mp (hm5.regs .X24 _ rfl)).trans g24
  have w16'' := wordAt_keep w16' (hkeep4 16 (by omega) (by omega))
  have w24'' := wordAt_keep w24' (hkeep4 24 (by omega) (by omega))
  refine call_then hpc4 hkmul (hfr4.stackOk hS rfl hkle) fun s5 hpc5 ⟨hk1, hsame5, hsv5⟩ ↦ ?_
  have hfr5 := hfr4.call hS hkle slots_le hsame5 hsv5
  have hl5 := lanes_call hpre hfr4 hkle hsame5 hl4
  have bc : ∀ {o : Nat} {w : UInt64}, o + 8 ≤ 128 →
      NativeRustcVm.WordAt s4.data.dmem (fb + BitVec.ofNat 64 o) w →
      NativeRustcVm.WordAt s5.data.dmem (fb + BitVec.ofNat 64 o) w := fun ho h ↦
    hfr4.bytes_call hS hkle hsame5 (by rw [NativeRustcVm.length_wordBytes]; omega) h
  have u0 := bc (by omega) w0
  have u16 := bc (by omega) w16''
  have u24 := bc (by omega) w24''
  have k25 : s5.data.regs.X0 = kmul m0.regs.X2 (rdOf m0 0).beta.c1 := hk1.trans (by rw [g0, g1])
  -- `b3`: spill `n`, the turns' count
  have hk3 : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b3Offset) := b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b3Offset) := hpc5
  let env5 := Env.ofMachine s5.data [(fb, 128)]
  have hwf5 : env5.WF := wf_one (hfr5.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm6 : Match env5 frS s5.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr5.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk3 run_b3 hwf5 hpc5' hm6 fun s6 hm7 hpc6 ↦ ?_
  have hb3 := after_eq run_b3 ▸ b3_keeps
  have hb3' : ∀ w ∈ (after b3 frS).mem, w.r = 0 ∧ w.off + w.n ≤ 16 :=
    fun w hw ↦ ⟨(hb3.2 w hw).1, (hb3.2 w hw).2.2⟩
  have hfr6 := hfr5.of_block hm6 hm7 hwf5 rfl hb3.1 (r := 0) rfl (by decide) hb3'
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 0) (n := 16) (by omega)
      (by rw [NativeRustcVm.addr_add_zero]; exact h)))
    (fun q hq j hj ↦ by
      have := not_inRange_slot hS hF (o := 0) (n := 16) (by omega) (slots_le q hq) hj
        (.inl (by have := slots_ge q hq; omega))
      rwa [NativeRustcVm.addr_add_zero] at this)
  have hsame6 := same_region_le hm7 hwf5 (r := 0) rfl (by decide) hb3'
  have hl6 := lanes_frame hpre hl5 (st' := s6.data) fun p hp' ↦ hsame6 p fun h ↦ hp' <|
    NativeRustcVm.InRange.of_sub (o := 0) (by rwa [NativeRustcVm.addr_add_zero]) hfnw
      (show 0 + 16 ≤ 128 by omega)
  have hkeep6 : ∀ o, (o + 8 ≤ 8 ∨ 16 ≤ o) → o + 8 ≤ 128 → ∀ i < 8,
      s6.data.dmem.get? (fb + BitVec.ofNat 64 (o + i)) =
        s5.data.dmem.get? (fb + BitVec.ofNat 64 (o + i)) :=
    fun o h1 h2 ↦ Match.keep hm7 hwf5 (r := 0) rfl (o := o) (len := 8) h2 fun w hw ↦
      ⟨(hb3.2 w hw).1, by have := (hb3.2 w hw).2; omega⟩
  have v8 : NativeRustcVm.WordAt s6.data.dmem (fb + BitVec.ofNat 64 8) m0.regs.X1 := by
    have := Match.wordAt_write hm7 (r := 0) (o := 8) rfl (by decide) (v := .reg .X26) (by decide)
    convert this using 1
    show _ = s5.data.regs.X26
    exact ((hsv5.1 .X26 rfl).trans ((Match.reg_eq (r := .X26) hm4 hm5 rfl rfl).trans
      ((hsv3.1 .X26 rfl).trans f26))).symm
  have hsp6 : Spills m0 s6.data :=
    spills_of (wordAt_keep u0 (hkeep6 0 (by omega) (by omega))) v8
      (wordAt_keep u16 (hkeep6 16 (by omega) (by omega)))
      (wordAt_keep u24 (hkeep6 24 (by omega) (by omega)))
  -- registers through `b3`
  have r6 : ∀ r ∈ [XReg.X0, .X22, .X24, .X27, .X28], s6.data.regs.getXReg r =
      s5.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm6 hm7 rfl rfl
  have r5 : ∀ r ∈ [XReg.X22, .X26, .X27, .X28], s5.data.regs.getXReg r =
      s2.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;>
    exact (hsv5.1 _ rfl).trans ((Match.reg_eq hm4 hm5 rfl rfl).trans (hsv3.1 _ rfl))
  have y22 : s6.data.regs.X22 = m0.regs.X3 := ((r6 .X22 (by simp)).trans (r5 .X22 (by simp))).trans f22
  have h26 : (s6.data.regs.getXReg .X26).toBitVec.toNat = nOf m0 >>> 1 := by
    rw [hm7.regs .X26 _ rfl]
    sym_simp
    rw [lsr_toNat _ (by decide), Env.ofMachine_regs, r5 .X26 (by simp)]
    show s2.data.regs.X26.toNat >>> 1 = _
    rw [f26]
    rfl
  have hc3 : (SBool.cmp .eq .W64 (.un (.ubfm 1 63) .W64 (.reg .X26)) (.lit 0)).eval env5 =
      decide (nOf m0 >>> 1 = 0) := by
    sym_simp
    rw [bv_beq_toNat, lsr_toNat _ (by decide), Env.ofMachine_regs, r5 .X26 (by simp)]
    show decide (s2.data.regs.X26.toNat >>> 1 = _) = _
    rw [f26]
    exact decide_eq_decide.mpr (by simp [nOf])
  simp only [PcOk] at hpc6
  rw [hc3] at hpc6
  have hr1 : 1 ≤ rnOf m0 := by omega
  by_cases hz : nOf m0 >>> 1 = 0
  · simp only [hz, decide_true, ↓reduceIte] at hpc6
    rw [show Labels.label NativeRustcVmArm.Vm.FoldRow.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b9Offset) from hp.label (j := NativeRustcVmArm.Vm.FoldRow.b9Offset) NativeRustcVmArm.Vm.FoldRow.label_6_at] at hpc6
    refine .done _ (.inr (.inl ⟨⟨hfr6, hsp6, y22, h26, ?_, hr1⟩, hpc6⟩))
    rw [memOf_succ, show nOf m0 >>> (0 + 1) = 0 from hz, foldPart_zero]
    exact hl6
  simp only [hz, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc6
  -- `b4`: the pointers
  have hk4 : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.FoldRow.b4Offset) := b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b4Offset) := hpc6
  let env6 := Env.ofMachine s6.data [(fb, 128)]
  have hwf6 : env6.WF := wf_one (hfr6.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm8 : Match env6 frS s6.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr6.sp]; simp [Sym.eval, fb, fbOf]) trivial trivial trivial trivial
  refine exec_at hk4 run_b4 hwf6 hpc6' hm8 fun s7 hm9 hpc7 ↦ ?_
  have hb4 := after_eq run_b4 ▸ b4_keeps
  have hfr7 := hfr6.of_regs hm8 hm9 hwf6 rfl hb4.1 hb4.2
  have hd7 : s7.data.dmem = s6.data.dmem := hm9.dmem_eq hwf6 hb4.2
  have lv : env6.load 0 24 8 = m0.regs.X0.toBitVec :=
    load_word (show NativeRustcVm.WordAt s6.data.dmem (fb + BitVec.ofNat 64 24) m0.regs.X0 from
      spill_word hsp6 (i := 3) (by decide))
  have r7 : ∀ r ∈ [XReg.X22, .X24, .X26, .X27, .X28], s7.data.regs.getXReg r =
      s6.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm8 hm9 rfl rfl
  have hpc7' : s7.pc = Host.addrOf (k + NativeRustcVmArm.Vm.FoldRow.b6Offset) := by
    simp only [PcOk] at hpc7
    rw [hpc7]
    exact hp.label (j := NativeRustcVmArm.Vm.FoldRow.b6Offset) NativeRustcVmArm.Vm.FoldRow.label_4_at
  refine .done _ (.inr (.inr ⟨⟨hfr7, hsp6.of_dmem hd7, (r7 .X22 (by simp)).trans y22, ?_, ?_, ?_,
    by omega, ?_, ?_, ?_, hr1⟩, hpc7'⟩))
  · -- the factor
    have h24 : s7.data.regs.X24 = kmul m0.regs.X2 (rdOf m0 0).beta.c0 :=
      ((r7 .X24 (by simp)).trans ((r6 .X24 (by simp)).trans (hsv5.1 .X24 rfl))).trans g24
    have h25 : s7.data.regs.X25 = kmul m0.regs.X2 (rdOf m0 0).beta.c1 :=
      (UInt64.toBitVec_inj.mp (hm9.regs .X25 _ rfl)).trans ((r6 .X0 (by simp)).trans k25)
    have h27 : s7.data.regs.X27 = (rdOf m0 0).alpha.c0 :=
      ((r7 .X27 (by simp)).trans ((r6 .X27 (by simp)).trans (r5 .X27 (by simp)))).trans f27
    have h28 : s7.data.regs.X28 = (rdOf m0 0).alpha.c1 :=
      ((r7 .X28 (by simp)).trans ((r6 .X28 (by simp)).trans (r5 .X28 (by simp)))).trans f28
    rw [h27, h28]
    exact fac_eq h24 h25
  · show (s7.data.regs.getXReg .X26).toBitVec.toNat = _
    rw [r7 .X26 (by simp)]
    exact h26
  · show (s7.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [hm9.regs .X29 _ rfl]
    rfl
  · refine (hm9.regs .X20 _ rfl).trans ?_
    sym_simp
    rw [lv]
    rfl
  · refine (hm9.regs .X23 _ rfl).trans ?_
    sym_simp
    rw [lv]
    rfl
  · rw [foldPart_zero, hd7]
    exact hl6

end

end NativeRustcVmArm.Whir.FoldRow
