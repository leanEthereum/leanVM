module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.SubspaceTable.Names
public import NativeRustcVmArm.Whir.SubspaceTable.Inv

/-!
# `subspace_table`'s layer loop

At the head (`b15`) of turn `t` at word `j` (`IInv t j`): `b15` loads the word `v` and calls `kmul`
(`v²`), `b16` calls `kmul` (`last·v`), `b17` stores `v² + last·v` over the word and counts; after
the last word it falls through to `b18` (`Turned t`).
-/

namespace NativeRustcVmArm.Whir.SubspaceTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceTable NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region WordAt WordsAt)

public section

variable [Host] {k : Nat}

/-- **A word of the layer's loop.** -/
theorem inner_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hS : StackOk m0 subspaceTableStack) {t j : Nat} {st : MachineData}
    (hI : IInv m0 t j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (IInv m0 t (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset)) ∨
        (Turned m0 t s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b18Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset)⟩ := by
  have hF : 864 ≤ subspaceTableStack := by decide
  have hkle : 864 + kmulStack ≤ subspaceTableStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hT := hI.turn
  have hfr := hT.fr
  have hmu := hT.hmu
  have hj := hI.hj
  have htj := hI.htj
  have hlay0 := hI.layer
  obtain ⟨L, hLd⟩ : ∃ L, layerAt (muOf m0) t = L := ⟨_, rfl⟩
  rw [hLd] at hlay0
  have hL : L.length = muOf m0 := hLd ▸ layerAt_length _ _
  have hjL : j < L.length := by omega
  let a := fbOf m0 + BitVec.ofNat 64 (16 + 8 * j)
  have hilen := innerL_length L t j (by omega)
  have hlb : ((innerL L t j).flatMap NativeRustcVm.wordBytes).length = 8 * muOf m0 := by
    rw [NativeRustcVm.length_wordsBytes, hilen, hL]
  -- the word
  have hv : WordAt st.dmem a (L[j]'hjL) := by
    have := hlay0.getElem (i := j) (by omega)
    rw [innerL_getElem hjL, addr_add] at this
    exact this
  -- `b15`: load the word, call `kmul`
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st a 8 := hfr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env1 := Env.ofMachine st [(a, 8)]
  have hwf1 : env1.WF := wf_one hrd.1 hrd.2
  have hm1 : Match env1 wordS st := match_one (by
    show st.regs.X19.toBitVec = a + BitVec.ofInt 64 0
    rw [hI.x19]
    simp [a])
  refine exec_then hk15 run_b15 hwf1 hm1 fun s1 hm2 hpc1 ↦ ?_
  have hb15 := after_eq run_b15 ▸ b15_keeps
  have hfr1 := hfr.of_regs hm1 hm2 hwf1 rfl hb15.1 hb15.2
  have hd1 : s1.data.dmem = st.dmem := hm2.dmem_eq hwf1 hb15.2
  have hT1 : Turn m0 t s1.data := hT.store (o := 16) (n := 0) hS hfr1 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm1 hm2 rfl rfl)
    (fun p _ ↦ by rw [hd1]) le_rfl (by omega)
  have hld : env1.load 0 0 8 = (L[j]'hjL).toBitVec :=
    load_word (show WordAt st.dmem (a + BitVec.ofNat 64 0) _ by
      rw [NativeRustcVm.addr_add_zero]; exact hv)
  have hx0 : s1.data.regs.X0 = L[j]'hjL := UInt64.toBitVec_inj.mp ((hm2.regs .X0 _ rfl).trans hld)
  have hx1 : s1.data.regs.X1 = L[j]'hjL := UInt64.toBitVec_inj.mp ((hm2.regs .X1 _ rfl).trans hld)
  have hx22 : s1.data.regs.X22 = L[j]'hjL :=
    UInt64.toBitVec_inj.mp ((hm2.regs .X22 _ rfl).trans hld)
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hk2, hsame2, hsv2⟩ ↦ ?_
  have hT2 := hT1.call hS hkle hsame2 hsv2
  have hlay2 : WordsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (innerL L t j) :=
    hfr1.bytes_call hS hkle hsame2 (o := 16) (by rw [hlb]; omega) (hd1 ▸ hlay0)
  -- `b16`: call `kmul` for `last·v`
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b16Offset) := hpc2
  refine exec_at hk16 run_b16 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb16 := after_eq run_b16 ▸ b16_keeps
  have hfr3 := hT2.fr.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb16.1 hb16.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb16.2
  have hT3 : Turn m0 t s3.data := hT2.store (o := 16) (n := 0) hS hfr3 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact Match.reg_eq (match_nil _) hm3 rfl rfl)
    (fun p _ ↦ by rw [hd3]) le_rfl (by omega)
  have e21 : s2.data.regs.X21 = st.regs.X21 :=
    (hsv2.1 .X21 rfl).trans (Match.reg_eq hm1 hm2 rfl rfl)
  have hx0' : s3.data.regs.X0 = lastAt L t :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X0 _ rfl)).trans (e21.trans (hLd ▸ hI.x21))
  have hx1' : s3.data.regs.X1 = L[j]'hjL :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)).trans ((hsv2.1 .X22 rfl).trans hx22)
  have hx23 : s3.data.regs.X23 = kmul (L[j]'hjL) (L[j]'hjL) := by
    apply UInt64.toBitVec_inj.mp
    show (s3.data.regs.getXReg .X23).toBitVec = _
    rw [hm3.regs .X23 _ rfl]
    show s2.data.regs.X0.toBitVec = _
    rw [hk2, hx0, hx1]
  refine call_then hpc3 hkmul (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hk4, hsame4, hsv4⟩ ↦ ?_
  have hT4 := hT3.call hS hkle hsame4 hsv4
  have hlay4 : WordsAt s4.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (innerL L t j) :=
    hfr3.bytes_call hS hkle hsame4 (o := 16) (by rw [hlb]; omega) (hd3 ▸ hlay2)
  have hx0'' : s4.data.regs.X0 = kmul (lastAt L t) (L[j]'hjL) := by rw [hk4, hx0', hx1']
  have hx23' : s4.data.regs.X23 = kmul (L[j]'hjL) (L[j]'hjL) := (hsv4.1 .X23 rfl).trans hx23
  have e19 : s4.data.regs.X19 = st.regs.X19 :=
    (hsv4.1 .X19 rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans
      ((hsv2.1 .X19 rfl).trans (Match.reg_eq hm1 hm2 rfl rfl)))
  have e29 : s4.data.regs.X29 = st.regs.X29 :=
    (hsv4.1 .X29 rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans
      ((hsv2.1 .X29 rfl).trans (Match.reg_eq hm1 hm2 rfl rfl)))
  have e21s4 : s4.data.regs.X21 = st.regs.X21 :=
    (hsv4.1 .X21 rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans e21)
  -- `b17`: store `v² + last·v`, count
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.SubspaceTable.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b17Offset) := hpc4
  have hrd4 : Readable s4.data a 8 := hT4.fr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env5 := Env.ofMachine s4.data [(a, 8)]
  have hwf5 : env5.WF := wf_one hrd4.1 hrd4.2
  have hm5 : Match env5 wordS s4.data := match_one (by
    show s4.data.regs.X19.toBitVec = a + BitVec.ofInt 64 0
    rw [e19, hI.x19]
    simp [a])
  refine exec_at hk17 run_b17 hwf5 hpc4' hm5 fun s5 hm6 hpc5 ↦ ?_
  have hb17 := after_eq run_b17 ▸ b17_keeps
  have hsame5 := same_region hm6 hwf5 (r := 0) rfl hb17.2
  have hfr5 := hT4.fr.of_block hm5 hm6 hwf5 rfl hb17.1 (r := 0) rfl le_rfl hb17.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 16 + 8 * j) (n := 8) (by omega) h))
    (fun q hq i hi ↦ not_inRange_slot hS hF (o := 16 + 8 * j) (n := 8) (by omega)
      (slots_le q hq) hi (.inl (by have := slots_ge q hq; omega)))
  have hT5 : Turn m0 t s5.data := hT4.store (o := 16 + 8 * j) (n := 8) hS hfr5 (fun r hr ↦ by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm5 hm6 rfl rfl)
    hsame5 (by omega) (by omega)
  have x21' : s5.data.regs.X21 = lastAt (layerAt (muOf m0) t) t :=
    (Match.reg_eq (r := .X21) hm5 hm6 rfl rfl).trans (e21s4.trans hI.x21)
  have hw : WordAt s5.data.dmem (fbOf m0 + BitVec.ofNat 64 16 + BitVec.ofNat 64 (8 * j))
      (sqStep (lastAt L t) (L[j]'hjL)) := by
    have := Match.wordAt_write hm6 (r := 0) (o := 0) rfl (by decide)
      (v := .bin .eor .W64 (.reg .X0) (.reg .X23)) (by decide)
    have hval : UInt64.ofBitVec ((Sym.bin .eor .W64 (.reg .X0) (.reg .X23)).eval env5) =
        sqStep (lastAt L t) (L[j]'hjL) := by
      apply UInt64.toBitVec_inj.mp
      sym_simp
      show s4.data.regs.X0.toBitVec ^^^ s4.data.regs.X23.toBitVec = _
      rw [hx0'', hx23', sqStep, UInt64.toBitVec_xor, BitVec.xor_comm]
    rw [hval, NativeRustcVm.addr_add_zero] at this
    rw [addr_add]
    exact this
  have hlay5 : WordsAt s5.data.dmem (fbOf m0 + BitVec.ofNat 64 16) (innerL L t (j + 1)) := by
    rw [← innerL_set htj hjL]
    refine NativeRustcVm.WordsAt.set hlay4 hw ?_ (by omega)
      (NativeRustcVm.NoWrap.sub hfnw (by rw [hilen, hL]; omega))
    rw [addr_add]
    exact hsame5
  have e29' : s5.data.regs.X29.toNat = 8 * (muOf m0 - (j + 1)) := by
    have h8 : 8 ≤ st.regs.X29.toNat := by have := hI.x29; omega
    show (s5.data.regs.getXReg .X29).toBitVec.toNat = _
    rw [hm6.regs .X29 _ rfl]
    sym_simp
    show (s4.data.regs.X29.toBitVec - _).toNat = _
    rw [e29, toNat_sub_ofNat h8]
    have := hI.x29
    show st.regs.X29.toNat - 8 = _
    omega
  have e19' : s5.data.regs.X19.toBitVec = fbOf m0 + BitVec.ofNat 64 (16 + 8 * (j + 1)) := by
    show (s5.data.regs.getXReg .X19).toBitVec = _
    rw [hm6.regs .X19 _ rfl]
    simp only [Sym.eval, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl]
    show a + BitVec.ofNat 64 8 = _
    rw [addr_add]
    congr 2
  simp only [PcOk] at hpc5
  sym_simp at hpc5
  simp only [bv_beq_toNat] at hpc5
  have h29 : (env5.regs .X29).toNat = 8 * (muOf m0 - j) := by
    show s4.data.regs.X29.toNat = _
    rw [e29]
    exact hI.x29
  rw [h29] at hpc5
  by_cases hlast : j + 1 = muOf m0
  · simp only [show 8 * (muOf m0 - j) = (BitVec.ofNat 64 8).toNat by
        rw [BitVec.toNat_ofNat]; omega, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at hpc5
    refine .done _ (.inr ⟨⟨hT5, ?_, x21'⟩, hpc5⟩)
    rw [show j + 1 = L.length by omega, innerL_end] at hlay5
    rw [layerAt, hLd]
    exact hlay5
  · have hne : decide (8 * (muOf m0 - j) = (BitVec.ofNat 64 8).toNat) = false := by
      rw [decide_eq_false_iff_not, BitVec.toNat_ofNat]
      omega
    simp only [hne, Bool.not_false, ↓reduceIte] at hpc5
    have hl : Labels.label NativeRustcVmArm.Vm.SubspaceTable.label_13 = Host.addrOf (k + NativeRustcVmArm.Vm.SubspaceTable.b15Offset) := hp.label (j := NativeRustcVmArm.Vm.SubspaceTable.b15Offset) NativeRustcVmArm.Vm.SubspaceTable.label_13_at
    exact .done _ (.inl ⟨⟨hT5, x21', hLd ▸ hlay5, e19', e29', by omega, by omega⟩,
      hpc5.trans hl⟩)

end

end NativeRustcVmArm.Whir.SubspaceTable
