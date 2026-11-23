module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Whir.InducedWeight.Inv

/-!
# `induced_weight`'s product loop

A turn (`inner_step`): `b9` loads the point's element `i` and `What_i` and calls `kmul`
(`(1 ⊕ What_i)·r₀`), `b10` calls `kmul` (`(1 ⊕ What_i)·r₁`), `b11` multiplies the product by the
factor (`EW::mul`), `b12` counts; after the last, `b13` goes to the sum (`Acc`).
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf)

public section

/-- Element `i` of an argument slice, in a body. -/
theorem slice_get {m0 st : MachineData} (hfr : Fr m0 st) (hS : StackOk m0 inducedWeightStack)
    {a n : UInt64} (h : SliceOk m0 a n inducedWeightStack) {i : Nat} (hi : i < n.toNat) :
    ewOf st.dmem (a.toBitVec + BitVec.ofNat 64 (16 * i)) = (slice m0 a n)[i]'(by simpa [slice]) := by
  simp only [slice, List.getElem_toArray, NativeRustcVm.getElem_ewsOf]
  refine NativeRustcVm.ewOf_congr fun b hb ↦ ?_
  rw [addr_add]
  exact hfr.get?_arg hS h (fun r hr ↦ absurd hr List.not_mem_nil) _ (by omega)

variable [Host] {k : Nat}

/-- **A turn of the product loop.** -/
theorem inner_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j i : Nat} {st : MachineData}
    (hI : IInv m0 j i st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Acc m0 j s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset)) ∨
        (IInv m0 j (i + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b9Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b9Offset)⟩ := by
  obtain ⟨hS, hqin, hwin, hpin, hout⟩ := hpre
  have hF : 1200 ≤ inducedWeightStack := by decide
  have hkle : 1200 + kmulStack ≤ inducedWeightStack := by decide
  have hmle : 1200 + ewMulStack ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hi := hI.hi
  have hL : lenOf m0 j ≤ (ptOf m0).size ∧ lenOf m0 j ≤ (whatOf m0 j).size :=
    ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩
  have hip : i < m0.regs.X7.toNat := by rw [← ptOf_size]; omega
  have hiw : i < (whatOf m0 j).size := by omega
  have hw31 : (whatOf m0 j).toList.length ≤ 31 := hI.what.1
  have hiw' : i < 31 := by simp at hw31; omega
  -- `b9`: the point's element, `What_i`, `kmul`
  let pa := m0.regs.X6.toBitVec + BitVec.ofNat 64 (16 * i)
  let wa := fbOf m0 + BitVec.ofNat 64 (600 + 8 * i)
  have hprd : Readable st pa 16 := hfr.readable (Readable.sub hpin.1 (by omega))
  have hwrd : Readable st wa 8 := hfr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  have hap : Apart pa 16 wa 8 := by
    have h0 := apart_frame hpin.2 hF hS.2.1
    have hfb : (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 1200 := hfe
    have hnw : m0.regs.X6.toBitVec.toNat + 16 * m0.regs.X7.toNat ≤ 2 ^ 64 := hpin.1.2
    have hfnw' : (fbOf m0).toNat + 1200 ≤ 2 ^ 64 := hfnw
    unfold Apart at h0 ⊢
    rw [hfe] at h0
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  let env := Env.ofMachine st [(pa, 16), (wa, 8)]
  have hwf : env.WF :=
    Env.wf_of ⟨⟨hprd.1, hprd.2⟩, ⟨hwrd.1, hwrd.2⟩, trivial⟩ (List.pairwise_pair.mpr hap)
  have hm : Match env pS st :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), rfl, fun h ↦ absurd h (by decide), trivial⟩
      rfl
      ⟨by
        show st.regs.X23.toBitVec = pa + BitVec.ofInt 64 8
        rw [hI.x23, show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add],
       by
        show st.regs.X24.toBitVec = wa + BitVec.ofInt 64 0
        rw [hI.x24, show BitVec.ofInt 64 0 = BitVec.ofNat 64 0 from rfl,
          NativeRustcVm.addr_add_zero],
       trivial⟩
      trivial trivial trivial
  have hk9 : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b9Offset) := b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk9 run_b9 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb9 := after_eq run_b9 ▸ b9_keeps
  have hfr1 := hfr.of_regs hm hm1 hwf rfl hb9.1 hb9.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf hb9.2
  let c := (ptOf m0)[i]'(by omega)
  let v := (whatOf m0 j)[i]'hiw
  have hc : ewOf st.dmem pa = c := slice_get hfr hS hpin hip
  have hv : NativeRustcVm.wordOf st.dmem wa = v := by
    have := NativeRustcVm.wordsAt_getElem hI.what.2.2 (i := i) (by simpa using hiw)
    rw [show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, addr_add, addr_add,
      show 592 + (8 + 8 * i) = 600 + 8 * i by omega, Array.getElem_toList] at this
    exact NativeRustcVm.wordOf_of_wordAt this
  have lv : env.load 1 0 8 = v.toBitVec := by
    rw [load8_eq, show env.base 1 = wa from rfl, NativeRustcVm.addr_add_zero, ← hv]; rfl
  have lc0 : env.load 0 0 8 = c.c0.toBitVec := by
    rw [load8_eq, show env.base 0 = pa from rfl, NativeRustcVm.addr_add_zero, ← hc]; rfl
  have lc1 : env.load 0 8 8 = c.c1.toBitVec := by
    rw [load8_eq, show env.base 0 = pa from rfl, ← hc]; rfl
  have e0 : s1.data.regs.X0 = v ^^^ 1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X0 _ rfl).trans ?_
    sym_simp
    rw [lv]
    rfl
  have e1 : s1.data.regs.X1 = c.c0 := UInt64.toBitVec_inj.mp ((hm1.regs .X1 _ rfl).trans lc0)
  have e20 : s1.data.regs.X20 = v := UInt64.toBitVec_inj.mp ((hm1.regs .X20 _ rfl).trans lv)
  have e27 : s1.data.regs.X27 = c.c1 := UInt64.toBitVec_inj.mp ((hm1.regs .X27 _ rfl).trans lc1)
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hk0, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hk2 := keep_call hfr1 hkle hS hsame2
  -- `b10`: `kmul((1 ⊕ v), r₁)`
  have hk10 : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b10Offset) := b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b10Offset) := hpc2
  refine exec_at hk10 run_b10 (Env.wf_nil _) hpc2' (match_nil _) fun s3 hm3 hpc3 ↦ ?_
  have hb10 := after_eq run_b10 ▸ b10_keeps
  have hfr3 := hfr2.of_regs (match_nil _) hm3 (Env.wf_nil _) rfl hb10.1 hb10.2
  have hd3 : s3.data.dmem = s2.data.dmem := hm3.dmem_eq (Env.wf_nil _) hb10.2
  have f28 : s3.data.regs.X28 = kmul (v ^^^ 1) c.c0 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X28 _ rfl)).trans (hk0.trans (by rw [e0, e1]))
  have f0 : s3.data.regs.X0 = v ^^^ 1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm3.regs .X0 _ rfl).trans ?_
    sym_simp
    show s2.data.regs.X20.toBitVec ^^^ _ = _
    rw [show s2.data.regs.X20 = v from (hsv2.1 .X20 rfl).trans e20]
    rfl
  have f1 : s3.data.regs.X1 = c.c1 :=
    (UInt64.toBitVec_inj.mp (hm3.regs .X1 _ rfl)).trans ((hsv2.1 .X27 rfl).trans e27)
  refine call_then hpc3 hkmul (hfr3.stackOk hS rfl hkle) fun s4 hpc4 ⟨hk1, hsame4, hsv4⟩ ↦ ?_
  have hfr4 := hfr3.call hS hkle slots_le hsame4 hsv4
  have hk4 := keep_call hfr3 hkle hS hsame4
  -- `b11`: the product times the factor
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b11Offset) := hpc4
  refine exec_at hk11 run_b11 (Env.wf_nil _) hpc4' (match_nil _) fun s5 hm5 hpc5 ↦ ?_
  have hb11 := after_eq run_b11 ▸ b11_keeps
  have hfr5 := hfr4.of_regs (match_nil _) hm5 (Env.wf_nil _) rfl hb11.1 hb11.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq (Env.wf_nil _) hb11.2
  -- callee-saved registers since `b9`
  have c4 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X25, .X26, .X29],
      s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (hsv4.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm3 rfl rfl).trans (hsv2.1 _ rfl))
  have c1 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X25, .X26, .X29],
      s1.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm hm1 rfl rfl
  have hfac : (⟨s5.data.regs.X2, s5.data.regs.X3⟩ : EW) = indFactor c v := by
    rw [indFactor_eq, UInt64.xor_comm 1 v]
    have h3 : s5.data.regs.X3 = kmul (v ^^^ 1) c.c1 :=
      (UInt64.toBitVec_inj.mp (hm5.regs .X3 _ rfl)).trans (hk1.trans (by rw [f0, f1]))
    have h2 : s5.data.regs.X2 = kmul (v ^^^ 1) c.c0 ^^^ 1 := by
      apply UInt64.toBitVec_inj.mp
      refine (hm5.regs .X2 _ rfl).trans ?_
      sym_simp
      show s4.data.regs.X28.toBitVec ^^^ _ = _
      rw [show s4.data.regs.X28 = _ from (hsv4.1 .X28 rfl).trans f28]
      rfl
    rw [h2, h3]
  have hprod : (⟨s5.data.regs.X0, s5.data.regs.X1⟩ : EW) = prodOf m0 j i := by
    have h0 : s5.data.regs.X0 = (prodOf m0 j i).c0 :=
      (UInt64.toBitVec_inj.mp (hm5.regs .X0 _ rfl)).trans
        (((c4 .X25 (by simp)).trans (c1 .X25 (by simp))).trans hI.x25)
    have h1 : s5.data.regs.X1 = (prodOf m0 j i).c1 :=
      (UInt64.toBitVec_inj.mp (hm5.regs .X1 _ rfl)).trans
        (((c4 .X26 (by simp)).trans (c1 .X26 (by simp))).trans hI.x26)
    rw [h0, h1]
  refine call_then hpc5 hmul (hfr5.stackOk hS rfl hmle) fun s6 hpc6 ⟨hp0, hp1, hsame6, hsv6⟩ ↦ ?_
  have hfr6 := hfr5.call hS hmle slots_le hsame6 hsv6
  have hk6 := keep_call hfr5 hmle hS hsame6
  rw [hprod, hfac] at hp0 hp1
  have hnext : prodOf m0 j (i + 1) = EW.mul (prodOf m0 j i) (indFactor c v) :=
    indProd_succ _ _ _ (by omega) hiw
  -- `b12`: count
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc6' : s6.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b12Offset) := hpc6
  refine exec_at hk12 run_b12 (Env.wf_nil _) hpc6' (match_nil _) fun s7 hm7 hpc7 ↦ ?_
  have hb12 := after_eq run_b12 ▸ b12_keeps
  have hfr7 := hfr6.of_regs (match_nil _) hm7 (Env.wf_nil _) rfl hb12.1 hb12.2
  have hd7 : s7.data.dmem = s6.data.dmem := hm7.dmem_eq (Env.wf_nil _) hb12.2
  have c6 : ∀ r ∈ [XReg.X19, .X21, .X22, .X23, .X24, .X29],
      s6.data.regs.getXReg r = st.regs.getXReg r ∨ r = .X24 := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact .inr rfl
      | exact .inl ((hsv6.1 _ rfl).trans ((Match.reg_eq (match_nil _) hm5 rfl rfl).trans
          ((c4 _ (by simp)).trans (c1 _ (by simp)))))
  have g : ∀ r ∈ [XReg.X19, .X22, .X24, .X29], s7.data.regs.getXReg r = s6.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact Match.reg_eq (match_nil _) hm7 rfl rfl
  have keep : ∀ r ∈ [XReg.X19, .X22, .X29], s7.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;>
    exact (g _ (by simp)).trans ((c6 _ (by simp)).resolve_right (by decide))
  have hdm : ∀ i', 16 ≤ i' → i' < 592 → s7.data.dmem.get? (fbOf m0 + BitVec.ofNat 64 i') =
      st.dmem.get? (fbOf m0 + BitVec.ofNat 64 i') := fun i' h1 h2 ↦ by
    rw [hd7, hk6 i' (by omega) (by omega), hd5, hk4 i' (by omega) (by omega), hd3,
      hk2 i' (by omega) (by omega), hd1]
  have hsp7 : Spills m0 s7.data := hI.sp.mono hdm
  have x25 : s7.data.regs.X25 = (prodOf m0 j (i + 1)).c0 :=
    (UInt64.toBitVec_inj.mp (hm7.regs .X25 _ rfl)).trans (hp0.trans (by rw [hnext]))
  have x26 : s7.data.regs.X26 = (prodOf m0 j (i + 1)).c1 :=
    (UInt64.toBitVec_inj.mp (hm7.regs .X26 _ rfl)).trans (hp1.trans (by rw [hnext]))
  have h21 : (s6.data.regs.getXReg .X21).toBitVec.toNat = lenOf m0 j - i := by
    rcases c6 .X21 (by simp) with h | h
    · rw [h]; exact hI.x21
    · cases h
  simp only [PcOk] at hpc7
  sym_simp at hpc7
  rw [Env.ofMachine_regs, bv_beq_toNat, h21] at hpc7
  by_cases hlast : lenOf m0 j - i = 1
  · simp only [hlast, BitVec.toNat_ofNat, Nat.one_mod, decide_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at hpc7
    have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
    have hpc7' : s7.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b13Offset) := hpc7
    refine exec_at hk13 run_b13 (Env.wf_nil _) hpc7' (match_nil _) fun s8 hm8 hpc8 ↦ .done _ (.inl ⟨?_,
      by simp only [PcOk] at hpc8; rw [hpc8]; exact hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b5Offset) NativeRustcVmArm.Vm.InducedWeight.label_3_at⟩)
    have hb13 := after_eq run_b13 ▸ b13_keeps
    have hd8 : s8.data.dmem = s7.data.dmem := hm8.dmem_eq (Env.wf_nil _) hb13.2
    have r8 : ∀ r, s8.data.regs.getXReg r = s7.data.regs.getXReg r := fun r ↦
      Match.reg_eq (match_nil _) hm8 (r := r) (v := .reg r) (by cases r <;> rfl) (by cases r <;> rfl)
    have hli : lenOf m0 j = i + 1 := by omega
    refine ⟨hfr7.of_regs (match_nil _) hm8 (Env.wf_nil _) rfl hb13.1 hb13.2, hsp7.of_dmem hd8,
      ?_, ?_, ?_, hI.hj, ?_, ?_⟩
    · show (s8.data.regs.getXReg .X22).toNat = _
      rw [r8, keep .X22 (by simp)]; exact hI.x22
    · show s8.data.regs.getXReg .X19 = _
      rw [r8, keep .X19 (by simp)]; exact hI.x19
    · show s8.data.regs.getXReg .X29 = _
      rw [r8, keep .X29 (by simp)]; exact hI.x29
    · show s8.data.regs.getXReg .X25 = _
      rw [r8, hli]; exact x25
    · show s8.data.regs.getXReg .X26 = _
      rw [r8, hli]; exact x26
  · simp only [show ¬lenOf m0 j - i = 1 % 2 ^ 64 by simpa using hlast, BitVec.toNat_ofNat,
      decide_false, Bool.not_false, ↓reduceIte] at hpc7
    refine .done _ (.inr ⟨⟨hfr7, hsp7, ?_, ?_, ?_, ?_, hI.hj, x25, x26, ?_, ?_, ?_, by omega⟩,
      hpc7.trans (hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b9Offset) NativeRustcVmArm.Vm.InducedWeight.label_6_at)⟩)
    · refine bufWords_keep hI.what (lo := 0) (hi := 1200) (by omega) (by omega) fun i' _ h2 ↦ ?_
      rw [hd7, hk6 i' (by omega) h2, hd5, hk4 i' (by omega) h2, hd3, hk2 i' (by omega) h2, hd1]
    · show (s7.data.regs.getXReg .X22).toNat = _
      rw [keep .X22 (by simp)]; exact hI.x22
    · show s7.data.regs.getXReg .X19 = _
      rw [keep .X19 (by simp)]; exact hI.x19
    · show s7.data.regs.getXReg .X29 = _
      rw [keep .X29 (by simp)]; exact hI.x29
    · show (s7.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [hm7.regs .X21 _ rfl]
      sym_simp
      rw [Env.ofMachine_regs, BitVec.toNat_sub, h21]
      show (2 ^ 64 - 1 % 2 ^ 64 + (lenOf m0 j - i)) % 2 ^ 64 = _
      omega
    · refine (hm7.regs .X23 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs]
      rcases c6 .X23 (by simp) with h | h
      · rw [h]
        show st.regs.X23.toBitVec + _ = _
        rw [hI.x23, addr_add, show 16 * i + 8 + 16 = 16 * (i + 1) + 8 by omega]
      · cases h
    · show (s7.data.regs.getXReg .X24).toBitVec = _
      rw [g .X24 (by simp), hsv6.1 .X24 rfl, Match.reg_eq (match_nil _) hm5 rfl rfl, hsv4.1 .X24 rfl,
        Match.reg_eq (match_nil _) hm3 rfl rfl, hsv2.1 .X24 rfl]
      refine (hm1.regs .X24 _ rfl).trans ?_
      show wa + BitVec.ofInt 64 8 = _
      rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from rfl, addr_add,
        show 600 + 8 * i + 8 = 600 + 8 * (i + 1) by omega]

end

end NativeRustcVmArm.Whir.InducedWeight
