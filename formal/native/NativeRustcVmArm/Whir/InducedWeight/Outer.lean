module

public import NativeRustcVmArm.Code.Vm.EWMul.Names
public import NativeRustcVmArm.Code.Vm.InducedWeight.Names
public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable.Names
public import NativeRustcVmArm.Whir.InducedWeight.Inner

/-!
# `induced_weight`'s queries' loop

A turn (`outer_step`) from the head `b6` after `j` queries (`OInv`): `b6` loads weight `j` and
query `j` and calls `subspace_at_table` (the `What`s at 592, the table's copy at 96 read back,
`pairsOf_of_pairsAt`); `b7` goes straight to the sum (`Acc`) when there is no factor, else `b8`
starts the product loop (`inner_step`, by `Sym.loop`). The sum (`sum_step`, `b5`) adds the product
to the total and goes back to `b6` (`OInv`), or to the store (`Done`) after the last query.
-/

namespace NativeRustcVmArm.Whir.InducedWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InducedWeight NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm
open NativeRustcVm (Region wordOf ewOf ewsOf WordAt WordsAt)

public section

theorem shl4_eq (x : BitVec 64) : x <<< 4 = BitVec.ofNat 64 (16 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  omega

theorem ext3_eq (x : BitVec 64) :
    BitVec.ofInt 64 (x.apply_mem_extend ⟨.UXTX, .E3⟩) = BitVec.ofNat 64 (8 * x.toNat) := by
  simp only [BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  rw [show ((x.toNat : Int) * 2 ^ 3) = ((8 * x.toNat : Nat) : Int) by push_cast; omega,
    BitVec.ofInt_natCast]

/-- Word `i` of words at a frame offset. -/
theorem word_at {d : DataMem} {a : BitVec 64} {o : Nat} {xs : List UInt64}
    (h : WordsAt d (a + BitVec.ofNat 64 o) xs) (i : Nat) (hi : i < xs.length) :
    WordAt d (a + BitVec.ofNat 64 (o + 8 * i)) xs[i] := by
  have := NativeRustcVm.wordsAt_getElem h hi
  rwa [addr_add] at this

/-- A frame word, loaded. -/
theorem load_fr {m0 st : MachineData} {rs : List (BitVec 64 × Nat)} {o : Nat} {v : UInt64}
    (h : WordAt st.dmem (fbOf m0 + BitVec.ofNat 64 o) v) :
    (Env.ofMachine st ((fbOf m0, 1200) :: rs)).load 0 o 8 = v.toBitVec :=
  load_word h

/-- A frame range is an input of a callee using `N` bytes of stack. -/
theorem whirIn_frame {m0 st : MachineData} (hS : StackOk m0 inducedWeightStack) (hfr : Fr m0 st)
    {o n N : Nat} (h : o + n ≤ 1200) (hN : 1200 + N ≤ inducedWeightStack) :
    WhirIn st (fbOf m0 + BitVec.ofNat 64 o) n N := by
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS (show 1200 ≤ inducedWeightStack by decide)
  refine ⟨hfr.readable (Readable.sub ⟨hfmap, hfnw⟩ h), ?_⟩
  have hS' : inducedWeightStack ≤ m0.regs.SP.toNat := hS.2.1
  have hlt := m0.regs.SP.toBitVec.isLt
  have hsp : m0.regs.SP.toNat = m0.regs.SP.toBitVec.toNat := rfl
  unfold OffStack Apart stackBelow fbOf
  rw [hfr.sp]
  right
  rw [toNat_sub_ofNat (by rw [hfe]; omega), hfe, toNat_add_ofNat' (by rw [hfe]; omega), hfe]
  omega

theorem getD_eq {α : Type} (a : Array α) {i : Nat} (v : α) (h : i < a.size) :
    a.getD i v = a[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- `csel lo`: the minimum. -/
theorem ite_min (a b : BitVec 64) :
    (if a.ult b = true then a else b).toNat = min a.toNat b.toNat := by
  rw [bv_ult_toNat]
  by_cases h : a.toNat < b.toNat
  · simp only [h, decide_true, ↓reduceIte]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- `b7`'s branch: to the sum iff there is no factor (at most 31 `What`s). -/
theorem b7_cond (a b : BitVec 64) (ha : a.toNat ≤ 31) :
    ((if (!((if a.ult b = true then a else b) == 0#64)) = true then !a.ult 31#64 else true) &&
      !(if (!((if a.ult b = true then a else b) == 0#64)) = true then a == 31#64 else false)) =
      decide (min a.toNat b.toNat = 0) := by
  have hm := ite_min a b
  generalize (if a.ult b = true then a else b) = c at hm ⊢
  rw [bv_beq_toNat, hm, bv_ult_toNat, bv_beq_toNat]
  by_cases h0 : min a.toNat b.toNat = 0
  · simp [h0]
  · by_cases h31 : a.toNat = 31
    · simp [h31]
    · simp [h0, h31]
      omega

variable [Host] {k : Nat}

/-- **A turn of the queries' loop**: query `j`'s product. -/
theorem outer_step (hp : Placed code k)
    (hsat : Spec (label NativeRustcVmArm.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    (hmul : Spec (label NativeRustcVmArm.Vm.EWMul.entryLabel) EWMulPre EWMulPost)
    {m0 : MachineData} (hpre : InducedWeightPre m0) {j : Nat} {st : MachineData}
    (hI : OInv m0 j st) :
    Eventually (step1 Host.exe) (fun s ↦ Acc m0 j s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b6Offset)⟩ := by
  have hpre' := hpre
  obtain ⟨hS, hqin, hwin, hpin, hout⟩ := hpre'
  have hF : 1200 ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have hfr := hI.fr
  have hsp := hI.sp
  have hjc := hI.hj
  have hjw : j < m0.regs.X5.toNat := by unfold cntOf at hjc; omega
  have hjq : j < m0.regs.X3.toNat := by unfold cntOf at hjc; omega
  have hx22 : (st.regs.getXReg .X22).toBitVec.toNat = j := hI.x22
  -- `b6a`: weight `j`
  let wa := m0.regs.X4.toBitVec + BitVec.ofNat 64 (16 * j)
  have hwrd : Readable st wa 16 := hfr.readable (Readable.sub hwin.1 (by omega))
  have hfb : (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 1200 := hfe
  have hapw : Apart (fbOf m0) 1200 wa 16 := by
    have h0 := apart_frame hwin.2 hF hS.2.1
    have hnw : m0.regs.X4.toBitVec.toNat + 16 * m0.regs.X5.toNat ≤ 2 ^ 64 := hwin.1.2
    unfold Apart at h0 ⊢
    rw [hfe] at h0
    rw [toNat_add_ofNat' (by omega)]
    omega
  let env6 := Env.ofMachine st [(fbOf m0, 1200), (wa, 16)]
  have hwf6 : env6.WF :=
    Env.wf_of ⟨⟨(hfr.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨hwrd.1, hwrd.2⟩, trivial⟩
      (List.pairwise_pair.mpr hapw)
  have hm6 : Match env6 qaS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial
      ⟨by
        show wAddr.eval env6 = wa + BitVec.ofInt 64 0
        simp only [wAddr]
        sym_simp
        rw [load_fr (word_at hsp.args 1 (by simp)), shl4_eq,
          show env6.regs .X22 = (st.regs.getXReg .X22).toBitVec from rfl, hx22]
        simp [wa], trivial⟩
  have hk6a : b6a.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b6Offset) :=
    (show b6a.IsInfixAt b6 0 from ⟨b6b, by rw [List.drop_zero, b6_split]⟩).trans
      (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) (List.cons_ne_nil _ _)
  refine exec_then hk6a run_b6a hwf6 hm6 fun s1 hm1 hpc1 ↦ ?_
  have hb6a := after_eq run_b6a ▸ b6a_keeps
  have hfr1 := hfr.of_regs hm6 hm1 hwf6 rfl hb6a.1 hb6a.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf6 hb6a.2
  have r1 : ∀ r ∈ [XReg.X19, .X22, .X29], s1.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact Match.reg_eq hm6 hm1 rfl rfl
  have hjws : j < (wsOf m0).size := by rw [wsOf_size]; exact hjw
  have hjqs : j < (qsOf m0).size := by rw [qsOf_size]; exact hjq
  let w := (wsOf m0)[j]'hjws
  have hw : ewOf st.dmem wa = w := slice_get hfr hS hwin hjw
  have e25 : s1.data.regs.X25 = w.c0 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X25 _ rfl).trans ?_
    show env6.load 1 0 8 = _
    rw [load8_eq, show env6.base 1 = wa from rfl, NativeRustcVm.addr_add_zero, ← hw]; rfl
  have e26 : s1.data.regs.X26 = w.c1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X26 _ rfl).trans ?_
    show env6.load 1 8 8 = _
    rw [load8_eq, show env6.base 1 = wa from rfl, ← hw]; rfl
  have e0 : s1.data.regs.X0.toBitVec = fbOf m0 + BitVec.ofNat 64 592 :=
    (hm1.regs .X0 _ rfl).trans rfl
  have e1 : s1.data.regs.X1.toBitVec = fbOf m0 + BitVec.ofNat 64 96 :=
    (hm1.regs .X1 _ rfl).trans (load_fr (word_at hsp.ptrs 3 (by simp)))
  have e2 : s1.data.regs.X2 = (tbOf m0).size.toUInt64 :=
    UInt64.toBitVec_inj.mp ((hm1.regs .X2 _ rfl).trans (load_fr (word_at hsp.ptrs 2 (by simp))))
  -- `b6b`: query `j`, `subspace_at_table`
  let qa := m0.regs.X2.toBitVec + BitVec.ofNat 64 (8 * j)
  have hqrd : Readable s1.data qa 8 := hfr1.readable (Readable.sub hqin.1 (by omega))
  have hapq : Apart (fbOf m0) 1200 qa 8 := by
    have h0 := apart_frame hqin.2 hF hS.2.1
    have hnw : m0.regs.X2.toBitVec.toNat + 8 * m0.regs.X3.toNat ≤ 2 ^ 64 := hqin.1.2
    unfold Apart at h0 ⊢
    rw [hfe] at h0
    rw [toNat_add_ofNat' (by omega)]
    omega
  let env7 := Env.ofMachine s1.data [(fbOf m0, 1200), (qa, 8)]
  have hwf7 : env7.WF :=
    Env.wf_of ⟨⟨(hfr1.readable ⟨hfmap, hfnw⟩).1, hfnw⟩, ⟨hqrd.1, hqrd.2⟩, trivial⟩
      (List.pairwise_pair.mpr hapq)
  have hx22' : (s1.data.regs.getXReg .X22).toBitVec.toNat = j := by
    rw [r1 .X22 (by simp)]; exact hx22
  have hsp1 : Spills m0 s1.data := hsp.of_dmem hd1
  have hm7 : Match env7 qbS s1.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, rfl, fun h ↦ absurd h (by decide),
        trivial⟩
      (by rw [hfr1.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial
      ⟨by
        show qAddr.eval env7 = qa + BitVec.ofInt 64 0
        simp only [qAddr]
        sym_simp
        rw [load_fr (word_at hsp1.args 0 (by simp)), ext3_eq]
        rw [show env7.regs .X22 = (s1.data.regs.getXReg .X22).toBitVec from rfl, hx22']
        simp [qa], trivial⟩
  -- Interior cut: b6a's six directives establish the window needed to execute b6b.
  have hk6b : b6b.IsInfixAt Host.prog (k + (NativeRustcVmArm.Vm.InducedWeight.b6Offset + 6)) :=
    (show b6b.IsInfixAt b6 6 from ⟨[], List.append_nil _⟩).trans
      (b6_in_code.trans hp.1 (List.cons_ne_nil _ _)) (by intro h; cases h)
  have hpc1' : s1.pc = Host.addrOf (k + (NativeRustcVmArm.Vm.InducedWeight.b6Offset + 6)) := hpc1
  refine exec_at hk6b run_b6b hwf7 hpc1' hm7 fun s2 hm2 hpc2 ↦ ?_
  have hb6b := after_eq run_b6b ▸ b6b_keeps
  have hfr2 := hfr1.of_regs hm7 hm2 hwf7 rfl hb6b.1 hb6b.2
  have hd2 : s2.data.dmem = st.dmem := (hm2.dmem_eq hwf7 hb6b.2).trans hd1
  have r2 : ∀ r ∈ [XReg.X0, .X1, .X2, .X19, .X22, .X25, .X26, .X29],
      s2.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact Match.reg_eq hm7 hm2 rfl rfl
  have hargs := hfr.get?_arg hS hqin (fun r hr ↦ absurd hr List.not_mem_nil)
  let q := (qsOf m0)[j]'hjqs
  have hq : wordOf st.dmem qa = q := by
    simp only [q, qsOf, wordSlice, List.getElem_toArray, NativeRustcVm.getElem_wordsOf]
    refine NativeRustcVm.wordOf_congr fun i hi ↦ ?_
    rw [addr_add]
    exact hargs _ (by omega)
  have e3 : s2.data.regs.X3 = q := by
    apply UInt64.toBitVec_inj.mp
    refine (hm2.regs .X3 _ rfl).trans ?_
    show env7.load 1 0 8 = _
    rw [load8_eq, show env7.base 1 = qa from rfl, NativeRustcVm.addr_add_zero,
      show env7.mem0 = st.dmem from hd1, hq]
  have hts : (tbOf m0).size ≤ 31 := by
    have := hsp.table.1
    rw [Array.length_toList] at this
    exact this
  have f0 : s2.data.regs.X0.toBitVec = fbOf m0 + BitVec.ofNat 64 592 := by
    rw [show s2.data.regs.X0 = s1.data.regs.X0 from r2 .X0 (by simp)]; exact e0
  have f1 : s2.data.regs.X1.toBitVec = fbOf m0 + BitVec.ofNat 64 96 := by
    rw [show s2.data.regs.X1 = s1.data.regs.X1 from r2 .X1 (by simp)]; exact e1
  have f2 : s2.data.regs.X2.toNat = (tbOf m0).size := by
    rw [show s2.data.regs.X2 = s1.data.regs.X2 from r2 .X2 (by simp), e2]
    exact natCast_toUInt64_toNat (by omega)
  have hNle : 1200 + subspaceAtTableStack ≤ inducedWeightStack := by decide
  have hlt := m0.regs.SP.toBitVec.isLt
  have hSP : inducedWeightStack ≤ m0.regs.SP.toBitVec.toNat := hS.2.1
  have hP : SubspaceAtTablePre s2.data := by
    unfold SubspaceAtTablePre
    rw [f0, f1, f2]
    refine ⟨hfr2.stackOk hS rfl hNle, hts, whirIn_frame hS hfr2 (by omega) hNle,
      whirIn_frame hS hfr2 (by decide) hNle, Or.inr ?_⟩
    rw [toNat_add_ofNat' (by omega), toNat_add_ofNat' (by omega)]
    omega
  refine call_then hpc2 hsat hP fun s3 hpc3 ⟨hval, hch, hsv⟩ ↦ ?_
  have hpairs : pairsOf s2.data.dmem (fbOf m0 + BitVec.ofNat 64 96) (tbOf m0).size =
      (tbOf m0).toList := by
    have := pairsOf_of_pairsAt hsp.table.2.2
    simp only [NativeRustcVm.Transcript.off, addr_add, Array.length_toList] at this
    rw [hd2]
    exact this
  have hwj : whatOf m0 j = subspaceAtTable (tbOf m0) q := by
    unfold whatOf subspaceAt
    rw [getD_eq _ _ hjqs]
    rfl
  rw [f0, f1, f2, e3, hpairs, Array.toArray_toList, ← hwj] at hval
  rw [f0] at hch
  have hfr3 : Fr m0 s3.data := hfr2.call_out hS hNle (o := 592) (n := 256) (by decide) (by decide)
    hch hsv
  have hk3 := keep_call_out hfr2 hNle hS (n := 256) (by decide) hch
  have hsp3 : Spills m0 s3.data := (hsp.of_dmem hd2).mono hk3
  -- `b7`: any factor?
  let env8 := Env.ofMachine s3.data [(fbOf m0, 1200)]
  have hwf8 : env8.WF := wf_one (hfr3.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm8 : Match env8 frS s3.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr3.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc3' : s3.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b7Offset) := hpc3
  refine exec_at hk7 run_b7 hwf8 hpc3' hm8 fun s4 hm4 hpc4 ↦ ?_
  have l592 : env8.load 0 592 8 = (whatOf m0 j).toList.length.toUInt64.toBitVec :=
    load_fr hval.2.1
  have l80 : env8.load 0 80 8 = m0.regs.X7.toBitVec := load_fr (word_at hsp3.args 2 (by simp))
  simp only [PcOk] at hpc4
  sym_simp at hpc4
  rw [l592, l80] at hpc4
  have hL31 : (whatOf m0 j).toList.length ≤ 31 := hval.1
  have hLn : (whatOf m0 j).toList.length.toUInt64.toBitVec.toNat = (whatOf m0 j).toList.length :=
    natCast_toUInt64_toNat (by omega)
  have hlenEq : min (whatOf m0 j).toList.length.toUInt64.toBitVec.toNat m0.regs.X7.toBitVec.toNat =
      lenOf m0 j := by
    have : (ptOf m0).size = m0.regs.X7.toBitVec.toNat := ptOf_size m0
    unfold lenOf
    rw [hLn, this, Array.length_toList]
    exact Nat.min_comm _ _
  rw [b7_cond _ _ (by omega), hlenEq] at hpc4
  have hb7 := after_eq run_b7 ▸ b7_keeps
  have hfr4 := hfr3.of_regs hm8 hm4 hwf8 rfl hb7.1 hb7.2
  have hd4 : s4.data.dmem = s3.data.dmem := hm4.dmem_eq hwf8 hb7.2
  have c4 : ∀ r ∈ [XReg.X19, .X22, .X25, .X26, .X29],
      s4.data.regs.getXReg r = s1.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
      exact (Match.reg_eq hm8 hm4 rfl rfl).trans ((hsv.1 _ rfl).trans (r2 _ (by simp)))
  have hprod0 : prodOf m0 j 0 = w := by
    unfold prodOf
    rw [indProd_zero, getD_eq _ _ hjws]
  have h21 : (s4.data.regs.getXReg .X21).toBitVec.toNat = lenOf m0 j := by
    rw [hm4.regs .X21 _ rfl]
    sym_simp
    rw [l592, l80, ite_min, hlenEq]
  by_cases h0 : lenOf m0 j = 0
  · -- no factor: the product is the weight
    simp only [h0, decide_true, ↓reduceIte] at hpc4
    rw [show Labels.label NativeRustcVmArm.Vm.InducedWeight.label_3 = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset) from hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b5Offset) NativeRustcVmArm.Vm.InducedWeight.label_3_at] at hpc4
    refine .done _ ⟨⟨hfr4, hsp3.of_dmem hd4, ?_, ?_, ?_, hjc, ?_, ?_⟩, hpc4⟩
    · show (s4.data.regs.getXReg .X22).toNat = _
      rw [c4 .X22 (by simp), r1 .X22 (by simp)]; exact hI.x22
    · show s4.data.regs.getXReg .X19 = _
      rw [c4 .X19 (by simp), r1 .X19 (by simp)]; exact hI.x19
    · show s4.data.regs.getXReg .X29 = _
      rw [c4 .X29 (by simp), r1 .X29 (by simp)]; exact hI.x29
    · show s4.data.regs.getXReg .X25 = _
      rw [c4 .X25 (by simp), h0, hprod0]; exact e25
    · show s4.data.regs.getXReg .X26 = _
      rw [c4 .X26 (by simp), h0, hprod0]; exact e26
  simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc4
  -- `b8`: the point's and the `What`s' cursors
  let env9 := Env.ofMachine s4.data [(fbOf m0, 1200)]
  have hwf9 : env9.WF := wf_one (hfr4.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm9 : Match env9 frS s4.data :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr4.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  have hk8 : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b8Offset) := b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc4' : s4.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b8Offset) := hpc4
  refine exec_at hk8 run_b8 hwf9 hpc4' hm9 fun s5 hm5 hpc5 ↦ ?_
  have hb8 := after_eq run_b8 ▸ b8_keeps
  have hfr5 := hfr4.of_regs hm9 hm5 hwf9 rfl hb8.1 hb8.2
  have hd5 : s5.data.dmem = s4.data.dmem := hm5.dmem_eq hwf9 hb8.2
  have hsp4 : Spills m0 s4.data := hsp3.of_dmem hd4
  have c5 : ∀ r ∈ [XReg.X19, .X21, .X22, .X25, .X26, .X29],
      s5.data.regs.getXReg r = s4.data.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact Match.reg_eq hm9 hm5 rfl rfl
  have hI0 : IInv m0 j 0 s5.data := by
    refine ⟨hfr5, hsp4.of_dmem hd5, ?_, ?_, ?_, ?_, hjc, ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [hd5, hd4]; exact hval
    · show (s5.data.regs.getXReg .X22).toNat = _
      rw [c5 .X22 (by simp), c4 .X22 (by simp), r1 .X22 (by simp)]; exact hI.x22
    · show s5.data.regs.getXReg .X19 = _
      rw [c5 .X19 (by simp), c4 .X19 (by simp), r1 .X19 (by simp)]; exact hI.x19
    · show s5.data.regs.getXReg .X29 = _
      rw [c5 .X29 (by simp), c4 .X29 (by simp), r1 .X29 (by simp)]; exact hI.x29
    · show s5.data.regs.getXReg .X25 = _
      rw [c5 .X25 (by simp), c4 .X25 (by simp), hprod0]; exact e25
    · show s5.data.regs.getXReg .X26 = _
      rw [c5 .X26 (by simp), c4 .X26 (by simp), hprod0]; exact e26
    · show (s5.data.regs.getXReg .X21).toBitVec.toNat = _
      rw [c5 .X21 (by simp), h21]; rfl
    · refine (hm5.regs .X23 _ rfl).trans ?_
      refine (load_fr (word_at hsp4.ptrs 0 (by simp))).trans ?_
      simp
    · exact (hm5.regs .X24 _ rfl).trans (load_fr (word_at hsp4.ptrs 1 (by simp)))
  have hpc5' : s5.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b9Offset) := hpc5
  -- the product loop
  exact Sym.loop (tr := step1 Host.exe)
    (Q := fun s ↦ Acc m0 j s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset))
    (fun n s ↦ ∃ i, n = lenOf m0 j - i ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b9Offset) ∧ IInv m0 j i s.data)
    (fun n s ⟨i, hn', hpc, hI'⟩ ↦ by
      obtain ⟨d, pc⟩ := s
      simp only at hpc
      subst hpc
      refine (inner_step hp hkmul hmul hpre hI').mono fun s' h ↦ ?_
      rcases h with h | ⟨hI'', hpc'⟩
      · exact .inl h
      · exact .inr ⟨lenOf m0 j - (i + 1), by have := hI'.hi; omega, i + 1, rfl, hpc', hI''⟩)
    (n := lenOf m0 j) ⟨0, by omega, hpc5', hI0⟩

/-- **The sum** (`b5`): query `j`'s product added; the next query, or the store after the last. -/
theorem sum_step (hp : Placed code k) {m0 : MachineData} (hpre : InducedWeightPre m0) {j : Nat}
    {st : MachineData} (hA : Acc m0 j st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (OInv m0 (j + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b6Offset)) ∨
        (Done m0 s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b15Offset)))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset)⟩ := by
  have hS := hpre.1
  have hF : 1200 ≤ inducedWeightStack := by decide
  obtain ⟨hfmap, hfnw, -⟩ := frame_ok hS hF
  have hfr := hA.fr
  have hsp := hA.sp
  have hjc := hA.hj
  have hjws : j < (wsOf m0).size := by rw [wsOf_size]; unfold cntOf at hjc; omega
  have hjqs : j < (qsOf m0).size := by rw [qsOf_size]; unfold cntOf at hjc; omega
  have hc64 : cntOf m0 < 2 ^ 64 := by unfold cntOf; have := m0.regs.X5.toNat_lt; omega
  have hwf : (Env.ofMachine st [(fbOf m0, 1200)]).WF :=
    wf_one (hfr.readable ⟨hfmap, hfnw⟩).1 hfnw
  have hm : Match (Env.ofMachine st [(fbOf m0, 1200)]) frS st :=
    match_ofMachine ⟨rfl, fun _ ↦ frame_aligned hS hF rfl, trivial⟩
      (by rw [hfr.sp]; simp [Sym.eval, fbOf]) trivial trivial trivial trivial
  have hx22 : (st.regs.getXReg .X22).toBitVec.toNat = j := hA.x22
  have hcn : (cntOf m0).toUInt64.toBitVec.toNat = cntOf m0 := natCast_toUInt64_toNat hc64
  have hc : (SBool.cmp .eq .W64 (.bin .add .W64 (.reg .X22) (.lit 1)) (.load 0 56 8)).eval
      (Env.ofMachine st [(fbOf m0, 1200)]) = decide (j + 1 = cntOf m0) := by
    sym_simp
    rw [bv_beq_toNat, load_fr hsp.cnt, Env.ofMachine_regs, BitVec.toNat_add, hx22, hcn]
    by_cases h : j + 1 = cntOf m0 <;> simp [h] <;> omega
  have hk5 : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.InducedWeight.b5Offset) := b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk5 run_b5 hwf hm fun s1 hm1 hpc1 ↦ ?_
  have hb5 := after_eq run_b5 ▸ b5_keeps
  have hfr1 := hfr.of_regs hm hm1 hwf rfl hb5.1 hb5.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf hb5.2
  have htot : totOf m0 (j + 1) = totOf m0 j + prodOf m0 j (lenOf m0 j) := by
    unfold totOf prodOf lenOf whatOf
    rw [indTot_succ _ _ _ _ hjws hjqs, getD_eq _ _ hjws, getD_eq _ _ hjqs]
  have x19 : s1.data.regs.X19 = (totOf m0 (j + 1)).c0 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X19 _ rfl).trans ?_
    sym_simp
    rw [htot, Env.ofMachine_regs, Env.ofMachine_regs]
    show _ = ((totOf m0 j).c0 ^^^ (prodOf m0 j (lenOf m0 j)).c0).toBitVec
    rw [UInt64.toBitVec_xor, ← hA.x25, ← hA.x19, BitVec.xor_comm]
    rfl
  have x29 : s1.data.regs.X29 = (totOf m0 (j + 1)).c1 := by
    apply UInt64.toBitVec_inj.mp
    refine (hm1.regs .X29 _ rfl).trans ?_
    sym_simp
    rw [htot, Env.ofMachine_regs, Env.ofMachine_regs]
    show _ = ((totOf m0 j).c1 ^^^ (prodOf m0 j (lenOf m0 j)).c1).toBitVec
    rw [UInt64.toBitVec_xor, ← hA.x26, ← hA.x29, BitVec.xor_comm]
    rfl
  simp only [PcOk] at hpc1
  rw [hc] at hpc1
  by_cases hlast : j + 1 = cntOf m0
  · simp only [hlast, decide_true, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmArm.Vm.InducedWeight.label_8 = Host.addrOf (k + NativeRustcVmArm.Vm.InducedWeight.b15Offset) from hp.label (j := NativeRustcVmArm.Vm.InducedWeight.b15Offset) NativeRustcVmArm.Vm.InducedWeight.label_8_at] at hpc1
    refine .done _ (.inr ⟨⟨hfr1, hd1 ▸ hsp.out, ?_, ?_⟩, hpc1⟩)
    · rw [← hlast]; exact x19
    · rw [← hlast]; exact x29
  simp only [hlast, decide_false, Bool.false_eq_true, ↓reduceIte] at hpc1
  refine .done _ (.inl ⟨⟨hfr1, hsp.of_dmem hd1, ?_, x19, x29, by omega⟩, hpc1⟩)
  show (s1.data.regs.getXReg .X22).toBitVec.toNat = _
  rw [hm1.regs .X22 _ rfl]
  sym_simp
  rw [Env.ofMachine_regs, BitVec.toNat_add, hx22]
  simp
  omega

end

end NativeRustcVmArm.Whir.InducedWeight
