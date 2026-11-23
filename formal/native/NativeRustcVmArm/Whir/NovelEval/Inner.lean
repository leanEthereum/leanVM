module

public import NativeRustcVmArm.Code.Vm.Kmul.Names
public import NativeRustcVmArm.Code.Vm.NovelEval.Names
public import NativeRustcVmArm.Whir.NovelEval.Inv

/-!
# `novel_eval`'s inner loop

A turn (`inner_step`): `b6` loads basis word `t` and calls `kmul` with the value, `b7` stores the
product after the basis (at `X26 + 8·X24`) and counts; after the last word it falls through to
`b8` with the doubled basis (`Post8`).
-/

namespace NativeRustcVmArm.Whir.NovelEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.NovelEval NativeVm.Model
open NativeRustcVm.Whir NativeRustcArm

public section

/-- The address `b7` stores at. -/
theorem stAddr_eval [Labels] (env : Env) :
    stAddr.eval env = env.regs .X26 + BitVec.ofNat 64 (8 * (env.regs .X24).toNat) := by
  simp only [stAddr, Sym.eval, BinOp.apply, UnOp.apply, low_W64, ext_W64,
    BitVec.apply_mem_extend, BitVec.unsigned, Int.shiftLeft_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  push_cast
  omega

variable [Host] {k : Nat}

/-- **A turn of the inner loop.** -/
theorem inner_step (hp : Placed code k) (hkmul : Spec (label NativeRustcVmArm.Vm.Kmul.entryLabel) KmulPre KmulPost)
    {m0 : MachineData} (hS : StackOk m0 novelEvalStack) (hc : cnt m0 ≤ 64) {j t : Nat}
    (ht : t < (basisOf m0 j).size) {st : MachineData} (hI : IInv m0 j t st) :
    Eventually (step1 Host.exe)
      (fun s ↦ (Post8 m0 j s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b8Offset)) ∨
        (IInv m0 j (t + 1) s.data ∧ s.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b6Offset) ∧ t + 1 < (basisOf m0 j).size))
      ⟨st, Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b6Offset)⟩ := by
  have hF : 1120 ≤ novelEvalStack := by decide
  have hkle : 1120 + kmulStack ≤ novelEvalStack := by decide
  obtain ⟨hfmap, hfnw, hfe⟩ := frame_ok hS hF
  have h32 := basis_le_32 m0 j hc hI.lt
  have hfr := hI.fr
  let B := basisOf m0 j
  let v := (whatOf m0).getD j 0
  have hBs : B.size = (basisOf m0 j).size := rfl
  -- `b6`: load the word, call `kmul`
  have hk6 : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b6Offset) := b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hrd : Readable st (fbOf m0 + BitVec.ofNat 64 (8 * t)) 8 :=
    hfr.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env6 := Env.ofMachine st [(fbOf m0 + BitVec.ofNat 64 (8 * t), 8)]
  have hwf6 : env6.WF := wf_one hrd.1 hrd.2
  have hm6 : Match env6 bS st := match_one <| by
    show st.regs.X26.toBitVec = _
    rw [hI.x26]
    simp
  refine exec_then hk6 run_b6 hwf6 hm6 fun s1 hm1 hpc1 ↦ ?_
  have hb6 := after_eq run_b6 ▸ b6_keeps
  have hfr1 := hfr.of_regs hm6 hm1 hwf6 rfl hb6.1 hb6.2
  have hd1 : s1.data.dmem = st.dmem := hm1.dmem_eq hwf6 hb6.2
  have hBt : (s1.data.regs.getXReg .X0).toBitVec = (B[t]'ht).toBitVec := by
    refine (hm1.regs .X0 _ rfl).trans ?_
    simp only [Sym.eval]
    refine load_word ?_
    rw [NativeRustcVm.addr_add_zero]
    exact NativeRustcVm.wordsAt_getElem hI.basis (by simpa using ht)
  have hv1 : s1.data.regs.X1 = v :=
    (UInt64.toBitVec_inj.mp (hm1.regs .X1 _ rfl)).trans hI.x23
  refine call_then hpc1 hkmul (hfr1.stackOk hS rfl hkle) fun s2 hpc2 ⟨hx0, hsame2, hsv2⟩ ↦ ?_
  have hfr2 := hfr1.call hS hkle slots_le hsame2 hsv2
  have hlenB : (B.toList.flatMap NativeRustcVm.wordBytes).length = 8 * B.size := by
    rw [NativeRustcVm.length_wordsBytes, Array.length_toList]
  have hlenN : ((B.toList.take t).map (kmul · v) |>.flatMap NativeRustcVm.wordBytes).length =
      8 * t := by
    rw [NativeRustcVm.length_wordsBytes, List.length_map, List.length_take, Array.length_toList]
    omega
  have hbasis2 : NativeRustcVm.WordsAt s2.data.dmem (fbOf m0) B.toList := by
    have := hfr1.bytes_call hS hkle hsame2 (o := 0) (by rw [hlenB]; omega)
      (by rw [NativeRustcVm.addr_add_zero, hd1]; exact hI.basis)
    rwa [NativeRustcVm.addr_add_zero] at this
  have hnew2 : NativeRustcVm.WordsAt s2.data.dmem (fbOf m0 + BitVec.ofNat 64 (8 * B.size))
      ((B.toList.take t).map (kmul · v)) :=
    hfr1.bytes_call hS hkle hsame2 (by rw [hlenN]; omega) (hd1 ▸ hI.new)
  -- `b7`: store the product, count
  have hk7 : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.NovelEval.b7Offset) := b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hpc2' : s2.pc = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b7Offset) := hpc2
  have e2 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27],
      s2.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (hsv2.1 _ rfl).trans (Match.reg_eq hm6 hm1 rfl rfl)
  let a7 := fbOf m0 + BitVec.ofNat 64 (8 * B.size + 8 * t)
  have hrd7 : Readable s2.data a7 8 := hfr2.readable (Readable.sub ⟨hfmap, hfnw⟩ (by omega))
  let env7 := Env.ofMachine s2.data [(a7, 8)]
  have hwf7 : env7.WF := wf_one hrd7.1 hrd7.2
  have hm7 : Match env7 stS s2.data :=
    match_ofMachine ⟨rfl, fun h ↦ absurd h (by decide), trivial⟩ rfl trivial trivial trivial
      ⟨by
        show stAddr.eval env7 = env7.base 0 + BitVec.ofInt 64 0
        rw [stAddr_eval, Env.ofMachine_regs, Env.ofMachine_regs, e2 .X26 (by simp),
          e2 .X24 (by simp)]
        show st.regs.X26.toBitVec + BitVec.ofNat 64 (8 * st.regs.X24.toNat) = _
        rw [hI.x26, hI.x24, addr_add, show 8 * t + 8 * (basisOf m0 j).size =
          8 * B.size + 8 * t by omega]
        simp [a7, env7], trivial⟩
  refine exec_at hk7 run_b7 hwf7 hpc2' hm7 fun s3 hm8 hpc3 ↦ ?_
  have hb7 := after_eq run_b7 ▸ b7_keeps
  have hfr3 := hfr2.of_block hm7 hm8 hwf7 rfl hb7.1 (r := 0) rfl le_rfl hb7.2
    (fun p h ↦ .inr (inRange_frame_sub hS hF (o := 8 * B.size + 8 * t) (n := 8) (by omega) h))
    (fun q hq i hi ↦ not_inRange_slot hS hF (o := 8 * B.size + 8 * t) (n := 8) (by omega)
      (slots_le q hq) hi (.inl (by have := slots_ge q hq; omega)))
  have hsame3 := same_region_le hm8 hwf7 (r := 0) rfl le_rfl hb7.2
  have hfbn : (fbOf m0).toNat + 1120 ≤ 2 ^ 64 := hfnw
  have hfbt : ∀ o, o ≤ 1120 → (fbOf m0 + BitVec.ofNat 64 o).toNat = (fbOf m0).toNat + o :=
    fun o ho ↦ by
      rcases NativeRustcVm.toNat_add_ofNat_le (a := fbOf m0) (i := o) (by omega) with h | ⟨h, h'⟩
      · exact h
      · have : (fbOf m0).toNat = m0.regs.SP.toBitVec.toNat - 1120 := hfe
        have := m0.regs.SP.toBitVec.isLt
        omega
  have hprod : NativeRustcVm.WordAt s3.data.dmem a7 (kmul (B[t]'ht) v) := by
    have := Match.wordAt_write hm8 (r := 0) (o := 0) rfl (by decide) (v := .reg .X0) (by decide)
    rw [NativeRustcVm.addr_add_zero] at this
    convert this using 1
    show _ = UInt64.ofBitVec s2.data.regs.X0.toBitVec
    have h0 : s1.data.regs.X0 = B[t] := UInt64.toBitVec_inj.mp hBt
    rw [UInt64.ofBitVec_toBitVec, hx0, hv1, h0]
  have hbasis3 : NativeRustcVm.WordsAt s3.data.dmem (fbOf m0) B.toList := by
    refine NativeRustcVm.BytesAt.of_sameOutside_apart hbasis2 hsame3 ?_ ?_ hrd7.2
    · rw [hlenB]; unfold NativeRustcVm.Apart; rw [hfbt _ (by omega)]; omega
    · rw [hlenB]; exact NativeRustcVm.NoWrap.mono hfnw (by omega)
  have hnew3 : NativeRustcVm.WordsAt s3.data.dmem (fbOf m0 + BitVec.ofNat 64 (8 * B.size))
      ((B.toList.take (t + 1)).map (kmul · v)) := by
    rw [List.take_add_one, List.map_append, NativeRustcVm.wordsAt_append]
    refine ⟨NativeRustcVm.BytesAt.of_sameOutside_apart hnew2 hsame3 ?_ ?_ hrd7.2, ?_⟩
    · rw [hlenN]; unfold NativeRustcVm.Apart; rw [hfbt _ (by omega), hfbt _ (by omega)]; omega
    · rw [hlenN]; exact NativeRustcVm.NoWrap.sub hfnw (by omega)
    · rw [List.length_map, List.length_take, Array.length_toList, addr_add,
        show 8 * B.size + 8 * min t B.size = 8 * B.size + 8 * t by omega]
      rw [Array.getElem?_toList, show B[t]? = some (B[t]'ht) from Array.getElem?_eq_getElem ht]
      simp only [Option.toList_some, List.map_cons, List.map_nil]
      exact NativeRustcVm.wordsAt_singleton.mpr hprod
  -- the registers
  have e3 : ∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25],
      s3.data.regs.getXReg r = st.regs.getXReg r := by
    intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact (Match.reg_eq hm7 hm8 rfl rfl).trans (e2 _ (by simp))
  have rg : Regs m0 s3.data :=
    ⟨(e3 .X19 (by simp)).trans hI.rg.x19, (e3 .X20 (by simp)).trans hI.rg.x20,
      (e3 .X21 (by simp)).trans hI.rg.x21⟩
  have x22 : s3.data.regs.X22.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * j) := by
    rw [show s3.data.regs.X22 = st.regs.X22 from e3 .X22 (by simp)]; exact hI.x22
  have x25 : s3.data.regs.X25.toBitVec = m0.regs.X3.toBitVec + BitVec.ofNat 64 (8 * wn m0) := by
    rw [show s3.data.regs.X25 = st.regs.X25 from e3 .X25 (by simp)]; exact hI.x25
  have x24 : s3.data.regs.X24.toNat = (basisOf m0 j).size := by
    rw [show s3.data.regs.X24 = st.regs.X24 from e3 .X24 (by simp)]; exact hI.x24
  have hd3 : NativeRustcVm.WordsAt s3.data.dmem (fbOf m0) B.toList := hbasis3
  have h27 : st.regs.X27.toBitVec.toNat = B.size - t := hI.x27
  simp only [PcOk] at hpc3
  sym_simp at hpc3
  simp only [env7, Env.ofMachine_regs, e2 .X27 (by simp)] at hpc3
  have hl5 : Labels.label NativeRustcVmArm.Vm.NovelEval.label_5 = Host.addrOf (k + NativeRustcVmArm.Vm.NovelEval.b6Offset) := hp.label (j := NativeRustcVmArm.Vm.NovelEval.b6Offset) NativeRustcVmArm.Vm.NovelEval.label_5_at
  by_cases hlast : B.size - t = 1
  · have hx : (st.regs.getXReg .X27).toBitVec = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      show st.regs.X27.toBitVec.toNat = _
      rw [h27, hlast]
      rfl
    simp only [hx, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc3
    refine .done _ (.inl ⟨⟨hfr3, rg, hI.hj, hI.lt, x22, x25, x24, ?_⟩, hpc3⟩)
    rw [basisOf_succ m0 hI.hj hI.lt, Array.toList_append, Array.toList_map,
      NativeRustcVm.wordsAt_append]
    refine ⟨hd3, ?_⟩
    have := hnew3
    rw [show t + 1 = B.size by omega, List.take_of_length_le (by simp)] at this
    rwa [Array.length_toList]
  · have hb : ((st.regs.getXReg .X27).toBitVec == BitVec.ofNat 64 1) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      apply hlast
      rw [← h27]
      exact congrArg BitVec.toNat h
    simp only [hb, Bool.not_false, ↓reduceIte] at hpc3
    refine .done _ (.inr ⟨⟨hfr3, rg, hI.hj, hI.lt, x22, x25, x24,
      (e3 .X23 (by simp)).trans hI.x23, ?_, ?_, hd3, hnew3⟩, hpc3.trans hl5, by omega⟩)
    · refine (hm8.regs .X26 _ rfl).trans ?_
      sym_simp
      rw [Env.ofMachine_regs, e2 .X26 (by simp)]
      show st.regs.X26.toBitVec + _ = _
      rw [hI.x26, addr_add]
      rfl
    · show (s3.data.regs.getXReg .X27).toBitVec.toNat = _
      rw [hm8.regs .X27 _ rfl]
      sym_simp
      rw [Env.ofMachine_regs, e2 .X27 (by simp), BitVec.toNat_sub]
      show (2 ^ 64 - 1 % 2 ^ 64 + st.regs.X27.toBitVec.toNat) % 2 ^ 64 = _
      rw [h27]
      omega

end

end NativeRustcVmArm.Whir.NovelEval
