module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.IterB
public import NativeRustcVmX64.Code.Vm.FoldRow.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names

/-!
# `each_row` with `final_level`'s closure: folding a row, its `What`s (x86-64)

At `b11` (`AtB11`): `b11` spills the query's address and the rows left (48, 56) and calls
`fold_row` on the lanes with query `j` and the rounds; `b12` keeps the folded value in RBP, R14
and calls `subspace_at_table` on the table at 1392 and the query, the `What`s at 1128: at `b13`
(`AtB13`, `iter_c`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- **At `b13`**, in iteration `j`: the folded row in RBP, R14, the `What`s at 1128. -/
structure AtB13 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidM m0 j ((qsOf m0)[j]'hjq) m.dmem
  ok : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j →
    okOf m0 (qsOf m0)[i] rows[i] = true
  w48 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 48)
    (UInt64.ofBitVec (reg m0 .rsi + BitVec.ofNat 64 (8 * j)))
  w56 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 56)
    (UInt64.ofBitVec (BitVec.ofNat 64 (rows.size - (j + 1))))
  fold : ewArg (reg m .rbp) (reg m .r14) =
    foldRow (lanesJ m0 (rows[j]'hj)) ((qsOf m0)[j]'hjq) (eachRowArgs m0).2
  what : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1128) rootCap
    (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'hjq)).toList
  r15 : reg m .r15 = BitVec.ofNat 64 (tableOf m0).size
  rbx : reg m .rbx = fb m0 + BitVec.ofNat 64 1392

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

/-- The rounds read depend on their bytes only. -/
theorem roundsOf_congr {d d' : DataMem} {a : BitVec 64} {n : Nat}
    (h : ∀ i < 32 * n, d'.get? (a + BitVec.ofNat 64 i) = d.get? (a + BitVec.ofNat 64 i)) :
    roundsOf d' a n = roundsOf d a n := by
  unfold roundsOf
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [NativeRustcVm.ewOf_congr (d := d) fun k hk ↦ by
      rw [NativeRustcVm.addr_add_add]; exact h _ (by omega),
    NativeRustcVm.ewOf_congr (d := d) (a := a + BitVec.ofNat 64 (32 * i + 16)) fun k hk ↦ by
      rw [NativeRustcVm.addr_add_add]; exact h _ (by omega)]

theorem ewArg_ewRet (m : MachineData) : ewArg (reg m .rax) (reg m .rdx) = ewRet m := rfl

variable [Host] {k : Nat}

/-- **Folding a row and its `What`s**: from `b11` to `b13`. -/
theorem iter_c (hp : Placed code k) (hfold : Spec (label NativeRustcVmX64.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (hpre : EachRowFinalPre rows op m0) {m : MachineData} (h : AtB11 rows m0 j m)
    (cont : ∀ m', AtB13 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset)⟩ := by
  have hl := lay hpre
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowFinalStack = 3088 := rfl
  have hrdin := hpre.1.2.2.2.2.2.2.2.2
  have hjr := h.hj
  have hjq := h.hjq
  -- `b11`: `fold_row`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset + b11.length)).toBitVec
  have hk11 : b11.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset) := b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hq72 : (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset + b11.length)).toBitVec).load 0 72 8 = ((qsOf m0)[j]'hjq).toBitVec :=
    NativeRustcVmX64.Arrays.load_word h.mm.w72
  refine exec_then hk11 run_b11 hwf (fun _ _ ↦ rfl) hm fun st1 hm1 hpc1 ↦ ?_
  have hs1 : SameOutside m.dmem st1.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 48 64) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm1 hwf (by decide)
  have hfr1 : FR m0 0 st1.data :=
    h.fr.step hl (by decide) (by decide) ((rv hm1 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm1.kept hwf) hs1 (by decide)
  have w48 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 48)
      (UInt64.ofBitVec (reg m0 .rsi + BitVec.ofNat 64 (8 * j))) := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) (o := 48) rfl (by decide)
      (v := .reg .rbp) (by decide)
    rwa [show (Sym.reg .rbp).eval (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset + b11.length)).toBitVec) = _ from h.rbp] at this
  have w56 : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 56)
      (UInt64.ofBitVec (BitVec.ofNat 64 (rows.size - (j + 1)))) := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm1 (r := 0) (o := 56) rfl (by decide)
      (v := .reg .r13) (by decide)
    rwa [show (Sym.reg .r13).eval (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset + b11.length)).toBitVec) = _ from h.r13] at this
  have hmm1 := h.mm.keep hl (by decide) (by decide) (by decide) (by decide) hs1
  have hlanes1 : EWsAt st1.data.dmem (fb m0 + BitVec.ofNat 64 104) (lanesJ m0 (rows[j]'hjr)).toList :=
    EachRow.keep_frame hl (by decide) (by decide) hs1 (by decide)
      (.inr ⟨by decide, by rw [NativeRustcVm.length_ewsBytes]; have := h.lsize; simp; omega⟩)
      h.lanes
  have e1rdi : reg st1.data .rdi = fb m0 + BitVec.ofNat 64 104 :=
    (rv hm1 (v := .reg .rbx) rfl).trans h.rbx
  have e1rsi : (reg st1.data .rsi).toNat = (lanesJ m0 (rows[j]'hjr)).size :=
    (congrArg BitVec.toNat (rv hm1 (v := .reg .rdx) rfl)).trans h.rdx
  have e1rdx : reg st1.data .rdx = ((qsOf m0)[j]'hjq).toBitVec :=
    (rv hm1 (v := .load 0 72 8) rfl).trans hq72
  have e1rcx : reg st1.data .rcx = reg m0 .r9 :=
    (rv hm1 (v := .load 0 32 8) rfl).trans (NativeRustcVmX64.Arrays.load_word h.mm.low.w32)
  have e1r8 : reg st1.data .r8 = stackArg m0 0 :=
    (rv hm1 (v := .load 0 1944 8) rfl).trans (argW hpre h.fr 0 (by decide))
  have e1r13 : reg st1.data .r13 = ((qsOf m0)[j]'hjq).toBitVec :=
    (rv hm1 (v := .load 0 72 8) rfl).trans hq72
  have hrd := hfr1.whirIn_input hl hrdin (N' := foldRowStack) (by decide)
  have a104 := hl.addr (o := 104) (by decide)
  have hP1 : FoldRowPre st1.data := by
    unfold FoldRowPre
    rw [e1rdi, e1rcx, e1r8]
    refine ⟨hfr1.stackOk hl (by decide), hfr1.whirIn_frame hl (by decide) (by decide) (by decide),
      hrd, ?_, hpre.1.2.2.2.2.2.2.2.1⟩
    have := hrdin.2
    unfold OffStack Apart at this
    unfold Apart
    rw [hl.baseN] at this
    rw [a104]
    have : lanesBytes = 1024 := rfl
    omega
  refine call_then hpc1 hfold hP1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hval, hch, hsv⟩ := hq2
  rw [e1rdi] at hch
  have hs2 : SameOutside st1.data.dmem st2.data.dmem
      (EachRow.Hit m0 1936 eachRowFinalStack 104 1128) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr1.rsp0 (N' := foldRowStack) (by decide)
      le_rfl (by decide) hch
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr1 hrsp2 hsv hs2 (by decide)
  have hfoldv : ewRet st2.data =
      foldRow (lanesJ m0 (rows[j]'hjr)) ((qsOf m0)[j]'hjq) (eachRowArgs m0).2 := by
    refine hval.trans ?_
    rw [e1rdi, e1rsi, e1rdx, e1rcx, e1r8]
    have hn : min (lanesJ m0 (rows[j]'hjr)).size laneCap = (lanesJ m0 (rows[j]'hjr)).toList.length := by
      rw [Array.length_toList]
      exact Nat.min_eq_left h.lsize
    rw [hn]
    unfold ewSlice
    rw [NativeRustcVm.ewsOf_of_ewsAt hlanes1, Array.toArray_toList,
      roundsOf_congr (hfr1.input_same hl hrdin fun _ _ h ↦ h)]
    simp [eachRowArgs]
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv hfoldv
  subst hpc2
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11Offset + b11.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b12Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b11_next]]
  have k2 : ∀ r, calleeSaved r = true → reg d2 r = reg st1.data r := fun r hc ↦ sv hsv r hc
  have hmm2 := hmm1.keep hl (by decide) (by decide) (by decide) (by decide) hs2
  -- `b12`: `subspace_at_table`
  obtain ⟨hwf2, hm2⟩ := frame_env hpre hfr2 (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b12Offset + b12.length)).toBitVec
  have hk12 : b12.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b12Offset) := b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk12 run_b12 hwf2 (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hs3 : SameOutside d2.dmem st3.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 1384 1384) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm3 hwf2 (by decide)
  have hfr3 : FR m0 0 st3.data :=
    hfr2.step hl le_rfl (by decide) ((rv hm3 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm3.kept hwf2) hs3 (by decide)
  have hlow := hmm2.low
  have hts : (tableOf m0).size ≤ 31 := by
    have := hlow.tab.1
    rwa [Array.length_toList] at this
  have hr12 : reg d2 .r12 = BitVec.ofNat 64 (tableOf m0).size := by
    rw [k2 .r12 rfl, rv hm1 (v := .reg .r12) rfl]; exact h.r12
  have hr15 : reg d2 .r15 = fb m0 + BitVec.ofNat 64 1392 := by
    rw [k2 .r15 rfl, rv hm1 (v := .reg .r15) rfl]; exact h.r15
  have e3rdi : reg st3.data .rdi = fb m0 + BitVec.ofNat 64 1128 :=
    (rv hm3 (v := .ptr 0 1128) rfl).trans (EachRow.eval_ptr0 1128)
  have e3rsi : reg st3.data .rsi = fb m0 + BitVec.ofNat 64 1392 :=
    (rv hm3 (v := .reg .r15) rfl).trans hr15
  have e3rdx : (reg st3.data .rdx).toNat = (tableOf m0).size := by
    rw [rv hm3 (v := .reg .r12) rfl]
    show (reg d2 .r12).toNat = _
    rw [hr12, BitVec.toNat_ofNat]
    omega
  have e3rcx : reg st3.data .rcx = ((qsOf m0)[j]'hjq).toBitVec := by
    rw [rv hm3 (v := .reg .r13) rfl]
    show reg d2 .r13 = _
    rw [k2 .r13 rfl, e1r13]
  have a1128 := hl.addr (o := 1128) (by decide)
  have a1392 := hl.addr (o := 1392) (by decide)
  have hP3 : SubspaceAtTablePre st3.data := by
    unfold SubspaceAtTablePre
    rw [e3rdi, e3rsi, e3rdx]
    refine ⟨hfr3.stackOk hl (by decide), hts,
      hfr3.whirIn_frame hl (by decide) (by omega) (by decide),
      hfr3.whirIn_frame hl (by decide) (by decide) (by decide), ?_, ?_⟩
    · unfold Apart
      rw [a1128, a1392]
      have : whatBytes = 256 := rfl
      omega
    · apply hfr3.got_callee hl hpre.2.2.2 (got_nw hpre) (by intro q h; cases h) (by decide)
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · refine ⟨(stackBelow m0 eachRowFinalStack, eachRowFinalStack + 8), by simp, ?_, ?_⟩ <;>
          rw [a1392, hl.baseN] <;> have := hl.sp <;> rw [stack_eq] at * <;> omega
      · have hsp : 3088 ≤ (rspOf m0).toNat := hl.sp
        refine ⟨(stackBelow m0 eachRowFinalStack, eachRowFinalStack + 8), by simp, ?_, ?_⟩
        · change (stackBelow m0 eachRowFinalStack).toNat ≤ (fb m0 + BitVec.ofNat 64 1128).toNat
          rw [a1128, hl.baseN, stack_eq]
          omega
        · change (fb m0 + BitVec.ofNat 64 1128).toNat + 256 ≤
            (stackBelow m0 eachRowFinalStack).toNat + (eachRowFinalStack + 8)
          rw [a1128, hl.baseN, stack_eq]
          omega
  refine call_then hpc3 hsat hP3 fun st4 hpc4 hrsp4 hq4 ↦ ?_
  obtain ⟨hval4, hch4, hsv4⟩ := hq4
  rw [e3rdi] at hch4
  have hs4 : SameOutside st3.data.dmem st4.data.dmem
      (EachRow.Hit m0 1936 eachRowFinalStack 1128 1384) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr3.rsp0 (N' := subspaceAtTableStack)
      (by decide) le_rfl (by decide) hch4
  have hfr4 : FR m0 8 st4.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr3 hrsp4 hsv4 hs4 (by decide)
  have hlow3 : Low m0 st3.data.dmem := hlow.keep hl le_rfl (by decide) (by decide) hs3
  have hpairs : pairsOf st3.data.dmem (fb m0 + BitVec.ofNat 64 1392) (tableOf m0).size =
      (tableOf m0).toList := by
    have := EachRow.pairsOf_of_pairsAt hlow3.tab.2.2
    rw [show off (fb m0 + BitVec.ofNat 64 1384) 8 = fb m0 + BitVec.ofNat 64 1392 from
      NativeRustcVm.addr_add_add _ _ _, Array.length_toList] at this
    exact this
  have hrbp3 : reg st3.data .rbp = reg d2 .rax := rv hm3 (v := .reg .rax) rfl
  have hr143 : reg st3.data .r14 = reg d2 .rdx := rv hm3 (v := .reg .rdx) rfl
  have hr153 : reg st3.data .r15 = BitVec.ofNat 64 (tableOf m0).size :=
    (rv hm3 (v := .reg .r12) rfl).trans hr12
  have hrbx3 : reg st3.data .rbx = fb m0 + BitVec.ofNat 64 1392 :=
    (rv hm3 (v := .reg .r15) rfl).trans hr15
  rw [e3rdi, e3rsi, e3rdx, e3rcx, hpairs, Array.toArray_toList, UInt64.ofBitVec_toBitVec] at hval4
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hfr4 hs4 hsv4 hval4
  subst hpc4
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b12Offset + b12.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b12_next]]
  refine cont d4 ⟨hfr4, hjr, hjq,
    (hmm2.keep hl le_rfl (by decide) (by decide) (by decide) hs3).keep hl (by decide) (by decide)
      (by decide) (by decide) hs4, h.ok, ?_, ?_, ?_, hval4, ?_, ?_⟩
  · exact keepW hl (by decide) (by decide) hs4 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs3 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w48))
  · exact keepW hl (by decide) (by decide) hs4 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs3 (by decide) (by decide)
        (keepW hl (by decide) (by decide) hs2 (by decide) (by decide) w56))
  · rw [sv hsv4 .rbp rfl, sv hsv4 .r14 rfl, hrbp3, hr143, ewArg_ewRet]
    exact hfoldv
  · rw [sv hsv4 .r15 rfl]; exact hr153
  · rw [sv hsv4 .rbx rfl]; exact hrbx3

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
