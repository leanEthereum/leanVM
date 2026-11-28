module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterB
public import NativeRustcVmX64.Code.Vm.FoldRow.Names
public import NativeRustcVmX64.Code.Vm.SubspaceAtTable.Names

/-!
# `each_row` with `next_level`'s closure: folding a row, its `What`s (x86-64)

At `b15` (`AtB15`): `b15` calls `fold_row` on the lanes with query `j` and the rounds; `b16`
stores the folded value's low limb at 112, keeps its high limb in R12 and calls
`subspace_at_table` on the table at 1440 and the query, the `What`s at 1176: at `b17` (`AtB17`,
`iter_c`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off)

@[expose] public section

/-- Row `j`'s folded value. -/
abbrev foldJ (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (hj : j < rows.size)
    (hjq : j < (qsOf m0).size) : EW :=
  foldRow (lanesJ m0 (rows[j]'hj)) ((qsOf m0)[j]'hjq) (eachRowArgs m0).2

/-- **At `b17`**, in iteration `j`: the folded row at 112 and in R12, the `What`s at 1176. -/
structure AtB17 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  w112 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 112) (foldJ rows m0 j hj hjq).c0
  r12 : reg m .r12 = (foldJ rows m0 j hj hjq).c1.toBitVec
  what : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1176) rootCap
    (subspaceAtTable (tableOf m0) ((qsOf m0)[j]'hjq)).toList
  rbp : reg m .rbp = ((qsOf m0)[j]'hjq).toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 j
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r14 : reg m .r14 = bOf m0

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

variable [Host] {k : Nat}

/-- **Folding a row and its `What`s**: from `b15` to `b17`. -/
theorem iter_c (hp : Placed code k) (hfold : Spec (label NativeRustcVmX64.Vm.FoldRow.entryLabel) FoldRowPre FoldRowPost)
    (hsat : Spec (label NativeRustcVmX64.Vm.SubspaceAtTable.entryLabel) SubspaceAtTablePre SubspaceAtTablePost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB15 rows m0 j m)
    (cont : ∀ m', AtB17 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b17Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b15Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowNextStack = 3136 := rfl
  have hrdin := c.rdin
  have hjr := h.hj
  have hjq := h.hjq
  -- `b15`: `fold_row`
  obtain ⟨hwf, hm⟩ := frame_env c h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b15Offset + b15.length)).toBitVec
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk15 run_b15 hwf (fun _ _ ↦ rfl) hm fun st1 hm1 hpc1 ↦ ?_
  have hs1 : SameOutside m.dmem st1.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm1 hwf (by decide)
  have hfr1 : FR m0 0 st1.data :=
    h.fr.step hl le_rfl (by decide) ((rv hm1 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm1.kept hwf) hs1 (by decide)
  have hmm1 := h.mm.keep c le_rfl (by decide) (by decide) (by decide) hs1
  have hlanes1 : EWsAt st1.data.dmem (fb m0 + BitVec.ofNat 64 152) (lanesJ m0 (rows[j]'hjr)).toList :=
    EachRow.keep_frame hl le_rfl (by decide) hs1 (by decide)
      (.inl (by rw [NativeRustcVm.length_ewsBytes]; have := h.lsize; simp; omega)) h.lanes
  have e1rdi : reg st1.data .rdi = fb m0 + BitVec.ofNat 64 152 :=
    (rv hm1 (v := .reg .r12) rfl).trans h.r12
  have e1rsi : (reg st1.data .rsi).toNat = (lanesJ m0 (rows[j]'hjr)).size :=
    (congrArg BitVec.toNat (rv hm1 (v := .reg .rdx) rfl)).trans h.rdx
  have e1rdx : reg st1.data .rdx = ((qsOf m0)[j]'hjq).toBitVec :=
    (rv hm1 (v := .reg .rbp) rfl).trans h.rbp
  have e1rcx : reg st1.data .rcx = reg m0 .r9 :=
    (rv hm1 (v := .load 0 88 8) rfl).trans (NativeRustcVmX64.Arrays.load_word h.mm.low.w88)
  have e1r8 : reg st1.data .r8 = stackArg m0 0 :=
    (rv hm1 (v := .load 0 1992 8) rfl).trans (argW c h.fr 0 (by decide))
  have hrd := hfr1.whirIn_input hl hrdin (N' := foldRowStack) (by decide)
  have a152 := hl.addr (o := 152) (by decide)
  have hP1 : FoldRowPre st1.data := by
    unfold FoldRowPre
    rw [e1rdi, e1rcx, e1r8]
    refine ⟨hfr1.stackOk hl (by decide), hfr1.whirIn_frame hl (by decide) (by decide) (by decide),
      hrd, ?_, c.nr⟩
    have := hrdin.2
    unfold OffStack Apart at this
    unfold Apart
    rw [hl.baseN] at this
    rw [a152]
    have : lanesBytes = 1024 := rfl
    omega
  refine call_then hpc1 hfold hP1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hval, hch, hsv⟩ := hq2
  rw [e1rdi] at hch
  have hs2 : SameOutside st1.data.dmem st2.data.dmem
      (EachRow.Hit m0 1984 eachRowNextStack 152 1176) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr1.rsp0 (N' := foldRowStack) (by decide)
      le_rfl (by decide) hch
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr1 hrsp2 hsv hs2 (by decide)
  have hfoldv : ewRet st2.data = foldJ rows m0 j hjr hjq := by
    refine hval.trans ?_
    rw [e1rdi, e1rsi, e1rdx, e1rcx, e1r8]
    have hn : min (lanesJ m0 (rows[j]'hjr)).size laneCap =
        (lanesJ m0 (rows[j]'hjr)).toList.length := by
      rw [Array.length_toList]
      exact Nat.min_eq_left h.lsize
    rw [hn]
    unfold ewSlice
    rw [NativeRustcVm.ewsOf_of_ewsAt hlanes1, Array.toArray_toList,
      roundsOf_congr (hfr1.input_same hl hrdin (notB_in c hrdin c.brd))]
    rfl
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv hfoldv
  subst hpc2
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b15Offset + b15.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b16Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b15_next]]
  have k2 : ∀ r, calleeSaved r = true → reg d2 r = reg st1.data r := fun r hc ↦ sv hsv r hc
  have hmm2 := hmm1.keep c (by decide) (by decide) (by decide) (by decide) hs2
  -- `b16`: `subspace_at_table`
  obtain ⟨hwf2, hm2⟩ := frame_env c hfr2 (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b16Offset + b16.length)).toBitVec
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk16 run_b16 hwf2 (fun _ _ ↦ rfl) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hs3 : SameOutside d2.dmem st3.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 112 120) :=
    EachRow.hit_of_block hl (by decide) (by decide) hm3 hwf2 (by decide)
  have hfr3 : FR m0 0 st3.data :=
    hfr2.step hl (by decide) (by decide) ((rv hm3 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm3.kept hwf2) hs3 (by decide)
  have w112 : WordAt st3.data.dmem (fb m0 + BitVec.ofNat 64 112) (foldJ rows m0 j hjr hjq).c0 := by
    have := NativeRustcVmX64.Transcript.wordAt_write hm3 (r := 0) (o := 112) rfl (by decide)
      (v := .reg .rax) (by decide)
    rw [← hfoldv]
    exact this
  have hmm3 := hmm2.keep c (by decide) (by decide) (by decide) (by decide) hs3
  have hlow := hmm3.low
  have hts : (tableOf m0).size ≤ 31 := by
    have := hlow.tab.1
    rwa [Array.length_toList] at this
  have hr13 : reg d2 .r13 = fb m0 + BitVec.ofNat 64 1440 := by
    rw [k2 .r13 rfl, rv hm1 (v := .reg .r13) rfl]; exact h.r13
  have e3rdi : reg st3.data .rdi = fb m0 + BitVec.ofNat 64 1176 :=
    (rv hm3 (v := .ptr 0 1176) rfl).trans (EachRow.eval_ptr0 1176)
  have e3rsi : reg st3.data .rsi = fb m0 + BitVec.ofNat 64 1440 :=
    (rv hm3 (v := .reg .r13) rfl).trans hr13
  have e3rdx : (reg st3.data .rdx).toNat = (tableOf m0).size := by
    have hl72 : (EachRow.envE m0 d2 1984 16 [] (fun _ ↦ 0)
        (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b16Offset + b16.length)).toBitVec).load 0 72 8 =
        BitVec.ofNat 64 (tableOf m0).size := NativeRustcVmX64.Arrays.load_word hmm2.low.w72
    rw [rv hm3 (v := .load 0 72 8) rfl]
    show (Env.load _ 0 72 8).toNat = _
    rw [hl72, BitVec.toNat_ofNat]
    omega
  have e3rcx : reg st3.data .rcx = ((qsOf m0)[j]'hjq).toBitVec := by
    rw [rv hm3 (v := .reg .rbp) rfl]
    show reg d2 .rbp = _
    rw [k2 .rbp rfl, rv hm1 (v := .reg .rbp) rfl]
    exact h.rbp
  have a1176 := hl.addr (o := 1176) (by decide)
  have a1440 := hl.addr (o := 1440) (by decide)
  have hP3 : SubspaceAtTablePre st3.data := by
    unfold SubspaceAtTablePre
    rw [e3rdi, e3rsi, e3rdx]
    refine ⟨hfr3.stackOk hl (by decide), hts,
      hfr3.whirIn_frame hl (by decide) (by omega) (by decide),
      hfr3.whirIn_frame hl (by decide) (by decide) (by decide), ?_, ?_⟩
    · unfold Apart
      rw [a1176, a1440]
      have : whatBytes = 256 := rfl
      omega
    · apply hfr3.got_callee hl c.got c.got_nw
        (fun q h => ⟨(bOf m0, 16), by simp, h⟩) (by decide)
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · refine ⟨(stackBelow m0 eachRowNextStack, eachRowNextStack + 8), by simp, ?_, ?_⟩ <;>
          rw [a1440, hl.baseN] <;> have := hl.sp <;> rw [stack_eq] at * <;> omega
      · have hsp : 3136 ≤ (rspOf m0).toNat := hl.sp
        refine ⟨(stackBelow m0 eachRowNextStack, eachRowNextStack + 8), by simp, ?_, ?_⟩
        · change (stackBelow m0 eachRowNextStack).toNat ≤ (fb m0 + BitVec.ofNat 64 1176).toNat
          rw [a1176, hl.baseN, stack_eq]
          omega
        · change (fb m0 + BitVec.ofNat 64 1176).toNat + 256 ≤
            (stackBelow m0 eachRowNextStack).toNat + (eachRowNextStack + 8)
          rw [a1176, hl.baseN, stack_eq]
          omega
  refine call_then hpc3 hsat hP3 fun st4 hpc4 hrsp4 hq4 ↦ ?_
  obtain ⟨hval4, hch4, hsv4⟩ := hq4
  rw [e3rdi] at hch4
  have hs4 : SameOutside st3.data.dmem st4.data.dmem
      (EachRow.Hit m0 1984 eachRowNextStack 1176 1432) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr3.rsp0 (N' := subspaceAtTableStack)
      (by decide) le_rfl (by decide) hch4
  have hfr4 : FR m0 8 st4.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr3 hrsp4 hsv4 hs4 (by decide)
  have hpairs : pairsOf st3.data.dmem (fb m0 + BitVec.ofNat 64 1440) (tableOf m0).size =
      (tableOf m0).toList := by
    have := EachRow.pairsOf_of_pairsAt hlow.tab.2.2
    rw [show off (fb m0 + BitVec.ofNat 64 1432) 8 = fb m0 + BitVec.ofNat 64 1440 from
      NativeRustcVm.addr_add_add _ _ _, Array.length_toList] at this
    exact this
  rw [e3rdi, e3rsi, e3rdx, e3rcx, hpairs, Array.toArray_toList, UInt64.ofBitVec_toBitVec] at hval4
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hfr4 hs4 hsv4 hval4
  subst hpc4
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b16Offset + b16.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b17Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b16_next]]
  have k4 : ∀ r, calleeSaved r = true → r ≠ .r12 → reg d4 r = reg m r := fun r hc hr ↦ by
    rw [sv hsv4 r hc, rv hm3 (v := .reg r) (by revert hc hr; cases r <;> decide)]
    show reg d2 r = _
    rw [k2 r hc, rv hm1 (v := .reg r) (by revert hc; cases r <;> decide)]
    rfl
  refine cont d4 ⟨hfr4, hjr, hjq, hmm3.keep c (by decide) (by decide) (by decide) (by decide) hs4,
    keepW hl (by decide) (by decide) hs4 (by decide) (by decide) w112, ?_, hval4, ?_, ?_, ?_, ?_⟩
  · rw [sv hsv4 .r12 rfl, rv hm3 (v := .reg .rdx) rfl, ← hfoldv]
    rfl
  · rw [k4 .rbp rfl (by decide)]; exact h.rbp
  · rw [k4 .rbx rfl (by decide)]; exact h.rbx
  · rw [k4 .r15 rfl (by decide)]; exact h.r15
  · rw [k4 .r14 rfl (by decide)]; exact h.r14

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
