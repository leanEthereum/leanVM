module

public import NativeRustcVmX64.Whir.EachRowOfFinalLevel.IterC
public import NativeRustcVmX64.Code.Vm.EachRowOfFinalLevel.Names
public import NativeRustcVmX64.Code.Vm.NovelEval.Names

/-!
# `each_row` with `final_level`'s closure: the check of a row (x86-64)

At `b13` (`AtB13`): `b13` calls `novel_eval` on the folded scalars (the stack arguments `1`, `2`)
and the `What`s, its `Option<EW>` at 80; `b14` checks its `Some`, `b15`, `b16` compare it with the
folded row limb by limb (a difference: the outcome `false`); `b17` counts the row: the next
iteration, or the outcome `true` after the last row (`iter_d`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfFinalLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfFinalLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

theorem toBitVec_beq (a b : UInt64) : (a.toBitVec == b.toBitVec) = (a == b) := by
  by_cases h : a = b
  · subst h; simp
  · have : a.toBitVec ≠ b.toBitVec := fun h' ↦ h (UInt64.toBitVec_inj.mp h')
    simp [h, this]

theorem add_ofNat_ofNat (a : BitVec 64) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := addr_add _ _ _

variable [Host] {k : Nat}

/-- **The check of a row**: from `b13` to the next iteration or the exit. -/
theorem iter_d (hp : Placed code k) (hnov : Spec (label NativeRustcVmX64.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (hpre : EachRowFinalPre rows op m0) {m : MachineData} (h : AtB13 rows m0 j m)
    (cont : ∀ m', Inv rows m0 (j + 1) m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset)⟩ := by
  have hl := lay hpre
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowFinalStack = 3088 := rfl
  have hflen : (stackArg m0 2).toNat ≤ laneCap := hpre.2.1
  have hfold : WhirIn m0 (stackArg m0 1) (16 * (stackArg m0 2).toNat) eachRowFinalStack := hpre.2.2.1
  have hjr := h.hj
  have hjq := h.hjq
  have hrs : rows.size ≤ 256 := hpre.1.2.2.1.2.1
  let q := (qsOf m0)[j]'hjq
  let W := subspaceAtTable (tableOf m0) q
  let F := foldRow (lanesJ m0 (rows[j]'hjr)) q (eachRowArgs m0).2
  have hWs : W.size ≤ 31 := by have := h.what.1; rwa [Array.length_toList] at this
  -- `b13`: `novel_eval`
  obtain ⟨hwf, hm⟩ := frame_env hpre h.fr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset + b13.length)).toBitVec
  have hk13 : b13.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset) := b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hl1128 : (EachRow.envE m0 m 1936 24 [] (fun _ ↦ 0)
      (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset + b13.length)).toBitVec).load 0 1128 8 = BitVec.ofNat 64 W.size := by
    have := h.what.2.1
    rw [Array.length_toList] at this
    exact NativeRustcVmX64.Arrays.load_word this
  have hult : (BitVec.ofNat 64 W.size).ult (BitVec.ofNat 64 32) = true := by
    rw [BitVec.ult, decide_eq_true_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  refine exec_then hk13 run_b13 hwf (fun _ _ ↦ rfl) hm fun st1 hm1 hpc1 ↦ ?_
  have hs1 : SameOutside m.dmem st1.data.dmem (EachRow.Hit m0 1936 eachRowFinalStack 1384 1384) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm1 hwf (by decide)
  have hfr1 : FR m0 0 st1.data :=
    h.fr.step hl le_rfl (by decide) ((rv hm1 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm1.kept hwf) hs1 (by decide)
  have e1rdi : reg st1.data .rdi = fb m0 + BitVec.ofNat 64 80 :=
    (rv hm1 (v := .ptr 0 80) rfl).trans (EachRow.eval_ptr0 80)
  have e1rsi : reg st1.data .rsi = stackArg m0 1 :=
    (rv hm1 (v := .load 0 1952 8) rfl).trans (argW hpre h.fr 1 (by decide))
  have e1rdx : reg st1.data .rdx = stackArg m0 2 :=
    (rv hm1 (v := .load 0 1960 8) rfl).trans (argW hpre h.fr 2 (by decide))
  have e1rcx : reg st1.data .rcx = fb m0 + BitVec.ofNat 64 1136 := by
    rw [rv hm1 (v := .ite (.cmp .ult .W64 (.load 0 1128 8) (.lit 32)) (.ptr 0 1136) (.lit 8)) rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hl1128, hult]
    exact EachRow.eval_ptr0 1136
  have e1r8 : (reg st1.data .r8).toNat = W.size := by
    rw [rv hm1 (v := .ite (.not (.cmp .ult .W64 (.load 0 1128 8) (.lit 32))) (.lit 0)
      (.load 0 1128 8)) rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hl1128, hult]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  have hP1 : NovelEvalPre st1.data := by
    unfold NovelEvalPre
    rw [e1rdi, e1rsi, e1rdx, e1rcx, e1r8]
    refine ⟨hfr1.stackOk hl (by decide), hfr1.whirIn_input hl hfold (by decide),
      hfr1.whirIn_frame hl (by decide) (by omega) (by decide),
      hfr1.whirIn_frame hl (by decide) (by decide) (by decide), ?_⟩
    apply hfr1.got_callee hl (hpre.2.2.2.symbols (by decide)) (got_nw hpre)
      (by intro q h; cases h) (by decide)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨(stackArg m0 1, 16 * (stackArg m0 2).toNat), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 eachRowFinalStack, eachRowFinalStack + 8), by simp, ?_, ?_⟩ <;>
        rw [hl.addr (o := 1136) (by decide), hl.baseN, hstk] <;> omega
    · refine ⟨(stackBelow m0 eachRowFinalStack, eachRowFinalStack + 8), by simp, ?_, ?_⟩ <;>
        rw [hl.addr (o := 80) (by decide), hl.baseN, hstk] <;> omega
  refine call_then hpc1 hnov hP1 fun st2 hpc2 hrsp2 hq2 ↦ ?_
  obtain ⟨hval, hch, hsv⟩ := hq2
  rw [e1rdi] at hch
  have hs2 : SameOutside st1.data.dmem st2.data.dmem
      (EachRow.Hit m0 1936 eachRowFinalStack 80 104) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr1.rsp0 (N' := novelEvalStack) (by decide)
      le_rfl (by decide) hch
  have hfr2 : FR m0 8 st2.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr1 hrsp2 hsv hs2 (by decide)
  let r := novelEval (foldedOf m0) W
  have hr : OptEWAt st2.data.dmem (fb m0 + BitVec.ofNat 64 80) (some r) := by
    have hsl : slice st1.data (stackArg m0 1) (stackArg m0 2) = foldedOf m0 := by
      unfold slice
      rw [NativeRustcVm.ewsOf_congr (hfr1.input_same hl hfold fun _ _ h ↦ h)]
      rfl
    have hws : wordSlice st1.data (fb m0 + BitVec.ofNat 64 1136) W.size = W := by
      unfold wordSlice
      have hw := h.what.2.2
      rw [show fb m0 + BitVec.ofNat 64 1128 + 8#64 = fb m0 + BitVec.ofNat 64 1136 from
        addr_add _ _ _] at hw
      have hw' : WordsAt st1.data.dmem (fb m0 + BitVec.ofNat 64 1136) W.toList :=
        EachRow.keep_frame hl le_rfl (by decide) hs1 (by decide)
          (.inl (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList]; omega)) hw
      have := NativeRustcVm.wordsOf_of_wordsAt hw'
      rw [Array.length_toList] at this
      rw [this, Array.toArray_toList]
    rw [e1rdi, e1rsi, e1rdx, e1rcx, e1r8, hsl, hws] at hval
    simp only [hflen, ↓reduceIte] at hval
    exact hval
  obtain ⟨d2, pc2⟩ := st2
  simp only at hpc2 hfr2 hs2 hsv hr
  subst hpc2
  rw [show k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13Offset + b13.length = k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b14Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfFinalLevel.b13_next]]
  have k2 : ∀ r, calleeSaved r = true → (after b13 frameS).reg r = some (.reg r) →
      reg d2 r = reg m r := fun r hc hr ↦ by
    rw [sv hsv r hc]
    exact rv hm1 (by rw [← after_eq run_b13]; exact hr)
  have hmm2 := (h.mm.keep hl le_rfl (by decide) (by decide) (by decide) hs1).keep hl (by decide)
    (by decide) (by decide) (by decide) hs2
  have w48 := keepW hl (by decide) (by decide) hs2 (by decide) (by decide)
    (keepW hl le_rfl (by decide) hs1 (by decide) (by decide) h.w48)
  have w56 := keepW hl (by decide) (by decide) hs2 (by decide) (by decide)
    (keepW hl le_rfl (by decide) hs1 (by decide) (by decide) h.w56)
  -- `b14` to `b17`
  obtain ⟨hwf2, hm2⟩ := frame_env hpre hfr2 0
  have htag : (EachRow.envE m0 d2 1936 24 []).load 0 80 1 = BitVec.ofNat 64 (1 : UInt64).toNat :=
    NativeRustcVmX64.Transcript.load1_of_tag (.inr rfl) hr.1
  have hrc := NativeRustcVm.ewAt_iff.mp hr.2
  have hr0 : (EachRow.envE m0 d2 1936 24 []).load 0 88 8 = r.c0.toBitVec := by
    have := hrc.1
    rw [show off (fb m0 + BitVec.ofNat 64 80) 8 = fb m0 + BitVec.ofNat 64 88 from
      addr_add _ _ _] at this
    exact NativeRustcVmX64.Arrays.load_word this
  have hr1 : (EachRow.envE m0 d2 1936 24 []).load 0 96 8 = r.c1.toBitVec := by
    have := hrc.2
    rw [show off (fb m0 + BitVec.ofNat 64 80) 8 + BitVec.ofNat 64 8 = fb m0 + BitVec.ofNat 64 96
      by unfold off; rw [add_ofNat_ofNat, add_ofNat_ofNat]] at this
    exact NativeRustcVmX64.Arrays.load_word this
  have hF : F = ewArg (reg d2 .rbp) (reg d2 .r14) := by
    rw [k2 .rbp rfl rfl, k2 .r14 rfl rfl]
    exact h.fold.symm
  have hrbp : (EachRow.envE m0 d2 1936 24 []).regs .rbp = F.c0.toBitVec := by rw [hF]; rfl
  have hr14 : (EachRow.envE m0 d2 1936 24 []).regs .r14 = F.c1.toBitVec := by rw [hF]; rfl
  have hok : okOf m0 q (rows[j]'hjr) = (F.c0 == r.c0 && F.c1 == r.c1) := EachRow.ew_beq _ _
  have hL12 : Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_12 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b19Offset) := hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_12_at
  have hfalse : ∀ {d : MachineData} {S : SState}, Match (EachRow.envE m0 d2 1936 24 []) S d → S.mem = [] →
      S.reg .rsp = some (.ptr 0 8) → okOf m0 q (rows[j]'hjr) = false →
      Eventually (step1 Host.exe) (Done rows m0) ⟨d, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b19Offset)⟩ :=
    fun hm' hmem hsp' hb ↦ exit_false hp hpre (hfr2.ofBlock hwf2 hm' hmem hsp')
      (EachRow.finalOk_false hjq hjr hb)
  have hk14 : b14.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b14Offset) := b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk15 : b15.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b15Offset) := b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk16 : b16.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b16Offset) := b16_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk14 run_b14 hwf2 (fun _ h ↦ by cases h) hm2 fun st3 hm3 hpc3 ↦ ?_
  have hpc3' : st3.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b15Offset) := by
    simp only [PcOk] at hpc3
    rw [hpc3]
    simp only [SBool.eval, Sym.eval, CmpOp.apply, htag]
    rfl
  refine exec_at hk15 (exec_after run_b14 run_b15) hwf2 (fun _ h ↦ by cases h) hpc3' hm3
    fun st4 hm4 hpc4 ↦ ?_
  simp only [PcOk] at hpc4
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hrbp, hr0, toBitVec_beq] at hpc4
  by_cases hc0 : F.c0 = r.c0
  swap
  · simp only [beq_false_of_ne hc0, Bool.not_false, ↓reduceIte, hL12] at hpc4
    obtain ⟨d, pc⟩ := st4
    simp only at hpc4
    subst hpc4
    refine hfalse hm4 rfl rfl ?_
    rw [hok, beq_false_of_ne hc0, Bool.false_and]
  simp only [hc0, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc4
  refine exec_at hk16 (exec_after (exec_after run_b14 run_b15) run_b16) hwf2
    (fun _ h ↦ by cases h) hpc4 hm4 fun st5 hm5 hpc5 ↦ ?_
  simp only [PcOk] at hpc5
  simp only [SBool.eval, Sym.eval, CmpOp.apply, low_W64, hr14, hr1, toBitVec_beq] at hpc5
  by_cases hc1 : F.c1 = r.c1
  swap
  · simp only [beq_false_of_ne hc1, Bool.not_false, ↓reduceIte, hL12] at hpc5
    obtain ⟨d, pc⟩ := st5
    simp only at hpc5
    subst hpc5
    refine hfalse hm5 rfl rfl ?_
    rw [hok, beq_false_of_ne hc1, Bool.and_false]
  simp only [hc1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc5
  have hokj : okOf m0 q (rows[j]'hjr) = true := by
    rw [hok, hc0, hc1]
    simp
  have ok' : ∀ i (h1 : i < (qsOf m0).size) (h2 : i < rows.size), i < j + 1 →
      okOf m0 (qsOf m0)[i] rows[i] = true := fun i h1 h2 hi ↦ by
    rcases Nat.lt_or_ge i j with hij | hij
    · exact h.ok i h1 h2 hij
    · obtain rfl : i = j := by omega
      exact hokj
  refine exec_at hk17 (exec_after (exec_after (exec_after run_b14 run_b15) run_b16) run_b17)
    hwf2 (fun _ h ↦ by cases h) hpc5 hm5 fun st6 hm6 hpc6 ↦ ?_
  have hfr6 : FR m0 8 st6.data := hfr2.ofBlock hwf2 hm6 rfl rfl
  have hd6 : st6.data.dmem = d2.dmem := hm6.dmem_eq hwf2 rfl
  have hl56 : (EachRow.envE m0 d2 1936 24 []).load 0 56 8 = BitVec.ofNat 64 (rows.size - (j + 1)) :=
    NativeRustcVmX64.Arrays.load_word w56
  have hc6 : (SBool.cmp .eq .W64 (.bin .and .W64 (.load 0 56 8) (.load 0 56 8)) (.lit 0)).eval
      (EachRow.envE m0 d2 1936 24 []) = decide (rows.size = j + 1) := by
    rw [NativeRustcVmX64.Arrays.eval_test, Sym.eval, hl56,
      NativeRustcVmX64.Arrays.beq_ofNat _ (by decide), BitVec.toNat_ofNat]
    simp only [decide_eq_decide]
    omega
  have hcn : (SBool.not (.cmp .eq .W64 (.bin .and .W64 (.load 0 56 8) (.load 0 56 8))
      (.lit 0))).eval (EachRow.envE m0 d2 1936 24 []) = !decide (rows.size = j + 1) := by
    show (!SBool.eval _ _) = _
    rw [hc6]
  simp only [PcOk] at hpc6
  rw [hcn] at hpc6
  by_cases hlast : rows.size = j + 1
  · -- the last row
    simp only [hlast, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc6
    obtain ⟨d, pc⟩ := st6
    simp only at hpc6 hfr6
    subst hpc6
    exact exit_true hp hpre hfr6 (EachRow.finalOk_of (j := j + 1) (.inr (by omega)) ok')
  · simp only [hlast, decide_false, Bool.not_false, ↓reduceIte] at hpc6
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_3 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfFinalLevel.b5Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfFinalLevel.label_3_at]
      at hpc6
    obtain ⟨d, pc⟩ := st6
    simp only at hpc6 hfr6 hd6 hm6
    subst hpc6
    have hlow := hmm2.low
    refine cont d ⟨hfr6, hd6 ▸ hlow, by omega, by omega, ok', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rv hm6 (v := .bin .add .W64 (.lit 8) (.load 0 48 8)) rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [NativeRustcVmX64.Arrays.load_word w48]
      show BitVec.ofNat 64 8 + (reg m0 .rsi + BitVec.ofNat 64 (8 * j)) = _
      rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
    · rw [rv hm6 (v := .bin .add .W64 (.load 0 64 8) (.lit 1)) rfl]
      simp only [Sym.eval, BinOp.apply, low_W64, ext_W64]
      rw [NativeRustcVmX64.Arrays.load_word hmm2.w64]
      show BitVec.ofNat 64 j + BitVec.ofNat 64 1 = _
      rw [← BitVec.ofNat_add]
    · rw [rv hm6 (v := .load 0 56 8) rfl]
      exact hl56
    · rw [rv hm6 (v := .load 0 16 8) rfl]
      exact NativeRustcVmX64.Arrays.load_word hlow.w16
    · rw [rv hm6 (v := .reg .r15) rfl]
      show reg d2 .r15 = _
      rw [k2 .r15 rfl rfl]
      exact h.r15
    · rw [rv hm6 (v := .reg .rbx) rfl]
      show reg d2 .rbx = _
      rw [k2 .rbx rfl rfl]
      exact h.rbx
    · exact (rv hm6 (v := .ptr 0 104) rfl).trans (EachRow.eval_ptr0 104)

end

end NativeRustcVmX64.Whir.EachRowOfFinalLevel
