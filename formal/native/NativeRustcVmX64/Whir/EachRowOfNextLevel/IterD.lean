module

public import NativeRustcVmX64.Whir.EachRowOfNextLevel.IterC
public import NativeRustcVmX64.Code.Vm.EachRowOfNextLevel.Names
public import NativeRustcVmX64.Code.Vm.NovelEval.Names

/-!
# `each_row` with `next_level`'s closure: the `What`s at `μ`, `novel_eval` (x86-64)

At `b17` (`AtB17`): `b17` reads `μ` through the closure and caps the `What`s' count; `b18` reads
`What` `μ` when it exists (R13, else `0`); `b19` calls `novel_eval` on the high part and the
`What`s, its `Option<EW>` at 128; `b20` checks its `Some` (always): at `b21` (`AtB21`,
`iter_d`).
-/

namespace NativeRustcVmX64.Whir.EachRowOfNextLevel

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Whir
open NativeRustcVmX64.Vm.EachRowOfNextLevel
open NativeRustcVm (WordAt WordsAt EWAt EWsAt BufWordsAt)
open NativeRustcVm.Transcript (off OptEWAt)

@[expose] public section

/-- Row `j`'s `What`s. -/
abbrev whatJ (m0 : MachineData) (q : UInt64) : Array UInt64 := subspaceAtTable (tableOf m0) q

/-- **At `b21`**, in iteration `j`: `novel_eval`'s value at 128, `What` `μ` in R13. -/
structure AtB21 (rows : Array (Array UInt64)) (m0 : MachineData) (j : Nat) (m : MachineData) :
    Prop where
  fr : FR m0 8 m
  hj : j < rows.size
  hjq : j < (qsOf m0).size
  mm : MidN rows m0 j m.dmem
  w112 : WordAt m.dmem (fb m0 + BitVec.ofNat 64 112) (foldJ rows m0 j hj hjq).c0
  r12 : reg m .r12 = (foldJ rows m0 j hj hjq).c1.toBitVec
  nov : OptEWAt m.dmem (fb m0 + BitVec.ofNat 64 128)
    (some (novelEval (highOf m0) (whatJ m0 ((qsOf m0)[j]'hjq))))
  r13 : reg m .r13 = ((whatJ m0 ((qsOf m0)[j]'hjq)).getD (reg m0 .r8).toNat 0).toBitVec
  rbx : reg m .rbx = BitVec.ofNat 64 j
  r15 : reg m .r15 = reg m0 .rsi + BitVec.ofNat 64 (8 * j)
  r14 : reg m .r14 = bOf m0

end

public section

variable {rows : Array (Array UInt64)} {op : BitVec 64} {m0 : MachineData} {j : Nat}

variable [Host] {k : Nat}

/-- **`b20`**: `novel_eval`'s `Some`, nothing changed. -/
theorem b20_step (hp : Placed code k) (c : Ctx rows op m0) {m : MachineData} (h : AtB21 rows m0 j m)
    (cont : ∀ m', AtB21 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b20Offset)⟩ := by
  obtain ⟨hwf3, hm3⟩ := frame_env c h.fr 0
  have hk20 : b20.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b20Offset) := b20_in_code.trans hp.1 (List.cons_ne_nil _ _)
  have htag : (EachRow.envE m0 m 1984 16 [] (fun _ ↦ 0) 0).load 0 128 4 =
      BitVec.ofNat 64 (1 : UInt64).toNat :=
    NativeRustcVmX64.Transcript.load4_of_tag (.inr rfl) h.nov.1
  refine exec_then hk20 run_b20 hwf3 (fun _ h ↦ by cases h) hm3 fun st4 hm4 hpc4 ↦ ?_
  have hfr4 : FR m0 8 st4.data := h.fr.ofBlock hwf3 hm4 rfl (by decide)
  have hd4 : st4.data.dmem = m.dmem := hm4.dmem_eq hwf3 rfl
  simp only [PcOk] at hpc4
  split at hpc4
  · rename_i hc
    simp only [SBool.eval, Sym.eval, CmpOp.apply, htag] at hc
    exact absurd hc (by decide)
  obtain ⟨d4, pc4⟩ := st4
  simp only at hpc4 hfr4 hd4 hm4
  subst hpc4
  have k4 : ∀ r, calleeSaved r = true → reg d4 r = reg m r := fun r hc ↦
    rv hm4 (v := .reg r) (by revert hc; cases r <;> decide)
  exact cont d4 ⟨hfr4, h.hj, h.hjq, hd4 ▸ h.mm, hd4 ▸ h.w112, (k4 .r12 rfl).trans h.r12,
    hd4 ▸ h.nov, (k4 .r13 rfl).trans h.r13, (k4 .rbx rfl).trans h.rbx, (k4 .r15 rfl).trans h.r15,
    (k4 .r14 rfl).trans h.r14⟩

/-- **From `b19`**, R13 `What` `μ`: `novel_eval`, `b20`, to `b21`. -/
theorem iter_d_tail (hp : Placed code k)
    (hnov : Spec (label NativeRustcVmX64.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB17 rows m0 j m)
    (cont : ∀ m', AtB21 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b20Offset)⟩) :
    ∀ st : MachineState, st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b19Offset) → FR m0 8 st.data →
      st.data.dmem = m.dmem → reg st.data .rcx = fb m0 + BitVec.ofNat 64 1184 →
      reg st.data .r8 = BitVec.ofNat 64 (whatJ m0 ((qsOf m0)[j]'h.hjq)).size →
      reg st.data .r13 =
        ((whatJ m0 ((qsOf m0)[j]'h.hjq)).getD (reg m0 .r8).toNat 0).toBitVec →
      (∀ r, calleeSaved r = true → r ≠ .r13 → reg st.data r = reg m r) →
      Eventually (step1 Host.exe) (Done rows m0) st := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  obtain ⟨W, hW⟩ : ∃ W, W = whatJ m0 ((qsOf m0)[j]'h.hjq) := ⟨_, rfl⟩
  have hwhat : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1176) rootCap W.toList := by
    rw [hW]; exact h.what
  have hWs : W.size ≤ 31 := by have := hwhat.1; rwa [Array.length_toList] at this
  have hWw := hwhat.2.2
  rw [show fb m0 + BitVec.ofNat 64 1176 + 8#64 = fb m0 + BitVec.ofNat 64 1184 from
    addr_add _ _ _] at hWw
  intro st hpc hfr hd hrcx hr8 hr13 hk
  rw [← hW] at hr8 hr13
  obtain ⟨d, pc⟩ := st
  simp only at hpc hfr hd hrcx hr8 hr13 hk
  subst hpc
  obtain ⟨hwf9, hm9⟩ := frame_env c hfr (Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b19Offset + b19.length)).toBitVec
  have hk19 : b19.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b19Offset) := b19_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk19 run_b19 hwf9 (fun _ _ ↦ rfl) hm9 fun st2 hm2 hpc2 ↦ ?_
  have hs2 : SameOutside d.dmem st2.data.dmem (EachRow.Hit m0 1984 eachRowNextStack 1432 1432) :=
    EachRow.hit_of_block hl le_rfl (by decide) hm2 hwf9 (by decide)
  have hfr2 : FR m0 0 st2.data :=
    hfr.step hl le_rfl (by decide) ((rv hm2 (v := .ptr 0 0) rfl).trans (EachRow.eval_ptr0 0))
      (hm2.kept hwf9) hs2 (by decide)
  have hmm := h.mm
  rw [← hd] at hmm
  have e2rdi : reg st2.data .rdi = fb m0 + BitVec.ofNat 64 128 :=
    (rv hm2 (v := .ptr 0 128) rfl).trans (EachRow.eval_ptr0 128)
  have e2rsi : reg st2.data .rsi = nextEnv m0 1 :=
    (rv hm2 (v := .load 0 56 8) rfl).trans (NativeRustcVmX64.Arrays.load_word hmm.low.w56)
  have e2rdx : reg st2.data .rdx = nextEnv m0 2 :=
    (rv hm2 (v := .load 0 48 8) rfl).trans (NativeRustcVmX64.Arrays.load_word hmm.low.w48)
  have e2rcx : reg st2.data .rcx = fb m0 + BitVec.ofNat 64 1184 :=
    (rv hm2 (v := .reg .rcx) rfl).trans hrcx
  have e2r8 : (reg st2.data .r8).toNat = W.size := by
    rw [rv hm2 (v := .reg .r8) rfl]
    show (reg d .r8).toNat = _
    rw [hr8, BitVec.toNat_ofNat]
    omega
  have hP : NovelEvalPre st2.data := by
    unfold NovelEvalPre
    rw [e2rdi, e2rsi, e2rdx, e2rcx, e2r8]
    refine ⟨hfr2.stackOk hl (by decide), hfr2.whirIn_input hl c.hin (by decide),
      hfr2.whirIn_frame hl (by decide) (by omega) (by decide),
      hfr2.whirIn_frame hl (by decide) (by decide) (by decide), ?_⟩
    apply hfr2.got_callee hl (c.got.symbols (by decide)) c.got_nw
      (fun q h => ⟨(bOf m0, 16), by simp, h⟩) (by decide)
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨(nextEnv m0 1, 16 * (nextEnv m0 2).toNat), by simp, le_rfl, le_rfl⟩
    · refine ⟨(stackBelow m0 eachRowNextStack, eachRowNextStack + 8), by simp, ?_, ?_⟩ <;>
        rw [hl.addr (o := 1184) (by decide), hl.baseN] <;>
        have := hl.sp <;> rw [stack_eq] at * <;> omega
    · refine ⟨(stackBelow m0 eachRowNextStack, eachRowNextStack + 8), by simp, ?_, ?_⟩ <;>
        rw [hl.addr (o := 128) (by decide), hl.baseN] <;>
        have := hl.sp <;> rw [stack_eq] at * <;> omega
  refine call_then hpc2 hnov hP fun st3 hpc3 hrsp3 hq3 ↦ ?_
  obtain ⟨hval, hch, hsv⟩ := hq3
  rw [e2rdi] at hch
  have hs3 : SameOutside st2.data.dmem st3.data.dmem
      (EachRow.Hit m0 1984 eachRowNextStack 128 152) :=
    EachRow.hit_of_call hl (by decide) (by decide) hfr2.rsp0 (N' := novelEvalStack) (by decide)
      le_rfl (by decide) hch
  have hfr3 : FR m0 8 st3.data :=
    EachRow.Fr.call hl (by decide) (by decide) hfr2 hrsp3 hsv hs3 (by decide)
  have hr : OptEWAt st3.data.dmem (fb m0 + BitVec.ofNat 64 128)
      (some (novelEval (highOf m0) W)) := by
    have hsl : slice st2.data (nextEnv m0 1) (nextEnv m0 2) = highOf m0 := by
      unfold slice
      rw [NativeRustcVm.ewsOf_congr (hfr2.input_same hl c.hin (notB_in c c.hin c.bh))]
      rfl
    have hws : wordSlice st2.data (fb m0 + BitVec.ofNat 64 1184) W.size = W := by
      unfold wordSlice
      have hw' : WordsAt st2.data.dmem (fb m0 + BitVec.ofNat 64 1184) W.toList :=
        EachRow.keep_frame hl le_rfl (by decide) hs2 (by decide)
          (.inl (by rw [NativeRustcVm.length_wordsBytes, Array.length_toList]; omega))
          (by rw [hd]; exact hWw)
      have := NativeRustcVm.wordsOf_of_wordsAt hw'
      rw [Array.length_toList] at this
      rw [this, Array.toArray_toList]
    rw [e2rdi, e2rsi, e2rdx, e2rcx, e2r8, hsl, hws] at hval
    have hlen : (nextEnv m0 2).toNat ≤ laneCap := c.hlen
    simp only [hlen, ↓reduceIte] at hval
    exact hval
  obtain ⟨d3, pc3⟩ := st3
  simp only at hpc3 hfr3 hs3 hsv hr
  subst hpc3
  rw [show k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b19Offset + b19.length = k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b20Offset from by rw [Nat.add_assoc, NativeRustcVmX64.Vm.EachRowOfNextLevel.b19_next]]
  have k3 : ∀ r, calleeSaved r = true → r ≠ .r13 → reg d3 r = reg m r := fun r hc hr ↦ by
    rw [sv hsv r hc]
    exact (rv hm2 (v := .reg r) (by revert hc; cases r <;> decide)).trans (hk r hc hr)
  have k13 : reg d3 .r13 = reg d .r13 := by
    rw [sv hsv .r13 rfl]
    exact rv hm2 (v := .reg .r13) rfl
  have hmm3 : MidN rows m0 j d3.dmem :=
    (hmm.keep c le_rfl (by decide) (by decide) (by decide) hs2).keep c (by decide)
      (by decide) (by decide) (by decide) hs3
  have w112 : WordAt d3.dmem (fb m0 + BitVec.ofNat 64 112) (foldJ rows m0 j h.hj h.hjq).c0 := by
    have := h.w112
    rw [← hd] at this
    exact keepW hl (by decide) (by decide) hs3 (by decide) (by decide)
      (keepW hl le_rfl (by decide) hs2 (by decide) (by decide) this)
  have hr' : OptEWAt d3.dmem (fb m0 + BitVec.ofNat 64 128)
      (some (novelEval (highOf m0) (whatJ m0 ((qsOf m0)[j]'h.hjq)))) := by
    rw [← hW]; exact hr
  have hr13' : reg d3 .r13 =
      ((whatJ m0 ((qsOf m0)[j]'h.hjq)).getD (reg m0 .r8).toNat 0).toBitVec := by
    rw [← hW]; exact k13.trans hr13
  exact cont d3 ⟨hfr3, h.hj, h.hjq, hmm3, w112, (k3 .r12 rfl (by decide)).trans h.r12, hr',
    hr13', (k3 .rbx rfl (by decide)).trans h.rbx, (k3 .r15 rfl (by decide)).trans h.r15,
    (k3 .r14 rfl (by decide)).trans h.r14⟩

/-- **The `What`s at `μ`, `novel_eval`**: from `b17` to `b21`. -/
theorem iter_d (hp : Placed code k) (hnov : Spec (label NativeRustcVmX64.Vm.NovelEval.entryLabel) NovelEvalPre NovelEvalPost)
    (c : Ctx rows op m0) {m : MachineData} (h : AtB17 rows m0 j m)
    (cont : ∀ m', AtB21 rows m0 j m' →
      Eventually (step1 Host.exe) (Done rows m0) ⟨m', Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b21Offset)⟩) :
    Eventually (step1 Host.exe) (Done rows m0) ⟨m, Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b17Offset)⟩ := by
  have hl := lay c
  have hsp := hl.sp
  have htop := hl.ok.2.1
  have hstk : eachRowNextStack = 3136 := rfl
  have hjr := h.hj
  have hjq := h.hjq
  obtain ⟨W, hW⟩ : ∃ W, W = whatJ m0 ((qsOf m0)[j]'hjq) := ⟨_, rfl⟩
  have hwhat : BufWordsAt m.dmem (fb m0 + BitVec.ofNat 64 1176) rootCap W.toList := by
    rw [hW]; exact h.what
  let μ := (reg m0 .r8).toNat
  have hmu : μ ≤ 30 := c.mu
  have hWs : W.size ≤ 31 := by have := hwhat.1; rwa [Array.length_toList] at this
  have hWw := hwhat.2.2
  rw [show fb m0 + BitVec.ofNat 64 1176 + 8#64 = fb m0 + BitVec.ofNat 64 1184 from
    addr_add _ _ _] at hWw
  -- `b17`
  let env7 := EachRow.envE m0 m 1984 0 [(nextEnv m0 0, 8)] (fun _ ↦ 0) 0
  have hwf7 : env7.WF := env1 c h.fr c.muin 0
  have hl64 : env7.load 0 64 8 = nextEnv m0 0 := NativeRustcVmX64.Arrays.load_word h.mm.low.w64
  have hm7 : Match env7 muS m :=
    match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨h.fr.match_rsp, trivial⟩ trivial trivial
      ⟨by
        show env7.load 0 64 8 = nextEnv m0 0 + BitVec.ofInt 64 0
        rw [hl64]
        exact (BitVec.add_zero _).symm, trivial⟩
  have hmuv : env7.load 1 0 8 = reg m0 .r8 := by
    rw [NativeRustcVmX64.Arrays.load8_eq]
    show (NativeRustcVm.wordOf m.dmem (nextEnv m0 0 + BitVec.ofNat 64 0)).toBitVec = _
    have hs := h.fr.input_same hl c.muin (notB_in c c.muin c.bmu)
    rw [NativeRustcVm.addr_add_zero, NativeRustcVm.wordOf_congr (d := m0.dmem) hs, c.muw]
  have hl1176 : env7.load 0 1176 8 = BitVec.ofNat 64 W.size := by
    have := hwhat.2.1
    rw [Array.length_toList] at this
    exact NativeRustcVmX64.Arrays.load_word this
  have hult : (BitVec.ofNat 64 W.size).ult (BitVec.ofNat 64 32) = true := by
    rw [BitVec.ult, decide_eq_true_iff, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  have hk17 : b17.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b17Offset) := b17_in_code.trans hp.1 (List.cons_ne_nil _ _)
  refine exec_then hk17 run_b17 hwf7 (fun _ h ↦ by cases h) hm7 fun st1 hm1 hpc1 ↦ ?_
  have hd1 : st1.data.dmem = m.dmem := hm1.dmem_eq hwf7 rfl
  have hfr1 : FR m0 8 st1.data := h.fr.ofBlock hwf7 hm1 rfl rfl
  have e1rax : reg st1.data .rax = reg m0 .r8 := (rv hm1 (v := .load 1 0 8) rfl).trans hmuv
  have e1rcx : reg st1.data .rcx = fb m0 + BitVec.ofNat 64 1184 := by
    rw [rv hm1 (v := .ite (.cmp .ult .W64 (.load 0 1176 8) (.lit 32)) (.ptr 0 1184) (.lit 8)) rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hl1176, hult]
    exact EachRow.eval_ptr0 1184
  have e1r8 : reg st1.data .r8 = BitVec.ofNat 64 W.size := by
    rw [rv hm1 (v := .ite (.not (.cmp .ult .W64 (.load 0 1176 8) (.lit 32))) (.lit 0)
      (.load 0 1176 8)) rfl]
    simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
    rw [hl1176, hult]
    rfl
  have e1 : ∀ r, calleeSaved r = true → r ≠ .r13 → reg st1.data r = reg m r := fun r hc hr ↦
    rv hm1 (v := .reg r) (by revert hc hr; cases r <;> decide)
  have hcmp : (SBool.not (.cmp .ult .W64 (.load 1 0 8) (.ite (.not (.cmp .ult .W64 (.load 0 1176 8)
      (.lit 32))) (.lit 0) (.load 0 1176 8)))).eval env7 = !decide (μ < W.size) := by
    have hite : (Sym.ite (.not (.cmp .ult .W64 (.load 0 1176 8) (.lit 32))) (.lit 0)
        (.load 0 1176 8)).eval env7 = BitVec.ofNat 64 W.size := by
      simp only [Sym.eval, SBool.eval, CmpOp.apply, low_W64]
      rw [hl1176, hult]
      rfl
    simp only [SBool.eval, CmpOp.apply, low_W64]
    rw [hite]
    show (!(env7.load 1 0 8).ult _) = _
    rw [hmuv, BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have tail := iter_d_tail hp hnov c h fun m' h' ↦ b20_step hp c h' cont
  simp only [PcOk] at hpc1
  rw [hcmp] at hpc1
  by_cases hlt : μ < W.size
  · -- `b18`: `What` `μ`
    simp only [hlt, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hpc1
    obtain ⟨hwf8, hm8⟩ := frame_env c hfr1 0
    have hm8' : Match (EachRow.envE m0 st1.data 1984 16 [] (fun _ ↦ 0) 0) whatS st1.data :=
      match_ofMachine ⟨rfl, trivial⟩
        ⟨hfr1.match_rsp, (e1rcx.trans (EachRow.eval_ptr0 1184).symm), trivial⟩ trivial
        ⟨by
          show (reg st1.data .rax).toNat < 31
          rw [e1rax]
          omega, trivial⟩ trivial
    have hk18 : b18.IsInfixAt Host.prog (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b18Offset) := b18_in_code.trans hp.1 (List.cons_ne_nil _ _)
    refine exec_at hk18 run_b18 hwf8 (fun _ h ↦ by cases h) hpc1 hm8' fun st2 hm2 hpc2 ↦ ?_
    refine tail st2 hpc2 (hfr1.ofBlock hwf8 hm2 rfl rfl) ((hm2.dmem_eq hwf8 rfl).trans hd1)
      ((rv hm2 (v := .ptr 0 1184) rfl).trans (EachRow.eval_ptr0 1184))
      (by rw [← hW]; exact (rv hm2 (v := .reg .r8) rfl).trans e1r8) ?_
      fun r hc hr ↦ (rv hm2 (v := .reg r) (by revert hc hr; cases r <;> decide)).trans (e1 r hc hr)
    rw [← hW, rv hm2 (v := .loadx 0 1184 (.bin .mul .W64 (.reg .rax) (.lit 8)) 8) rfl]
    simp only [Sym.eval, BinOp.apply, low_W64, ext_W64, Env.ofMachine_regs]
    have hax : st1.data.regs.get64 .rax = reg m0 .r8 := e1rax
    rw [hax]
    have hw := NativeRustcVm.WordsAt.getElem hWw (i := μ) (by rw [Array.length_toList]; exact hlt)
    rw [addr_add] at hw
    have hw' : WordAt st1.data.dmem (fb m0 + BitVec.ofNat 64 (1184 + 8 * μ)) (W.toList[μ]'(by
        rw [Array.length_toList]; exact hlt)) := by rw [hd1]; exact hw
    have hidx : (reg m0 .r8 * BitVec.ofNat 64 8).toNat = 8 * μ := by
      rw [BitVec.toNat_mul, BitVec.toNat_ofNat]
      omega
    rw [hidx]
    rw [NativeRustcVmX64.Arrays.load_word hw']
    simp only [Array.getElem_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  · simp only [hlt, decide_false, Bool.not_false, ↓reduceIte] at hpc1
    rw [show Labels.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_11 = Host.addrOf (k + NativeRustcVmX64.Vm.EachRowOfNextLevel.b19Offset) from hp.label NativeRustcVmX64.Vm.EachRowOfNextLevel.label_11_at]
      at hpc1
    refine tail st1 hpc1 hfr1 hd1 e1rcx (by rw [← hW]; exact e1r8) ?_ e1
    rw [← hW, rv hm1 (v := .lit 0) rfl]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    rfl

end

end NativeRustcVmX64.Whir.EachRowOfNextLevel
