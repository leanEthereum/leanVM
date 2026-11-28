module

public import NativeRustcVmX64.Layout.CommitStack.Exec
public import NativeRustcVmX64.Layout.Ladder.Table
public import NativeRustcVmX64.Layout.Stack.Common
public import NativeVm.Model.Stack
public import NativeRustcVmX64.Code.Vm.CommitStack.Names
public import NativeRustcVmX64.Code.Vm.Ladder.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names

/-!
# `commit_stack` on x86-64

`b0` pushes R14, RBX and calls `ladder` on the frame (`16` to `176`). Outside the window the
ladder is `None`: `b1` branches to `b3`, which returns AL = `0` (`commitStack` rejects,
`run_none`). Inside, `b2` checks the level count and `b4` reads level `0`'s fold (`6`) and rate
(`r`), restores the registers and tail-calls `read_commitment` with the shape `(μ - 6 + r, 64)`
(`run_some`).
-/

namespace NativeRustcVmX64.Layout.CommitStack

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.CommitStack NativeRustcVmX64.Transcript
open NativeRustcVm.Transcript NativeVm.Model LeanVM.Parameters NativeRustcVm.Layout
open NativeRustcVmX64.Layout.Ladder (nOf ladderW ladder_eq ladder_none admissible_iff nOf_le
  foldAt qAt length_ladderW)
open NativeRustcVmX64.Layout.Stack (tail_restored retOf_eq)

public section

theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 192 := by decide

theorem stack_eq : commitStackStack = 704 := rfl

/-- `commitStack` in the window: the root at level `0`'s shape. -/
theorem run_some {μ r : Nat} (h : Whir.Admissible μ r) (s : TState) :
    (commitStack μ r).run s = (readCommitment (μ - 6 + r) 64).run s := by
  have hn := nOf_le μ
  obtain ⟨n, hn'⟩ : ∃ n, nOf μ = n + 1 := ⟨nOf μ - 1, by omega⟩
  simp only [commitStack, ladder_eq h, ladderW, hn', List.range_succ_eq_map, List.map_cons,
    liftOpt, pure_bind, levelShape, foldAt, ↓reduceIte]
  rfl

/-- `commitStack` outside the window: rejected. -/
theorem run_none {μ r : Nat} (h : ¬Whir.Admissible μ r) (s : TState) :
    (commitStack μ r).run s = none := by
  simp only [commitStack, ladder_none h, liftOpt, StateT.run_bind]
  rfl

/-- `b2`'s check passes for a count of `3` to `6`. -/
theorem count_ok (n : Nat) (h3 : 3 ≤ n) (h6 : n ≤ 6) :
    (!CmpOp.apply .ult .W64 (BinOp.apply .add .W64 (BitVec.ofNat 64 18446744073709551609)
      (BitVec.ofNat 64 n)) (BitVec.ofNat 64 18446744073709551610)) = true := by
  interval_cases n <;> decide

/-- `b4`'s height: `μ - 6`, saturating, plus `r`. -/
theorem height_eq (x : BitVec 64) (r : Nat) (hx : x.toNat < 2 ^ 32) (hr : r < 2 ^ 32) :
    (BinOp.apply .add .W64 (BitVec.ofNat 64 r)
      (if (!CmpOp.apply .ult .W64 x (BitVec.ofNat 64 6)) = true then
        BinOp.apply .sub .W64 x (BitVec.ofNat 64 6) else BitVec.ofNat 64 0)).toNat =
      x.toNat - 6 + r := by
  simp only [BinOp.apply, CmpOp.apply, low_W64, ext_W64]
  cases h : x.ult (BitVec.ofNat 64 6) with
  | false =>
    simp only [BitVec.ult, decide_eq_false_iff_not, BitVec.toNat_ofNat] at h
    simp (config := { decide := true }) only [↓reduceIte]
    rw [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  | true =>
    simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_ofNat] at h
    simp (config := { decide := true }) only [↓reduceIte]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

variable [Host] {k : Nat}

/-- **`commit_stack`'s contract.** -/
theorem commitStack_spec (hp : Placed code k)
    (hlad : Spec (Labels.label NativeRustcVmX64.Vm.Ladder.entryLabel) LadderPre LadderPost)
    (hrcm : ∀ a s, Spec (Labels.label NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) (ReadCommitmentPre a s)
      (ReadCommitmentPost a s))
    (a : DecArea) (s : TState) :
    Spec (Labels.label NativeRustcVmX64.Vm.CommitStack.entryLabel) (CommitStackPre a s) (CommitStackPost a s) := by
  rintro m0 ⟨hst, hrc, hro, hts, htok, hroots, hgot⟩
  rw [stack_eq] at hst hrc hro htok hgot
  set t := reg m0 .rdi with htdef
  set fb := stackBelow m0 192 with hfb
  have hn : 704 ≤ (rspOf m0).toNat := hst.1
  have h8 : (rspOf m0).toNat + 8 ≤ 2 ^ 64 := hst.2.1
  have hfbN : fb.toNat = (rspOf m0).toNat - 192 := stackBelow_toNat (by omega)
  have hsbN : (stackBelow m0 704).toNat = (rspOf m0).toNat - 704 := stackBelow_toNat hn
  have hfnw : NativeRustcVm.NoWrap fb (192 + 8) := frame_noWrap hst (by decide)
  have hfnw192 : NativeRustcVm.NoWrap fb 192 := by unfold NativeRustcVm.NoWrap at hfnw ⊢; omega
  have hsnw := noWrap_stackBelow hst
  have hsnw' : NativeRustcVm.NoWrap (stackBelow m0 704) 704 := by
    unfold NativeRustcVm.NoWrap at hsnw ⊢; omega
  obtain ⟨⟨hTm, hTn⟩, ⟨hAm, hAn⟩, -⟩ := hts.footprint
  have hfS : ∀ q, NativeRustcVm.InRange fb 192 q →
      NativeRustcVm.InRange (stackBelow m0 704) 704 q :=
    fun q h ↦ inRange_frame_stack h8 hn (by decide) h
  have hRS : ∀ q, NativeRustcVm.InRange (stackBelow m0 704) 704 q →
      ¬ NativeRustcVm.InRange t tstateBytes q ∧ ¬ NativeRustcVm.InRange a.words (8 * a.len) q :=
    fun q hq ↦ ⟨fun h ↦ not_inRange_of_apart htok.1 hTn hsnw h (inRange_mono hq (by omega)),
      fun h ↦ not_inRange_of_apart htok.2.1 hAn hsnw h (inRange_mono hq (by omega))⟩
  have hrcOut : ∀ q, NativeRustcVm.InRange (stackBelow m0 704) 704 q →
      ¬ NativeRustcVm.InRange rcAddr 192 q :=
    fun q hq h ↦ not_inRange_of_apart hrc.2.2 hrc.2.1 hsnw h (inRange_mono hq (by omega))
  -- `b0`: the prologue, `call ladder`.
  have hwf0 := frame_wf (m0 := m0) (d := m0) (F := 192) (rest := []) (vars := fun _ ↦ 0)
    (ret := (Host.addrOf (k + NativeRustcVmX64.Vm.CommitStack.b0Offset + b0.length)).toBitVec) ⟨frame_mapped hst (by decide), hfnw⟩
    (by simp) (List.pairwise_singleton _ _)
  have hm0 : Match (frameEnv m0 m0 192 [] (fun _ ↦ 0) (Host.addrOf (k + NativeRustcVmX64.Vm.CommitStack.b0Offset + b0.length)).toBitVec)
      entryS m0 :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨match_rsp, trivial⟩ trivial trivial trivial
  unfold NativeRustcVmX64.Vm.CommitStack.entryLabel
  rw [hp.label NativeRustcVmX64.Vm.CommitStack.entry_at]
  refine exec_then (infix_of b0_in_code (by simp [b0]) hp) exit_b0 hwf0 (fun _ _ ↦ rfl) hm0
    fun st0 hm1 hpc1 => ?_
  obtain ⟨hpro, hws0, hx7, hx6, hx2, hx3, hx14⟩ := ok_b0
  have hf0 : Frame m0 192 slots 0 st0.data :=
    Frame.of_prologue Frame.entry hwf0 hm1 hpro slots_le (by decide)
  have hs0 : NativeRustcVm.SameOutside m0.dmem st0.data.dmem (NativeRustcVm.InRange fb 192) :=
    sameOutside_low hwf0 hm1 (r := 0) rfl (by decide) hws0
  have hsp0 : rspOf st0.data = fb := by rw [hf0.sp, off_zero]
  have hX7 : reg st0.data .rdi = off fb 16 := (hm1.regs .rdi _ hx7).trans (eval_ptr0 16)
  have hX6 : reg st0.data .rsi = reg m0 .rsi := hm1.regs .rsi _ hx6
  have hX2 : reg st0.data .rdx = reg m0 .rdx := hm1.regs .rdx _ hx2
  have hX3 : reg st0.data .rbx = t := hm1.regs .rbx _ hx3
  have hX14 : reg st0.data .r14 = reg m0 .rsi := hm1.regs .r14 _ hx14
  have hcb : stackBelow st0.data 72 = stackBelow m0 (192 + 72) :=
    stackBelow_callee hsp0 (by omega)
  have hcbN : (stackBelow st0.data 72).toNat = (rspOf m0).toNat - 264 := by
    rw [hcb, stackBelow_toNat (by omega)]
  have h16N : (off fb 16).toNat = (rspOf m0).toNat - 176 := by
    rw [toNat_off (by omega), hfbN]; omega
  -- `ladder`'s precondition.
  have hpre : LadderPre st0.data := by
    show StackOk st0.data 72 ∧ RodataAt st0.data 72 ∧ Readable st0.data (reg st0.data .rdi) 160 ∧
      OffStack st0.data (reg st0.data .rdi) 160 72 ∧ RodataApart (reg st0.data .rdi) 160
    rw [hX7]
    refine ⟨stackOk_callee hst hf0.kept hsp0 (by decide), ?_, ⟨?_, ?_⟩, ?_, fun it ↦ ?_⟩
    · refine RodataAt.mono hro (fun q hq ↦ hs0 q fun h ↦ hq (inRange_mono (hfS q h) (by omega)))
        hsnw ?_ ?_ <;> rw [hcbN, hsbN] <;> omega
    · exact Mapped.keeps (mapped_off (frame_mapped hst (by decide)) (by decide)) hf0.kept
    · show (off fb 16).toNat + 160 ≤ 2 ^ 64; omega
    · show (off fb 16).toNat + 160 ≤ (stackBelow st0.data 72).toNat ∨
        (stackBelow st0.data 72).toNat + (72 + 8) ≤ (off fb 16).toNat
      omega
    · have h := hro.apart it
      unfold NativeRustcVm.Apart at h ⊢
      rw [hsbN] at h
      omega
  refine call_then hpc1 hlad hpre fun st1 hpc2 hrsp2 ⟨hL, hch, hsv⟩ => ?_
  rw [hX7, hX6, hX2] at hL
  rw [hX7] at hch
  have hcal : ∀ q, NativeRustcVm.InRange (stackBelow st0.data 72) 72 q →
      NativeRustcVm.InRange (stackBelow m0 704) 704 q ∧ ¬ NativeRustcVm.InRange fb (192 + 8) q :=
    fun q hq ↦ inRange_callee hsp0 h8 hn (by decide) hq
  have hout : ∀ j, 176 ≤ j → j < 192 + 8 → ∀ q, q = off fb j →
      ¬ (NativeRustcVm.InRange (off fb 16) 160 q ∨
        NativeRustcVm.InRange (stackBelow st0.data 72) 72 q) := by
    rintro j hj1 hj2 q rfl (h | h)
    · rw [inRange_off_iff (by omega) (by omega)] at h; omega
    · exact (hcal _ h).2 (inRange_off_self hj2 (by omega))
  have hf1 : Frame m0 192 slots 8 st1.data :=
    Frame.call_slots hf0 hsv hrsp2 hch
      (fun p hp i hi ↦ hout _ (by
        simp only [slots, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> dsimp only <;> omega)
        (by have := slots_le p hp; omega) _ rfl)
      (fun j hj ↦ hout _ (by omega) (by omega) _ rfl)
  have hso1 : NativeRustcVm.SameOutside m0.dmem st1.data.dmem
      (NativeRustcVm.InRange (stackBelow m0 704) 704) := fun q hq ↦ by
    rw [hch q fun h ↦ h.elim (fun h' ↦ hq (hfS q (inRange_of_off hfnw192 (by decide) h')))
      fun h' ↦ hq (hcal q h').1]
    exact hs0 q fun h ↦ hq (hfS q h)
  have hY3 : reg st1.data .rbx = t := (hsv.1 .rbx rfl).trans hX3
  have hY14 : reg st1.data .r14 = reg m0 .rsi := (hsv.1 .r14 rfl).trans hX14
  -- From the return: `b1`, the tag.
  have hwf1 := frame_wf (m0 := m0) (d := st1.data) (F := 192) (rest := []) (vars := fun _ ↦ 0)
    (ret := 0) ⟨Mapped.keeps (frame_mapped hst (by decide)) hf1.kept, hfnw⟩ (by simp)
    (List.pairwise_singleton _ _)
  have hm2 : Match (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0) retS st1.data :=
    match_ofMachine ⟨rfl, trivial⟩ ⟨hf1.rsp_eval, trivial⟩ trivial trivial trivial
  refine exec_at (infix_of b1_in_code (by simp [b1]) hp) exit_b1 hwf1 nofun
    (hpc2.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.CommitStack.b0_next)) hm2 fun st2 hm3 hpc3 => ?_
  obtain ⟨hmid1, hmem1⟩ := ok_b1
  simp only [PcOk] at hpc3
  -- The common end: memory changed only in the stack.
  have hfin : ∀ {d : MachineData}, d.dmem = st1.data.dmem →
      NativeRustcVm.SameOutside m0.dmem d.dmem (fun q ↦ NativeRustcVm.InRange t tstateBytes q ∨
        NativeRustcVm.InRange (stackBelow m0 commitStackStack) commitStackStack q) :=
    fun hd q hq ↦ by rw [hd]; exact hso1 q fun h ↦ hq (.inr h)
  by_cases hadm : Whir.Admissible (reg m0 .rsi).toNat (reg m0 .rdx).toNat
  · -- Inside the window: the count, level `0`, the tail call.
    have hb := admissible_iff.mp hadm
    rw [ladder_eq hadm] at hL
    obtain ⟨htag, -, hcnt, hlev⟩ := hL
    have hl16 : (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0).load 0 16 4 =
        BitVec.ofNat 64 (1 : UInt64).toNat := load4_of_tag (Or.inr rfl) htag
    have hc1 : (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not.eval
        (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0) = false := by
      simp only [SBool.eval, Sym.eval, hl16]; decide
    rw [hc1] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    refine exec_at (infix_of b2_in_code (by simp [b2]) hp) exit_b2 hwf1 nofun
      (hpc3.trans (by rw [Nat.add_assoc]; exact congrArg (fun j ↦ Host.addrOf (k + j)) NativeRustcVmX64.Vm.CommitStack.b1_next)) hm3 fun st3 hm4 hpc4 => ?_
    have hn3 := nOf_le (reg m0 .rsi).toNat
    rw [length_ladderW] at hcnt
    have hl168 : (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0).load 0 168 8 =
        BitVec.ofNat 64 (nOf (reg m0 .rsi).toNat) := by
      rw [off_off] at hcnt; exact load_ofMachine (o := 168) rfl hcnt
    have hc2 : (SBool.cmp .ult .W64 (.bin .add .W64 (.lit 18446744073709551609) (.load 0 168 8))
        (.lit 18446744073709551610)).not.eval (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0) =
        true := by
      simp only [SBool.eval, Sym.eval, hl168]; exact count_ok _ hn3.1 hn3.2
    simp only [PcOk] at hpc4
    rw [hc2] at hpc4
    simp (config := { decide := true }) only [↓reduceIte] at hpc4
    rw [hp.label NativeRustcVmX64.Vm.CommitStack.label_3_at] at hpc4
    refine exec_at (infix_of b4_in_code (by simp [b4]) hp) exit_b4 hwf1 nofun
      hpc4 hm4 fun st4 hm5 hpc5 => ?_
    obtain ⟨hld, hko, hrsp4, hmem4, hrdi, hrsi, hrdx⟩ := end_b4
    obtain ⟨hsv4, hsp4⟩ := tail_restored hf1 hwf1 hm5 hld hko hrsp4
    have hd4 : st4.data.dmem = st1.data.dmem := hm5.dmem_eq hwf1 hmem4
    simp only [PcOk] at hpc5
    -- Level `0`: fold `6`, rate `r`.
    have hz : 0 < (ladderW (reg m0 .rsi).toNat (reg m0 .rdx).toNat).length := by
      rw [length_ladderW]; omega
    obtain ⟨-, -, -, hw⟩ := hlev 0 hz
    have hl0 : (ladderW (reg m0 .rsi).toNat (reg m0 .rdx).toNat)[0] =
        ⟨6, (reg m0 .rdx).toNat, qAt (reg m0 .rsi).toNat (reg m0 .rdx).toNat 0⟩ := by
      simp [ladderW, foldAt]
    rw [hl0, wordsAt_cons, wordsAt_cons] at hw
    obtain ⟨hwf, hwr, -⟩ := hw
    have e24 : off (off (off fb 16) 8) (NativeRustcVm.Whir.levelBytes * 0) = off fb 24 := by
      rw [off_off, off_off, show 16 + (8 + NativeRustcVm.Whir.levelBytes * 0) = 24 from rfl]
    rw [e24] at hwf hwr
    rw [off_off] at hwr
    have hlf : (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0).load 0 24 8 = BitVec.ofNat 64 6 :=
      load_ofMachine (o := 24) rfl hwf
    have hlr : (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0).load 0 32 8 =
        BitVec.ofNat 64 (reg m0 .rdx).toNat := load_ofMachine (o := 32) rfl hwr
    have hy7 : reg st4.data .rdi = t := (hm5.regs .rdi _ hrdi).trans hY3
    have hy6 : (reg st4.data .rsi).toNat = (reg m0 .rsi).toNat - 6 + (reg m0 .rdx).toNat := by
      rw [show reg st4.data .rsi = _ from hm5.regs .rsi _ hrsi]
      simp only [heightSym, Sym.eval, SBool.eval, hlf, hlr, Env.ofMachine_regs]
      rw [show st1.data.regs.get64 .r14 = reg m0 .rsi from hY14]
      exact height_eq _ _ (by omega) (by omega)
    have hy2 : (reg st4.data .rdx).toNat = 64 := by
      rw [show reg st4.data .rdx = _ from hm5.regs .rdx _ hrdx]
      simp only [Sym.eval, hlf]
      decide
    -- `read_commitment`'s precondition, from the entry's RSP.
    have hsp4' : rspOf st4.data = stackBelow m0 0 := by
      rw [hsp4]; unfold stackBelow; simp
    have hso4 : NativeRustcVm.SameOutside m0.dmem st4.data.dmem
        (NativeRustcVm.InRange (stackBelow m0 704) 704) := by rw [hd4]; exact hso1
    have hpre4 : ReadCommitmentPre a s st4.data := by
      show StackOk _ 704 ∧ RcAt _ 704 ∧ TStateAt _ (reg st4.data .rdi) a s ∧
        TStateOk _ (reg st4.data .rdi) a 704 ∧ _
      rw [hy7]
      refine ⟨stackOk_callee hst hsv4.2 hsp4' (by decide),
        RcAt.callee hrc (rc_keep hso4 hrcOut) hsp4' hn (by decide),
        hts.frame hsv4.2 hRS hso4, TStateOk.callee htok hsp4' hn (by decide), hroots, ?_⟩
      apply got_callee hgot
        (got_keep hgot hst (writes := []) (by simp) (by simp)
          (hso4.mono (by intro q hq; exact Or.inr hq)))
        hsp4' hn (by decide)
      intro l hl a' ha
      exact (hgot.1 l hl).2.2.2 a' ha
    have hret4 : retOf st4.data = retOf m0 := retOf_eq hf1 hd4 hsp4
    have hsb4 : stackBelow st4.data 704 = stackBelow m0 704 := by
      unfold stackBelow; rw [hsp4]
    refine Eventually.mono (Spec.apply (hrcm a s) hpc5 hpre4)
      fun st5 ⟨hpc6, hrsp6, hok, hnext, hso6, hsv6⟩ ↦ ⟨hpc6.trans hret4, hrsp6.trans (by rw [hsp4]),
        ?_, ?_, ?_, hsv4.trans hsv6⟩
    · rw [hy6, hy2] at hok
      rw [run_some hadm]; exact hok
    · rw [hy7, hy6, hy2] at hnext
      rw [run_some hadm]; exact hnext
    · intro q hq
      rw [hso6 q fun h ↦ hq (h.elim (fun h' ↦ .inl (by rw [hy7] at h'; exact h'))
        fun h' ↦ .inr (by rw [stack_eq, ← hsb4]; exact h'))]
      exact hso4 q fun h ↦ hq (.inr (by rw [stack_eq]; exact h))
  · -- Outside the window: `None`, `b3` returns `0`.
    rw [ladder_none hadm] at hL
    have hl16 : (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0).load 0 16 4 =
        BitVec.ofNat 64 (0 : UInt64).toNat := load4_of_tag (Or.inl rfl) hL
    have hc1 : (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not.eval
        (frameEnv m0 st1.data 192 [] (fun _ ↦ 0) 0) = true := by
      simp only [SBool.eval, Sym.eval, hl16]; decide
    rw [hc1] at hpc3
    simp (config := { decide := true }) only [↓reduceIte] at hpc3
    rw [hp.label NativeRustcVmX64.Vm.CommitStack.label_2_at] at hpc3
    refine exec_at (infix_of b3_in_code (by simp [b3]) hp) exit_b3 hwf1 nofun hpc3 hm3
      fun st3 hm4 hpc4 => ?_
    obtain ⟨hepi, hmem3, hrax3⟩ := end_b3
    obtain ⟨hsv3, hrsp3⟩ := Frame.epilogue hf1 hwf1 hm4 hepi
    have hd3 : st3.data.dmem = st1.data.dmem := hm4.dmem_eq hwf1 hmem3
    simp only [PcOk] at hpc4
    refine .done _ ⟨by rw [hpc4]; exact hf1.load_ret hst (by decide), hrsp3, ?_, ?_, hfin hd3,
      hsv3⟩
    · show (reg st3.data .rax).toNat % 256 = (okWord ((commitStack _ _).run s).isSome).toNat
      rw [run_none hadm, show reg st3.data .rax = _ from hm4.regs .rax _ hrax3]; rfl
    · intro x s' h; rw [run_none hadm] at h; cases h

end

end NativeRustcVmX64.Layout.CommitStack
