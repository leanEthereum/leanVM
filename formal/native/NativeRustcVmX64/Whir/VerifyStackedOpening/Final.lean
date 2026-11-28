module

public import NativeRustcVmX64.Whir.VerifyStackedOpening.CallPre
public import NativeRustcVmX64.Code.Vm.WhirLevels.Names

/-!
# `verify_stacked_opening`: `whir_levels` and the return (x86-64)

`whir_b48`: `b48` writes WHIR's fresh state (the batched target, no `α`, no glued claim) into
the `WhirW`, its address as `whir_levels`' stack argument, and calls it (`AtCall`). `call_whir`:
`whir_levels`' contract, `b49`, the epilogue `b51`: the function's goal.
-/

namespace NativeRustcVmX64.Whir.VerifyStackedOpening

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript
open NativeRustcVmX64.Transcript NativeRustcVm.Whir NativeRustcVmX64.Vm.VerifyStackedOpening
open LeanVM.Parameters

public section

section
variable [Labels] {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData}

/-- **The outputs** across a step changing the stack and the `WhirW` only. -/
theorem Outs.keepP (h : Parts a s layout target coefficients point slices cs z value m0)
    {d d' : Mem 64} (ho : Outs a s layout cs m0 d) (hk : Keeps d d') {R : BitVec 64 → Prop}
    (hR : ∀ q, R q → NativeRustcVm.InRange (stackBelow m0 verifyStackedOpeningStack)
      verifyStackedOpeningStack q ∨ NativeRustcVm.InRange (pA m0) whirBytes q)
    (hs : NativeRustcVm.SameOutside d d' R) : Outs a s layout cs m0 d' := by
  have hscn := h.sc_nw
  have hsc8 := h.sc8_le (layout := layout)
  have hpn := h.p_nat.1
  have hnot : ∀ q, NativeRustcVm.InRange (scA m0) scalesBytes q → ¬ R q := fun q hq hr ↦
    (hR q hr).elim (fun h' ↦ h.outs_not_stack (.inr (.inl hq)) h')
      fun h' ↦ not_inRange_of_apart (Apart.symm' h.psc) hscn hpn hq h'
  refine ⟨h.ts_keep ho.ts hk (fun q hq ↦ (hR q hq).elim .inl fun h' ↦ .inr (.inr h')) hs,
    ?_, ?_⟩
  · refine NativeRustcVm.BytesAt.of_sameOutside ho.scw hs fun i hi ↦ hnot _ ?_
    rw [NativeRustcVm.length_wordBytes] at hi
    exact NativeRustcVm.inRange_add (by show i < 2600; omega)
      (by unfold NativeRustcVm.NoWrap at hscn; omega)
  · refine NativeRustcVm.BytesAt.of_sameOutside ho.scs hs fun i hi ↦ hnot _ ?_
    rw [NativeRustcVm.length_flatMap_const NativeRustcVm.length_ewBytes, Array.length_toList,
      size_scalesOf] at hi
    rw [off_add]
    exact inRange_off_self (by omega) (by unfold NativeRustcVm.NoWrap at hscn; omega)

end

/-- Levels in the frame across a block writing it below their offset. -/
theorem levels_keep [Labels] {m0 st st' : MachineData} {rest : List (BitVec 64 × Nat)}
    {vars : Nat → BitVec 64} {ret : BitVec 64} {S : SState}
    (hwf : (frameEnv m0 st 512 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 512 rest vars ret) S st') (hin : writesIn S = true)
    {o : Nat} (hlow : belowRet o S = true) {ls : List Whir.Level} (hlen : ls.length ≤ 6)
    (ho : o + 144 ≤ 520) (hl : LevelsAt st.dmem (win m0 o) ls) : LevelsAt st'.dmem (win m0 o) ls :=
  fun i hi ↦ by
    obtain ⟨h1, h2, h3, h4⟩ := hl i hi
    refine ⟨h1, h2, h3, ?_⟩
    have hlb : levelBytes = 24 := rfl
    rw [off_off] at h4 ⊢
    refine NativeRustcVmX64.Sumcheck.keep_frame hwf hm hin ?_ (fun w hw hr ↦ ?_) h4
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        NativeRustcVm.length_wordBytes, hlb]
      omega
    · have := belowRet_spec hlow w hw hr
      left
      omega

variable [Host] {k : Nat} {a : DecArea} {s : TState} {layout : LayoutW} {target : EW}
  {coefficients point slices : Array EW} {cs : Array ColumnClaimW} {z : Array EW} {value : EW}
  {m0 : MachineData} {ls : List Whir.Level}

/-- **WHIR's fresh state**: `b48` to the call of `whir_levels`. -/
theorem whir_b48 (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k) {st : MachineState} (hpc : st.pc = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b48Offset))
    (hA : AtB48 a s layout target cs value ls m0 st.data) {R : MachineState → Prop}
    (cont : ∀ st', AtCall a s layout target cs value ls m0 st'.data →
      st'.pc = Labels.label NativeRustcVmX64.Vm.WhirLevels.entryLabel ∧ retOf st'.data = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b49Offset) →
      Eventually (step1 Host.exe) R st') :
    Eventually (step1 Host.exe) R st := by
  have hok := hA.ok
  have hpo := h.po
  have hwf : ∀ ret, (frameEnv m0 st.data 512 [(pA m0, 512)] (fun _ ↦ 0) ret).WF := fun _ ↦
    hok.wf1 h (fun i hi ↦ hpo.1.1 i (by show i < 63200; omega))
      (by
        have hh : (pA m0).toNat + 63200 ≤ 2 ^ 64 := hpo.1.2.1
        unfold NativeRustcVm.NoWrap; omega)
      (apart_shrink hpo.1.2.2.2.2.1 (by show 512 ≤ 63200; omega) le_rfl)
  have hm : ∀ ret, Match (frameEnv m0 st.data 512 [(pA m0, 512)] (fun _ ↦ 0) ret) whirS st.data :=
    fun _ ↦ match_ofMachine ⟨rfl, rfl, trivial⟩ ⟨hok.fr.rsp_eval, trivial⟩ trivial trivial
      ⟨by show reg st.data .rax = _
          rw [hA.rax, show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl, trivial⟩
  refine h.runOut hp b48_in_code (List.cons_ne_nil _ _) hpc hok (hwf _) (hm _) run_b48 (o := 0)
    (by decide +kernel) (i := 1) rfl (fun q hq ↦ .inl (inRange_mono hq (by decide)))
    (by decide +kernel) fun st1 hok1 hs1 hm1 hpc1 ↦ ?_
  have hout1 := Outs.keepP h hA.out (hm1.kept (hwf _))
    (fun q hq ↦ hq.elim (fun h' ↦ .inl (h.frame_stack h'))
      fun h' ↦ .inr (inRange_mono h' (by decide))) hs1
  have hfw1 := FW.block_os (hwf _) hm1 rfl hA.fw
    [24, 40, 48, 56, 64, 104, 112, 120, 128, 136, 144, 152] rfl (by decide +kernel)
  have hlv1 := levels_keep (hwf _) hm1 rfl (o := 320) (by decide +kernel) hA.len (by omega) hA.lv
  -- WHIR's fresh state
  have wP : ∀ (o : Nat) (v : Sym), o + 8 ≤ 512 →
      (∀ i < 8, findWrite 1 (o + i) (after b48 whirS).mem = some (v, i)) →
      NativeRustcVm.WordAt st1.data.dmem (off (pA m0) o)
        (UInt64.ofBitVec (v.eval (frameEnv m0 st.data 512 [(pA m0, 512)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b48Offset + b48.length)).toBitVec))) := fun o v ho hw ↦
    wordAt_write hm1 (r := 1) (b := pA m0) (sz := 512) rfl ho (by rw [← after_eq run_b48]; exact hw)
  have w0 := wP 0 (.reg .r12) (by omega) (by rw [after_eq run_b48]; decide +kernel)
  have w8 := wP 8 (.reg .r13) (by omega) (by rw [after_eq run_b48]; decide +kernel)
  have w16 := wP 16 (.lit 0) (by omega) (by rw [after_eq run_b48]; decide +kernel)
  have w504 := wP 504 (.lit 0) (by omega) (by rw [after_eq run_b48]; decide +kernel)
  have hws : WhirStateAt st1.data.dmem (pA m0) ⟨claimOf s layout target cs value, #[], #[]⟩ := by
    refine ⟨?_, ⟨by show 0 ≤ 30; decide, w16, NativeRustcVm.ewsAt_nil _ _⟩,
      by show 0 ≤ 10; decide, w504, fun i hi ↦ ?_⟩
    · rw [NativeRustcVm.ewAt_iff]
      have e0 : (Sym.reg .r12).eval (frameEnv m0 st.data 512 [(pA m0, 512)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b48Offset + b48.length)).toBitVec) = _ := hA.r12
      have e1 : (Sym.reg .r13).eval (frameEnv m0 st.data 512 [(pA m0, 512)] (fun _ ↦ 0)
          (Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b48Offset + b48.length)).toBitVec) = _ := hA.r13
      rw [e0, UInt64.ofBitVec_toBitVec, off_zero] at w0
      rw [e1, UInt64.ofBitVec_toBitVec] at w8
      exact ⟨w0, w8⟩
    · exact absurd hi (by simp)
  have harg := fw_reg hm1 (o := 8) (by omega) (r := .rax) (by decide +kernel) hA.rax
  simp only [PcOk] at hpc1
  refine cont st1 ⟨hok1, hout1, hfw1, hA.lad, hA.len, hlv1, hws, harg, ?_, ?_, ?_, ?_, ?_, ?_⟩ hpc1
  · rw [show reg st1.data .rdi = _ from hm1.regs .rdi _ rfl]
    exact fw_load hA.fw (o := 24) (v := UInt64.ofBitVec (tA m0)) (by simp [fwL])
  · rw [show reg st1.data .rsi = reg st.data .r14 from hm1.regs .rsi _ rfl]; exact hA.r14
  · rw [regKeep hm1 .rdx rfl]; exact hA.rdx
  · exact (hm1.regs .rcx _ rfl).trans (eval_ptr0 104)
  · exact (hm1.regs .r8 _ rfl).trans (eval_ptr0 320)
  · rw [regKeep hm1 .r9 rfl]; exact hA.r9

/-- **From the call of `whir_levels`** to the return. -/
theorem call_whir (h : Parts a s layout target coefficients point slices cs z value m0)
    (hp : Placed code k)
    (hwl : ∀ a s levels ba b claim, Spec (Labels.label NativeRustcVmX64.Vm.WhirLevels.entryLabel)
      (WhirLevelsPre a s levels ba b claim) (WhirLevelsPost a s levels b claim))
    {st : MachineState} (hc : AtCall a s layout target cs value ls m0 st.data)
    (hpc : st.pc = Labels.label NativeRustcVmX64.Vm.WhirLevels.entryLabel ∧ retOf st.data = Host.addrOf (k + NativeRustcVmX64.Vm.VerifyStackedOpening.b49Offset)) :
    Eventually (step1 Host.exe) (Goal a s layout target coefficients point cs z value m0) st := by
  have hok := hc.ok
  have hN : 512 + whirLevelsStack ≤ verifyStackedOpeningStack := by rw [stack_eq]; decide
  have hlog : layout.stackLog < 2 ^ 64 := h.lay.stack_log_lt
  have hsp := Ok.sp hok
  have harg : stackArg st.data 0 = pA m0 := by
    unfold stackArg
    rw [show rspOf st.data + BitVec.ofNat 64 (8 + 8 * 0) = win m0 8 by rw [hsp],
      NativeRustcVm.wordOf_of_wordAt hc.arg]
  refine call_then (P := WhirLevelsPre a (sq s).2 ls (baOf layout cs m0)
      (basisOf s layout target point coefficients cs z value) (claimOf s layout target cs value))
    (Q := WhirLevelsPost a (sq s).2 ls (basisOf s layout target point coefficients cs z value)
      (claimOf s layout target cs value)) (env := frameEnv m0 st.data 512 [] (fun _ ↦ 0) 0)
    hpc (hwl _ _ _ _ _ _) (pre_of h hc) fun st2 hpc2 hrsp2 hq ↦ ?_
  obtain ⟨hal, hnext, hch, hsv⟩ := hq
  have e_rsi : (reg st.data .rsi).toNat = layout.stackLog := by rw [hc.rsi, u64n hlog]
  have hrun := run_eq h hc.lad
  have hal' : OkAl st2.data (runOf s layout target coefficients point cs z value m0).isSome := by
    rw [hrun]
    have := hal
    rw [e_rsi, hc.rdx] at this
    exact this
  have hnext' : NextAt st2.data.dmem (tA m0) a
      (runOf s layout target coefficients point cs z value m0) := by
    rw [hrun]
    have := hnext
    rw [e_rsi, hc.rdx, hc.rdi] at this
    exact this
  have hch' : NativeRustcVm.SameOutside st.data.dmem st2.data.dmem
      (fun q ↦ (NativeRustcVm.InRange (pA m0) whirBytes q ∨
        NativeRustcVm.InRange (tA m0) tstateBytes q) ∨
        NativeRustcVm.InRange (stackBelow st.data whirLevelsStack) whirLevelsStack q) := by
    refine NativeRustcVm.SameOutside.mono hch fun q hq ↦ ?_
    rcases hq with ⟨r, hr, hq⟩ | hq
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have : NativeRustcVm.InRange (stackArg st.data 0) whirBytes q := hq
        rw [harg] at this
        exact .inl (.inl this)
      · have : NativeRustcVm.InRange (reg st.data .rdi) tstateBytes q := hq
        rw [hc.rdi] at this
        exact .inl (.inr this)
    · exact .inr hq
  obtain ⟨hok2, -⟩ := hok.call h hsv hrsp2 hN
    (fun q hq ↦ hq.elim (fun h' ↦ .inl h') fun h' ↦ .inr (.inr h')) hch'
  -- `b49`, `b51`
  refine h.run hp b49_in_code (List.cons_ne_nil _ _)
    hpc2 hok2 (vars := fun _ ↦ 0) (hok2.wf0 h)
    hok2.m_reg run_b49 (o := 8) (by decide +kernel) (by decide) fun st3 hok3 _ hm3 hpc3 ↦ ?_
  simp only [PcOk] at hpc3
  rw [hp.label NativeRustcVmX64.Vm.VerifyStackedOpening.label_41_at] at hpc3
  have hd3 : st3.data.dmem = st2.data.dmem := hm3.dmem_eq (hok2.wf0 h) rfl
  refine exit_b51 h hp hpc3 hok3 ?_ (by rw [hd3]; exact hnext')
  unfold OkAl boolRet at hal' ⊢
  rw [regKeep hm3 .rax rfl]
  exact hal'

end

end NativeRustcVmX64.Whir.VerifyStackedOpening
