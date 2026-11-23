module

public import NativeRustcVmX64.Whir.FoldRounds.Exec
public import NativeRustcVmX64.Whir.TFrame
public import NativeRustcVmX64.Whir.State
public import NativeRustcVmX64.Whir.SampleQueries.Basic
public import NativeRustcVm.Whir.Fold

/-!
# `fold_rounds` on x86-64: the model, the frame, the invariant

The model: `foldRounds` one round more (`foldRounds_succ`), rejecting from a rejected round on
(`foldRounds_none_of`), a round's `α` pushed (`foldRound_alphas`); the buffer of rounds kept and
pushed (`bufRoundsAt_agree`, `bufRoundsAt_push`). (The AArch64 proof's, restated here.)

`fold_rounds` keeps a 160-byte frame (`fb m0`), the `TState` at RDI (`tA`), `n` in RSI, WHIR's
state at RDX (`pA`), the buffer at RCX (`rA`); its outputs `outs` (`ctx`: the `TCtx`). `Inv i o`:
after `i` rounds, RSP at the frame's offset `o`, the registers (`r12` to `r15` the arguments, BL
`1`, RBP the output's `α` after a round), `foldRounds i`'s state, rounds and transcript in memory.
`callPre`: `fold_round`'s precondition at a call. The tag tests (`tag8_*`, `tag32_*`) and the
rounds' count test (`cnt_eq`) evaluated; a store's writes (`storeR`, `store_written`).
-/

namespace NativeRustcVmX64.Whir.FoldRounds

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRounds
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVm (WordAt EWAt EWsAt)

/-! ## The model -/

public section

theorem foldRounds_succ (n : Nat) (w : WhirStateW) (s : TState) :
    (foldRounds (n + 1) w).run s = ((foldRounds n w).run s).bind fun p ↦
      ((foldRound p.1.1).run p.2).map fun q ↦ ((q.1.1, p.1.2.push q.1.2), q.2) := by
  unfold foldRounds
  rw [List.range_succ, List.foldlM_append, StateT.run_bind]
  show Option.bind _ _ = Option.bind _ _
  congr 1
  funext p
  rcases hm : (foldRound p.1.1).run p.2 with _ | ⟨⟨w', r⟩, s'⟩ <;>
    simp [List.foldlM_cons, List.foldlM_nil, hm]

theorem foldRounds_none_of {i : Nat} {w w' : WhirStateW} {rs : Array FoldRoundW} {s s' : TState}
    (h : (foldRounds i w).run s = some ((w', rs), s')) (hm : (foldRound w').run s' = none) :
    ∀ n, i < n → (foldRounds n w).run s = none := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rw [foldRounds_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · rw [ih hlt]; rfl
    · subst heq
      rw [h]
      show ((foldRound w').run s').map _ = none
      rw [hm]; rfl

theorem foldRounds_some {i : Nat} {w w' w'' : WhirStateW} {rs : Array FoldRoundW} {r : FoldRoundW}
    {s s' s'' : TState} (h : (foldRounds i w).run s = some ((w', rs), s'))
    (hm : (foldRound w').run s' = some ((w'', r), s'')) :
    (foldRounds (i + 1) w).run s = some ((w'', rs.push r), s'') := by
  rw [foldRounds_succ, h]
  show ((foldRound w').run s').map _ = _
  rw [hm]; rfl

theorem foldRound_alphas {w w' : WhirStateW} {r : FoldRoundW} {s s' : TState}
    (h : (foldRound w).run s = some ((w', r), s')) : w'.alphas.size = w.alphas.size + 1 := by
  rw [foldRound_run] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h⟩ := h
  cases h
  simp [foldW]

theorem length_roundEWs (rs : List FoldRoundW) : (roundEWs rs).length = 2 * rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [roundEWs, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢; omega

/-- **The buffer kept.** -/
theorem bufRoundsAt_agree {d d' : Mem 64} {r : BitVec 64} {rs : List FoldRoundW}
    (h : BufRoundsAt d r rs) (hA : Agree d d' r 200 (fun _ ↦ False)) : BufRoundsAt d' r rs := by
  obtain ⟨hl, hw, he⟩ := h
  have h0 := agree_sub hA (o := 0) (k := 8) (by omega) fun _ _ ↦ id
  rw [off_zero] at h0
  refine ⟨hl, wordAt_of_agree h0 le_rfl hw,
    bytesAt_of_agree (agree_sub hA (o := 8) (k := 192) (by omega) fun _ _ ↦ id) ?_ he⟩
  rw [NativeRustcVm.length_ewsBytes, length_roundEWs]
  unfold roundCap at hl
  omega

/-- **A round pushed** on the buffer. -/
theorem bufRoundsAt_push {d d' : Mem 64} {r : BitVec 64} {rs : List FoldRoundW}
    (h : BufRoundsAt d r rs) (hlt : rs.length < roundCap)
    (hA : Agree d d' r 200 (fun j ↦ j < 8 ∨ (8 + 32 * rs.length ≤ j ∧ j < 40 + 32 * rs.length)))
    (hn : WordAt d' r (rs.length + 1).toUInt64) {ρ : FoldRoundW}
    (hx : EWsAt d' (off r (8 + 32 * rs.length)) [ρ.alpha, ρ.beta]) :
    BufRoundsAt d' r (rs ++ [ρ]) := by
  obtain ⟨-, -, he⟩ := h
  unfold roundCap at hlt
  refine ⟨by simp [roundCap]; omega, by simpa using hn, ?_⟩
  unfold RoundsAt
  rw [show roundEWs (rs ++ [ρ]) = roundEWs rs ++ [ρ.alpha, ρ.beta] by simp [roundEWs],
    NativeRustcVm.ewsAt_append_iff]
  refine ⟨bytesAt_of_agree (agree_sub hA (o := 8) (k := 32 * rs.length) (by omega)
    fun j hj hw ↦ by omega) ?_ he, ?_⟩
  · rw [NativeRustcVm.length_ewsBytes, length_roundEWs]; omega
  · rw [length_roundEWs, off_add, show 8 + 16 * (2 * rs.length) = 8 + 32 * rs.length by omega]
    exact hx

/-- `movl %ebx, %eax`: AL is BL. -/
theorem trunc32_low8 (x : BitVec 64) : (UnOp.apply .trunc .W32 x).toNat % 256 = x.toNat % 256 := by
  simp only [UnOp.apply, ext, BitVec.toNat_setWidth, toNat_low]
  show x.toNat % 2 ^ 32 % 2 ^ 64 % 256 = x.toNat % 256
  omega

end

/-! ## The frame and the invariant -/

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- WHIR's state. -/
abbrev pA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The buffer of rounds. -/
abbrev rA (m0 : MachineData) : BitVec 64 := reg m0 .rcx
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 160

/-- What the function may change but its stack: the buffer, the state, the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (rA m0) 200 q ∨ InRange (pA m0) stateBytes q ∨ InRange (tA m0) tstateBytes q

/-- Memory changed only in the outputs and the stack. -/
abbrev Sm (m0 d : MachineData) : Prop :=
  SameOutside m0.dmem d.dmem (fun q ↦ outs m0 q ∨ InRange (stackBelow m0 foldRoundsStack)
    foldRoundsStack q)

/-- What `i` rounds leave: `foldRounds i`'s state, rounds and transcript. -/
abbrev Run (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData) (i : Nat)
    (d : Mem 64) : Prop :=
  ∃ w' rs s', (foldRounds i w).run s = some ((w', rs), s') ∧ rs.size = i ∧
    w'.alphas.size = w.alphas.size + i ∧ WhirStateAt d (pA m0) w' ∧
    BufRoundsAt d (rA m0) rs.toList ∧ TStateAt d (tA m0) a s'

/-- **After `i` rounds**, RSP at the frame's offset `o`. -/
structure Inv (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData) (i o : Nat)
    (d : MachineData) : Prop where
  fr : Frame m0 160 slots o d
  same : Sm m0 d
  r12 : reg d .r12 = rA m0
  r13 : reg d .r13 = reg m0 .rsi
  r14 : reg d .r14 = pA m0
  r15 : reg d .r15 = tA m0
  rbx : (reg d .rbx).toNat % 256 = 1
  rbp : 0 < i → reg d .rbp = off (fb m0) 48
  run : Run a s w m0 i d.dmem

/-- `fold_rounds`' postcondition, reached. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ FoldRoundsPost a s w m0 st.data

end

public section

theorem stack_eq : foldRoundsStack = 160 + foldRoundStack := rfl
theorem F_le : 160 ≤ foldRoundsStack := by rw [stack_eq]; omega
theorem call_le : 160 + foldRoundStack ≤ foldRoundsStack := by rw [stack_eq]
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 160 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_112 : ∀ p ∈ slots, 112 ≤ p.1 := by decide
theorem rb_eq : 8 + roundBytes * roundCap = 200 := rfl

variable [Host] {k : Nat}

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

end

/-! ## The precondition's parts and the context -/

public section

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

theorem pre_S (h : FoldRoundsPre a s w m0) : StackOk m0 foldRoundsStack := h.1.1
theorem pre_rc (h : FoldRoundsPre a s w m0) : RcAt m0 foldRoundsStack := h.1.2.1
theorem pre_ro (h : FoldRoundsPre a s w m0) : RodataAt m0 foldRoundsStack := h.1.2.2.1
theorem pre_tok (h : FoldRoundsPre a s w m0) : TStateOk m0 (tA m0) a foldRoundsStack :=
  h.1.2.2.2.1
theorem pre_trt (h : FoldRoundsPre a s w m0) : RodataApart (tA m0) tstateBytes := h.1.2.2.2.2
theorem pre_ts (h : FoldRoundsPre a s w m0) : TStateAt m0.dmem (tA m0) a s := h.2.1
theorem pre_ws (h : FoldRoundsPre a s w m0) : WhirStateAt m0.dmem (pA m0) w := h.2.2.1
theorem pre_n6 (h : FoldRoundsPre a s w m0) : (reg m0 .rsi).toNat ≤ 6 := h.2.2.2.1
theorem pre_al (h : FoldRoundsPre a s w m0) : w.alphas.size + (reg m0 .rsi).toNat ≤ 30 := h.2.2.2.2.1
theorem pre_p (h : FoldRoundsPre a s w m0) :
    OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundsStack := h.2.2.2.2.2.1.1
theorem pre_pr (h : FoldRoundsPre a s w m0) : RodataApart (pA m0) stateBytes := h.2.2.2.2.2.1.2
theorem pre_r (h : FoldRoundsPre a s w m0) : OutOk m0 (tA m0) a (rA m0) 200 foldRoundsStack :=
  h.2.2.2.2.2.2.1.1
theorem pre_rr (h : FoldRoundsPre a s w m0) : RodataApart (rA m0) 200 := h.2.2.2.2.2.2.1.2
theorem pre_rp (h : FoldRoundsPre a s w m0) : Apart (rA m0) 200 (pA m0) stateBytes :=
  h.2.2.2.2.2.2.2.1

theorem ctx (h : FoldRoundsPre a s w m0) :
    TCtx m0 160 foldRoundsStack (tA m0) a (outs m0) := by
  have hS := pre_S h
  have hrc := pre_rc h
  have htok := pre_tok h
  have hfp := (pre_ts h).footprint
  have ho := pre_r h
  have hp := pre_p h
  have hfnw := Transcript.frame_noWrap hS F_le
  have hn : foldRoundsStack ≤ (rspOf m0).toNat := hS.1
  have hg := h.2.2.2.2.2.2.2.2
  refine ⟨hS, hrc, htok, hfp, F_le, fun q hq ↦ .inr (.inr hq), ?_, ?_, ?_, ?_, ?_⟩
  · rintro q (hq | hq | hq) hr
    · exact not_inRange_of_apart (Transcript.Apart.symm' ho.2.2.2.2.2) hrc.2.1 ho.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' hp.2.2.2.2.2) hrc.2.1 hp.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' htok.2.2) hrc.2.1 hfp.1.2 hr hq
  · rintro q (hq | hq | hq) hr
    · exact not_inRange_of_apart (Transcript.Apart.symm' ho.2.2.2.1) hfp.2.1.2 ho.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' hp.2.2.2.1) hfp.2.1.2 hp.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' hfp.2.2) hfp.2.1.2 hfp.1.2 hr hq
  · rintro q (hq | hq | hq) hr
    · exact not_inRange_of_apart (Transcript.Apart.symm' (Transcript.apart_frame ho.2.2.2.2.1 hn
        F_le)) hfnw ho.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' (Transcript.apart_frame hp.2.2.2.2.1 hn
        F_le)) hfnw hp.2.1 hr hq
    · exact not_inRange_of_apart (Transcript.Apart.symm' (Transcript.apart_frame htok.1 hn F_le))
        hfnw hfp.1.2 hr hq
  · apply hg.areas
    intro ar har
    simp only [List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl
    · simp
    · simp
    · exact List.mem_append_right _ rc_mem_rodata
  · intro d hs
    have hg' := hg.areas (areas' := [(rA m0, 200), (pA m0, stateBytes), (tA m0, tstateBytes)])
      (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har
          rcases har with rfl | rfl | rfl <;>
            simp [rA, pA, tA, roundBytes, roundCap])
    apply hg'.unchanged hS ?_ ?_ "memcpy" (by simp)
    · intro ar har
      simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl
      · exact noWrap_iff.mpr ho.2.1
      · exact noWrap_iff.mpr hp.2.1
      · exact noWrap_iff.mpr hfp.1.2
    · intro q hnot
      apply hs q
      intro hq
      apply hnot
      rcases hq with (hq | hq | hq) | hq
      · exact .inr ⟨(rA m0, 200), List.mem_cons_self, hq⟩
      · exact .inr ⟨(pA m0, stateBytes), List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
      · exact .inr ⟨(tA m0, tstateBytes),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hq⟩
      · exact .inl hq

/-- The frame's base as a number. -/
theorem fb_toNat (h : FoldRoundsPre a s w m0) : (fb m0).toNat = (rspOf m0).toNat - 160 :=
  stackBelow_toNat (by have := (pre_S h).1; have := F_le; omega)

/-- An area apart from the stack is apart from the frame's `40` bytes at `40`. -/
theorem out_apart (h : FoldRoundsPre a s w m0) {x : BitVec 64} {n : Nat}
    (hA : NativeRustcVm.Apart x n (stackBelow m0 foldRoundsStack) (foldRoundsStack + 8)) :
    NativeRustcVm.Apart (off (fb m0) 40) 40 x n := by
  show NativeRustcVm.Apart (off (stackBelow m0 160) 40) 40 x n
  have hS := pre_S h
  have h1 := Transcript.apart_frame hA hS.1 F_le
  have hfnw := Transcript.frame_noWrap hS F_le
  unfold NativeRustcVm.NoWrap at hfnw
  refine Transcript.Apart.symm' (Transcript.Apart.sub h1 ?_ ?_) <;>
    rw [toNat_off (by omega)] <;> omega

/-- The rodata items are apart from the outputs. -/
theorem ro_not_outs (h : FoldRoundsPre a s w m0) (t : NativeRustcVm.Data.Item) {q : BitVec 64}
    (hq : outs m0 q) : ¬ InRange (rodataAddr t) t.bytes.length q := by
  have hro := pre_ro h
  rcases hq with hq | hq | hq
  · exact NativeRustcVm.Apart.not_inRange (pre_rr h t) (pre_r h).2.1 (hro.noWrap t) hq
  · exact NativeRustcVm.Apart.not_inRange (pre_pr h t) (pre_p h).2.1 (hro.noWrap t) hq
  · exact NativeRustcVm.Apart.not_inRange (pre_trt h t) (pre_ts h).footprint.1.2 (hro.noWrap t) hq

/-- The read-only data for `fold_round`. -/
theorem rodataAt_call (h : FoldRoundsPre a s w m0) {d : MachineData} (hs : Sm m0 d)
    (hsp : rspOf d = stackBelow m0 160) : RodataAt d foldRoundStack := by
  have hro := pre_ro h
  intro t
  refine ⟨(hro.bytesAt t).of_sameOutside hs fun i hi hq ↦ ?_, hro.noWrap t,
    Transcript.apart_callee (hro.apart t) hsp (pre_S h).1 call_le⟩
  have hin : InRange (rodataAddr t) t.bytes.length (rodataAddr t + BitVec.ofNat 64 i) :=
    NativeRustcVm.inRange_add hi (by have := hro.noWrap t; unfold NativeRustcVm.NoWrap at this; omega)
  rcases hq with hq | hq
  · exact ro_not_outs h t hq hin
  · exact NativeRustcVm.Apart.not_inRange (hro.apart t) (hro.noWrap t) (noWrap_stackBelow (pre_S h))
      hin (Transcript.inRange_mono hq (by omega))

end

section
variable [Host] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

/-- **`fold_round`'s precondition** at a call: the frame with RSP at its base, the `i`-th round's
state and transcript, RDI the output in the frame, RSI the `TState`, RDX the state. -/
theorem callPre (h : FoldRoundsPre a s w m0) {d : MachineData} {i : Nat} {s1 : TState}
    {w1 : WhirStateW} (hf : Frame m0 160 slots 0 d) (hs : Sm m0 d) (hi : i < (reg m0 .rsi).toNat)
    (hal : w1.alphas.size = w.alphas.size + i) (hts : TStateAt d.dmem (tA m0) a s1)
    (hws : WhirStateAt d.dmem (pA m0) w1) (hdi : reg d .rdi = off (fb m0) 40)
    (hsi : reg d .rsi = tA m0) (hdx : reg d .rdx = pA m0) : FoldRoundPre a s1 w1 d := by
  have c := ctx h
  have hsp : rspOf d = stackBelow m0 160 := by rw [hf.sp, off_zero]
  have hp := pre_p h
  have hal' := pre_al h
  unfold FoldRoundPre
  rw [hsi, hdx, hdi]
  refine ⟨⟨c.stackOk hf.kept hsp call_le, c.rcAt hs hsp call_le, rodataAt_call h hs hsp,
    c.tstateOk hsp call_le, pre_trt h⟩, hts, hws, by unfold stackCap; omega,
    ⟨⟨Mapped.keeps hp.1 hf.kept, hp.2.1, hp.2.2.1, hp.2.2.2.1,
      Transcript.apart_callee hp.2.2.2.2.1 hsp c.hN call_le, hp.2.2.2.2.2⟩, pre_pr h⟩,
    ⟨c.localOk hf.kept hsp call_le (by omega) (by omega),
      fun t ↦ out_apart h ((pre_ro h).apart t)⟩, out_apart h hp.2.2.2.2.1, ?_⟩
  have hg := h.2.2.2.2.2.2.2.2
  have hn := c.hN
  have h8 := c.h8
  have hle := call_le
  have hfb := fb_toNat h
  have hsb := stackBelow_toNat hn
  have hd : (stackBelow d foldRoundStack).toNat =
      (rspOf m0).toNat - 160 - foldRoundStack := by
    rw [stackBelow_toNat (by
      rw [hsp]
      change foldRoundStack ≤ (fb m0).toNat
      rw [hfb]
      omega), hsp]
    change (fb m0).toNat - foldRoundStack = _
    rw [hfb]
  apply NativeRustcVmX64.GotAt.callee hg _ _ _ _
  · intro l hl j hj
    simp only [List.mem_singleton] at hl
    subst l
    exact c.got_keep d hs j hj
  · rw [hsb, hd]; omega
  · rw [hsb, hd]; omega
  · intro ar har
    rcases List.mem_append.mp har with har | har
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at har
      rcases har with rfl | rfl | rfl | rfl
      · exact ⟨(tA m0, tstateBytes), by simp [tA], le_rfl, le_rfl⟩
      · exact ⟨(a.words, 8 * a.len), by simp, le_rfl, le_rfl⟩
      · exact ⟨(pA m0, stateBytes), by simp [pA], le_rfl, le_rfl⟩
      · refine ⟨(stackBelow m0 foldRoundsStack, foldRoundsStack + 8), by simp, ?_, ?_⟩ <;>
          rw [hsb, toNat_off (by rw [hfb]; omega), hfb] <;> omega
    · exact ⟨ar, by simp [har], le_rfl, le_rfl⟩

omit [Host] in
/-- The changes in the outputs and the stack, as `ChangesIn`. -/
theorem changes {d : MachineData} (hs : Sm m0 d) :
    ChangesIn m0 d foldRoundsStack
      [⟨rA m0, 8 + roundBytes * roundCap⟩, ⟨pA m0, stateBytes⟩, ⟨tA m0, tstateBytes⟩] := by
  intro q hq
  refine hs q fun h ↦ hq ?_
  rcases h with (h | h | h) | h
  · exact .inl ⟨_, List.mem_cons_self .., h⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), h⟩
  · exact .inr h

end

end

end NativeRustcVmX64.Whir.FoldRounds
