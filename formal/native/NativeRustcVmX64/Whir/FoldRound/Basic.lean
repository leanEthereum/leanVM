module

public import NativeRustcVmX64.Whir.FoldRound.Exec
public import NativeRustcVmX64.Whir.TFrame
public import NativeRustcVmX64.Whir.State
public import NativeRustcVmX64.Whir.SampleQueries.Basic
public import NativeRustcVm.Whir.Fold

/-!
# `fold_round` on x86-64: the frame, the outputs, the exits

`fold_round` keeps a 176-byte frame (`fb m0`), the `TState` at RSI (`tA`), WHIR's state at RDX
(`pA`), the output at RDI (`oA`); its outputs `outs` (`ctx`: the `TCtx`). Before the state's
writes (`b18`) memory changed only in the stack and the `TState` (`Pre18`); a body state there
(`Bd`): the frame, that memory, the `TState`, RBX the output, R14 the state.

`exit21`: `b21` writes the tag in RAX to the output and returns; `none20`: the `None` exit
(`b20`, `b21`).
-/

namespace NativeRustcVmX64.Whir.FoldRound

open NativeRustcX64 NativeRustcX64.Sym NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Whir
open NativeRustcVmX64.Vm.FoldRound
open NativeRustcVmX64.Transcript (Frame frameEnv MidOk)
open NativeRustcVmX64.Whir.SampleQueries (wr0 miss wrote kept wrote_spec kept_spec wr0_spec
  miss_spec midOk_writesIn)
open NativeRustcVm (WordAt EWAt EWsAt)

@[expose] public section

/-- The `TState`. -/
abbrev tA (m0 : MachineData) : BitVec 64 := reg m0 .rsi
/-- WHIR's state. -/
abbrev pA (m0 : MachineData) : BitVec 64 := reg m0 .rdx
/-- The output. -/
abbrev oA (m0 : MachineData) : BitVec 64 := reg m0 .rdi
/-- The frame's base. -/
abbrev fb (m0 : MachineData) : BitVec 64 := stackBelow m0 176

/-- What the function may change but its stack: the output, the state, the `TState`. -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (oA m0) 40 q ∨ InRange (pA m0) stateBytes q ∨ InRange (tA m0) tstateBytes q

/-- What changes before `b18`: the stack, the `TState`. -/
def Pre18 (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange (stackBelow m0 foldRoundStack) foldRoundStack q ∨ InRange (tA m0) tstateBytes q

/-- The body's states. -/
abbrev Fr (m0 d : MachineData) : Prop := WFr m0 176 foldRoundStack slots (outs m0) d

/-- **A body state before `b18`**, the `TState` `s`. -/
structure Bd (m0 : MachineData) (a : DecArea) (s : TState) (d : MachineData) : Prop where
  fr : Fr m0 d
  mem : SameOutside m0.dmem d.dmem (Pre18 m0)
  ts : TStateAt d.dmem (tA m0) a s
  rbx : reg d .rbx = oA m0
  r14 : reg d .r14 = pA m0

/-- What the round leaves at the output, the state and the `TState`. -/
def Res (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData) (d : Mem 64) : Prop :=
  match (foldRound w).run s with
  | none => WordAt d (oA m0) 0
  | some ((w', r), s') => WordAt d (oA m0) 1 ∧ EWsAt d (off (oA m0) 8) [r.alpha, r.beta] ∧
      WhirStateAt d (pA m0) w' ∧ TStateAt d (tA m0) a s'

/-- `fold_round`'s postcondition, reached. -/
abbrev Goal [Labels] (a : DecArea) (s : TState) (w : WhirStateW) (m0 : MachineData)
    (st : MachineState) : Prop :=
  st.pc = retOf m0 ∧ rspOf st.data = rspOf m0 + 8#64 ∧ FoldRoundPost a s w m0 st.data

end

public section

theorem stack_eq : foldRoundStack =
    176 + max readScalarStack (max grindStack (max squeezeStack ewMulStack)) := rfl
theorem F_le : 176 ≤ foldRoundStack := by rw [stack_eq]; omega
theorem rs_le : 176 + readScalarStack ≤ foldRoundStack := by rw [stack_eq]; omega
theorem gr_le : 176 + grindStack ≤ foldRoundStack := by rw [stack_eq]; omega
theorem sq_le : 176 + squeezeStack ≤ foldRoundStack := by rw [stack_eq]; omega
theorem mul_le : 176 + ewMulStack ≤ foldRoundStack := by rw [stack_eq]; omega
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 176 := by decide
theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide
theorem slots_32 : ∀ p ∈ slots, 8 + 24 ≤ p.1 := by decide

theorem cs_of {r : Reg64} (h : calleeSaved r = true) : r ∈ cs := by
  cases r <;> simp [calleeSaved, cs] at h ⊢

theorem wrR_spec {S : SState} {r L : Nat} (h : wrR S r L = true) :
    ∀ w ∈ S.mem, w.r = r ∧ w.off + w.n ≤ L := by
  intro w hw
  unfold wrR at h
  rw [List.all_eq_true] at h
  simpa using h w hw

theorem wr0_le {S : SState} {L : Nat} (h : wr0 S L = true) (hL : L ≤ 176) :
    ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 176 := fun w hw ↦
  have := wr0_spec h w hw
  ⟨this.1, by omega⟩

theorem missL_spec {S : SState} {os : List Nat} (h : missL S os = true) {o : Nat} (ho : o ∈ os) :
    miss S o = true := by
  unfold missL at h
  rw [List.all_eq_true] at h
  exact h o ho

theorem keptI_spec {S0 S : SState} {rs : List Reg64} (h : keptI S0 S rs = true) {r : Reg64}
    (hr : r ∈ rs) : S.reg r = S0.reg r := by
  unfold keptI at h
  rw [List.all_eq_true] at h
  have := h r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact this.2

variable [Host] {k : Nat}

theorem inf (hp : Placed code k) {b : List Directive} {j : Nat} (hb : b.IsInfixAt code j)
    (hne : b ≠ []) : b.IsInfixAt Host.prog (k + j) :=
  hb.trans hp.1 hne

end

/-! ## The context -/

public section

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}

theorem pre_o (h : FoldRoundPre a s w m0) : OutOk m0 (tA m0) a (oA m0) 40 foldRoundStack :=
  h.2.2.2.2.2.1.1
theorem pre_p (h : FoldRoundPre a s w m0) :
    OutOk m0 (tA m0) a (pA m0) stateBytes foldRoundStack := h.2.2.2.2.1.1
theorem pre_op (h : FoldRoundPre a s w m0) : Apart (oA m0) 40 (pA m0) stateBytes :=
  h.2.2.2.2.2.2.1

theorem ctx (h : FoldRoundPre a s w m0) :
    TCtx m0 176 foldRoundStack (tA m0) a (outs m0) := by
  have hS : StackOk m0 foldRoundStack := h.1.1
  have hrc : RcAt m0 foldRoundStack := h.1.2.1
  have htok : TStateOk m0 (tA m0) a foldRoundStack := h.1.2.2.2.1
  have hfp := h.2.1.footprint
  have ho := pre_o h
  have hp := pre_p h
  have hfnw := Transcript.frame_noWrap hS F_le
  have hn : foldRoundStack ≤ (rspOf m0).toNat := hS.1
  have hg := h.2.2.2.2.2.2.2
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
    have hg' := hg.areas (areas' := [(oA m0, 40), (pA m0, stateBytes), (tA m0, tstateBytes)])
      (by intro ar har; simp only [List.mem_cons, List.not_mem_nil, or_false] at har
          rcases har with rfl | rfl | rfl <;> simp [oA, pA, tA])
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
      · exact .inr ⟨(oA m0, 40), List.mem_cons_self, hq⟩
      · exact .inr ⟨(pA m0, stateBytes), List.mem_cons_of_mem _ List.mem_cons_self, hq⟩
      · exact .inr ⟨(tA m0, tstateBytes),
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), hq⟩
      · exact .inl hq

/-- What changes before `b18` misses the state and the output. -/
theorem pre18_not (h : FoldRoundPre a s w m0) {q : BitVec 64} (hq : Pre18 m0 q) :
    ¬ InRange (pA m0) stateBytes q ∧ ¬ InRange (oA m0) 40 q := by
  have hp := pre_p h
  have ho := pre_o h
  have hS : StackOk m0 foldRoundStack := h.1.1
  have hfp := h.2.1.footprint
  rcases hq with hq | hq
  · exact ⟨fun hr ↦ not_inRange_of_apart hp.2.2.2.2.1 hp.2.1 (noWrap_stackBelow hS) hr
        (Transcript.inRange_mono hq (by omega)),
      fun hr ↦ not_inRange_of_apart ho.2.2.2.2.1 ho.2.1 (noWrap_stackBelow hS) hr
        (Transcript.inRange_mono hq (by omega))⟩
  · exact ⟨fun hr ↦ not_inRange_of_apart hp.2.2.1 hp.2.1 hfp.1.2 hr hq,
      fun hr ↦ not_inRange_of_apart ho.2.2.1 ho.2.1 hfp.1.2 hr hq⟩

/-- **WHIR's state** before `b18`: the entry's. -/
theorem ws_of_mem (h : FoldRoundPre a s w m0) {d : Mem 64}
    (hs : SameOutside m0.dmem d (Pre18 m0)) : WhirStateAt d (pA m0) w :=
  WhirStateAt.agree h.2.2.1 fun j hj _ ↦ hs _ fun hq ↦
    (pre18_not h hq).1 (inRange_off_self hj (by unfold stateBytes; omega))

omit [Labels] in
/-- Memory before `b18`, across a change in `R`. -/
theorem mem_trans {d d' : Mem 64} {R : BitVec 64 → Prop} (h1 : SameOutside m0.dmem d (Pre18 m0))
    (h2 : SameOutside d d' R) (hR : ∀ q, R q → Pre18 m0 q) : SameOutside m0.dmem d' (Pre18 m0) :=
  fun q hq ↦ (h2 q fun h ↦ hq (hR q h)).trans (h1 q hq)

omit [Labels] in
/-- The changes in the outputs and the stack, as `ChangesIn`. -/
theorem changes {d : Mem 64} {m' : MachineData}
    (hs : SameOutside m0.dmem d (fun q ↦ outs m0 q ∨
      InRange (stackBelow m0 foldRoundStack) foldRoundStack q))
    (h' : SameOutside d m'.dmem (InRange (oA m0) 8)) :
    ChangesIn m0 m' foldRoundStack
      [⟨oA m0, 40⟩, ⟨pA m0, stateBytes⟩, ⟨tA m0, tstateBytes⟩] := by
  have hio : ∀ q, InRange (oA m0) 40 q → NativeRustcVm.InAny
      [⟨oA m0, 40⟩, ⟨pA m0, stateBytes⟩, ⟨tA m0, tstateBytes⟩] q :=
    fun q hq ↦ ⟨_, List.mem_cons_self .., hq⟩
  intro q hq
  refine (h' q fun h ↦ hq (.inl (hio q (Transcript.inRange_mono h (by omega))))).trans
    (hs q fun h ↦ hq ?_)
  rcases h with (h | h | h) | h
  · exact .inl (hio q h)
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), h⟩
  · exact .inl ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)), h⟩
  · exact .inr h

end

/-! ## Frame words -/

section
variable [Labels] {a : DecArea} {s : TState} {w : WhirStateW} {m0 : MachineData}
  {st st' : MachineData} {rest : List (BitVec 64 × Nat)} {vars : Nat → BitVec 64}
  {ret : BitVec 64} {S : SState}

/-- **A frame word kept** by a block whose writes miss it. -/
theorem loc_keep (hwf : (frameEnv m0 st 176 rest vars ret).WF)
    (hm : Match (frameEnv m0 st 176 rest vars ret) S st') (hin : Transcript.writesIn S = true)
    {o : Nat} (ho : o + 8 ≤ 184) (hmiss : miss S o = true) {v : UInt64}
    (h : WordAt st.dmem (off (fb m0) o) v) : WordAt st'.dmem (off (fb m0) o) v := by
  have hmi := miss_spec hmiss
  refine fun i hi ↦ ?_
  have hi' : i < 8 := by rw [NativeRustcVm.length_wordBytes] at hi; exact hi
  rw [off_add, hm.get?_mem0 hwf (Transcript.not_written0 hwf hm hin (j := o + i) (by omega)
    fun w hw hr ↦ by have := hmi w hw hr; omega), ← off_add]
  exact h i hi

/-- **A frame word a block wrote.** -/
theorem loc_write (hm : Match (frameEnv m0 st 176 rest vars ret) S st') {o : Nat}
    (ho : o + 8 ≤ 184) {v : Sym} (hw : wrote S 0 o v = true) :
    WordAt st'.dmem (off (fb m0) o) (UInt64.ofBitVec (v.eval (frameEnv m0 st 176 rest vars ret))) :=
  Transcript.wordAt_write hm (r := 0) rfl ho (wrote_spec hw)

omit [Labels] in
/-- A frame word, loaded. -/
theorem loc_load {o : Nat} {v : UInt64} (h : WordAt st.dmem (off (fb m0) o) v) :
    (frameEnv m0 st 176 rest vars ret).load 0 o 8 = v.toBitVec :=
  Transcript.load_ofMachine rfl h

omit [Labels] in
/-- A frame word kept across a change missing its bytes. -/
theorem frame_keep {d d' : Mem 64} {R : BitVec 64 → Prop} (hs : SameOutside d d' R) {o : Nat}
    (hR : ∀ i < 8, ¬ R (off (fb m0) (o + i))) {v : UInt64} (h : WordAt d (off (fb m0) o) v) :
    WordAt d' (off (fb m0) o) v := fun i hi ↦ by
  have hi' : i < 8 := by rw [NativeRustcVm.length_wordBytes] at hi; exact hi
  rw [off_add, hs _ (hR i hi'), ← off_add]
  exact h i hi

/-- A frame byte is not the callee's stack nor the `TState`'s. -/
theorem frame_not_call (h : FoldRoundPre a s w m0) {x : Nat} (hx : x < 184) :
    ¬ (InRange (stackBelow m0 foldRoundStack) foldRoundStack (off (fb m0) x) ∧
        ¬ InRange (fb m0) (176 + 8) (off (fb m0) x)) ∧
      ¬ InRange (tA m0) tstateBytes (off (fb m0) x) :=
  ⟨fun hq ↦ hq.2 (inRange_off_self hx (by omega)),
    fun ht ↦ (ctx h).ofr _ (.inr (.inr ht)) (inRange_off_self hx (by omega))⟩

end

end

end NativeRustcVmX64.Whir.FoldRound
