/-
  Rv64mc.Total.Combine

  A total contract and a partial one of the same function give a total contract with both
  postconditions, for any instruction set. Written against machine-checked's `lprog` package
  only, in its namespaces, so that it can move there unchanged.

  The total contract (`Isa.TContract`) says the run from the function's entry returns, or ends
  the run in its stopping set, and passes only states that step; the partial one
  (`Isa.Contract`, over a context `c'` that may differ from the total one's `c`) says every
  return satisfies its postcondition. If every step the run takes under `c` is a step under `c'`,
  every run the total judgement covers is one the partial judgement covers, so a return the total
  judgement reaches satisfies both postconditions (`TContract.and_contract`). Neither run need be
  deterministic: the partial judgement holds of every run, and the total one ranges over every
  successor.

  The proof instantiates both contracts at the one-frame stack (`TContract.total`, and the
  partial one with `Q` the postcondition at the empty stack), combines the two judgements by
  induction on the total one (`Ascent.Total.and_safeN`), and extends the one-frame run to any
  caller's stack (`Total.append`): a run from `fr :: st ++ rest` steps as the run from `fr :: st`
  until that run returns, every result of a step with `rest` appended (`Isa.step_append_ok`,
  `step_append_ok_inv`, `step_append_of_not_ok`).

  ## Main definitions

  * `State.append`

  ## Main results

  * `Ascent.Total.and_safeN`: a total judgement and a partial one along the same steps
  * `Isa.step_append_ok`, `step_append_ok_inv`, `step_append_of_not_ok`, `accept_append`: a step
    under a longer stack
  * `Isa.step_ok_of_ext_not_ok`: a context whose external calls never continue steps only where
    any other context does
  * `Total.append`: a total run under a longer stack
  * `Isa.TContract.and_contract`: a total contract and a partial one give a total contract with
    both postconditions
-/

import Rv64mc.Total.Contract
import Lprog.Contract

namespace Lprog.Ascent.Total

variable {σ : Type} {R R' : σ → Outcome σ → Prop} {accept accept' : σ → Prop} {G G' : σ → Prop}
  {Q Q' : σ → Prop}

/-- **A total judgement and a partial one along the same steps.** If every step of `R` from a
    state satisfying `G` is a step of `R'`, and `s` is safe under `R'` for every budget, the run
    the total judgement covers ends where `Q'` holds too, if `accept'` holds there. -/
theorem and_safeN {s : σ} (h : Total R accept G Q s) (hs : ∀ n, SafeN R' accept' G' n Q' s)
    (hstep : ∀ s t, G s → R s (.ok t) → R' s (.ok t)) (hG : ∀ s, G s → G' s) :
    Total R accept G (fun t => Q t ∧ (accept' t → Q' t)) s := by
  induction h with
  | done hg ha hq => exact .done hg ha ⟨hq, fun ha' => (hs 1).of_accept (hG _ hg) ha'⟩
  | next hg ht hw hex _ ih =>
    exact .next hg ht hw hex fun t hr =>
      ih t hr fun n => (hs (n + 1)).next (hG _ hg) (hstep _ _ hg hr)

end Lprog.Ascent.Total

namespace Lprog

/-- A state with `rest` appended to its stack. -/
def State.append {I : Isa} (s : State I) (rest : List Frame) : State I :=
  ⟨s.stack ++ rest, s.regs, s.m⟩

namespace Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {body : Lcmd I.Op I.Reg}
  {fr : Frame} {st rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}

/-! ## A step under a longer stack -/

theorem stepI_append_ok {i : LinstrR I.Op I.Reg} {t : State I} {es : List E}
    (h : I.stepI p c body fr st regs m i (.ok (t, es))) :
    I.stepI p c body fr (st ++ rest) regs m i (.ok (t.append rest, es)) := by
  cases i <;> simp only [Isa.stepI] at h ⊢ <;> (repeat' split at h) <;> simp_all [State.append]

theorem stepI_append_ok_inv {i : LinstrR I.Op I.Reg} {t : State I} {es : List E}
    (h : I.stepI p c body fr (st ++ rest) regs m i (.ok (t, es))) :
    ∃ t₀ : State I, I.stepI p c body fr st regs m i (.ok (t₀, es)) ∧ t = t₀.append rest := by
  obtain ⟨stk, r, m'⟩ := t
  cases i
  case Lext =>
    obtain ⟨rfl, he⟩ := h
    exact ⟨⟨_ :: st, r, m'⟩, ⟨rfl, he⟩, rfl⟩
  all_goals simp only [Isa.stepI] at h ⊢; (repeat' split at h) <;> simp_all [State.append]

theorem stepI_append_of_not_ok {i : LinstrR I.Op I.Reg} {o : Ascent.Outcome (State I × List E)}
    (ho : ∀ x, o ≠ .ok x) (h : I.stepI p c body fr (st ++ rest) regs m i o) :
    I.stepI p c body fr st regs m i o := by
  cases o with
  | ok x => exact absurd rfl (ho x)
  | _ => cases i <;> simp only [Isa.stepI] at h ⊢ <;> (repeat' split at h) <;> simp_all

/-- A step from `fr :: st` is one from `fr :: st ++ rest`, `rest` appended to its result. -/
theorem step_append_ok {t : State I} {es : List E}
    (h : I.step p c ⟨fr :: st, regs, m⟩ (.ok (t, es))) :
    I.step p c ⟨fr :: st ++ rest, regs, m⟩ (.ok (t.append rest, es)) := by
  cases hf : p[fr.fn]? with
  | none => simp [Isa.step, hf] at h
  | some fd =>
    cases hi : fd.body[fr.pc]? with
    | none => simp [Isa.step, hf, hi] at h
    | some i => exact (SafeN.step_eq hf hi _).2 (stepI_append_ok ((SafeN.step_eq hf hi _).1 h))

/-- A step from `fr :: st ++ rest` is one from `fr :: st`, with `rest` appended to its result. -/
theorem step_append_ok_inv {t : State I} {es : List E}
    (h : I.step p c ⟨fr :: st ++ rest, regs, m⟩ (.ok (t, es))) :
    ∃ t₀ : State I, I.step p c ⟨fr :: st, regs, m⟩ (.ok (t₀, es)) ∧ t = t₀.append rest := by
  cases hf : p[fr.fn]? with
  | none => simp [Isa.step, hf] at h
  | some fd =>
    cases hi : fd.body[fr.pc]? with
    | none => simp [Isa.step, hf, hi] at h
    | some i =>
      obtain ⟨t₀, h₀, rfl⟩ := stepI_append_ok_inv ((SafeN.step_eq hf hi _).1 h)
      exact ⟨t₀, (SafeN.step_eq hf hi _).2 h₀, rfl⟩

/-- A trap or `wrong` from `fr :: st ++ rest` is one from `fr :: st`. -/
theorem step_append_of_not_ok {o : Ascent.Outcome (State I × List E)} (ho : ∀ x, o ≠ .ok x)
    (h : I.step p c ⟨fr :: st ++ rest, regs, m⟩ o) : I.step p c ⟨fr :: st, regs, m⟩ o := by
  cases hf : p[fr.fn]? with
  | none => simpa [Isa.step, hf] using h
  | some fd =>
    cases hi : fd.body[fr.pc]? with
    | none => simpa [Isa.step, hf, hi] using h
    | some i =>
      exact (SafeN.step_eq hf hi _).2 (stepI_append_of_not_ok ho ((SafeN.step_eq hf hi _).1 h))

/-- A state with a nonempty stack accepts under any longer stack. -/
theorem accept_append (h : I.accept p c ⟨fr :: st, regs, m⟩) :
    I.accept p c ⟨fr :: st ++ rest, regs, m⟩ := by
  rcases h with h | ⟨n, hn, ha⟩
  · cases h
  · exact .inr ⟨n, by simpa [Isa.fetch] using hn, ha⟩

/-- **A context whose external calls never continue** steps only where any other context does:
    every instruction but an external call steps alike in every context, with no events. -/
theorem step_ok_of_ext_not_ok {E' : Type} {c' : Context I E'}
    (hc : ∀ k regs m x, ¬ c.ext k regs m (.ok x)) {s t : State I} {es : List E}
    (h : I.step p c s (.ok (t, es))) : I.step p c' s (.ok (t, [])) := by
  obtain ⟨_ | ⟨fr, rest⟩, regs, m⟩ := s
  · exact h.elim
  cases hf : p[fr.fn]? with
  | none => simp [Isa.step, hf] at h
  | some fd =>
    cases hi : fd.body[fr.pc]? with
    | none => simp [Isa.step, hf, hi] at h
    | some i =>
      have h' := (SafeN.step_eq hf hi _).1 h
      refine (SafeN.step_eq hf hi _).2 ?_
      cases i
      case Lext => exact absurd h'.2 (hc _ _ _ _)
      all_goals simp only [Isa.stepI] at h' ⊢; (repeat' split at h') <;> simp_all

end Isa

/-! ## A total run under a longer stack -/

namespace Total

open Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G Q Q' : State I → Prop}
  {rest : List Frame}

/-- **A total run under a longer stack**: a run from `s` total for `Q'` is total for `Q` from `s`
    with `rest` appended to its stack, if the obligation holds under a longer stack, the run is
    total for `Q` from wherever it returns to `rest` with `Q'`, and `Q` holds under the longer
    stack wherever it ends with a nonempty stack and `Q'`. -/
theorem append (hG : ∀ fr st regs m, G ⟨fr :: st, regs, m⟩ → G ⟨fr :: st ++ rest, regs, m⟩)
    (hret : ∀ regs m, Q' ⟨[], regs, m⟩ → I.Total p c G Q ⟨rest, regs, m⟩)
    (hstop : ∀ fr st regs m, I.accept p c ⟨fr :: st, regs, m⟩ → Q' ⟨fr :: st, regs, m⟩ →
      Q ⟨fr :: st ++ rest, regs, m⟩)
    {s : State I} (h : I.Total p c G Q' s) : I.Total p c G Q (s.append rest) := by
  induction h with
  | @done s hg ha hq =>
    obtain ⟨_ | ⟨fr, st⟩, regs, m⟩ := s
    · exact hret _ _ hq
    · exact .done (hG _ _ _ _ hg) (accept_append ha) (hstop _ _ _ _ ha hq)
  | @next s hg ht hw hex _ ih =>
    obtain ⟨_ | ⟨fr, st⟩, regs, m⟩ := s
    · obtain ⟨_, _, h⟩ := hex
      exact h.elim
    refine .next (hG _ _ _ _ hg) (fun h => ht (step_append_of_not_ok nofun h))
      (fun h => hw (step_append_of_not_ok nofun h)) ?_ fun t ⟨es, h⟩ => ?_
    · obtain ⟨t, es, h⟩ := hex
      exact ⟨t.append rest, es, step_append_ok h⟩
    · obtain ⟨t₀, h₀, rfl⟩ := step_append_ok_inv h
      exact ih t₀ ⟨es, h₀⟩

end Total

/-! ## A total contract and a partial one -/

namespace Isa.TContract

variable {I : Isa} {p : Lprog I.Op I.Reg} {E E' : Type} {c : Context I E} {c' : Context I E'}
  {G : State I → Prop} {f : Nat}
  {Pre Pre' : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
  {Post Post' Stop :
    BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}

/-- **A total contract and a partial one give a total contract with both postconditions**, under
    both preconditions. The partial contract may be over another context `c'`: every step the run
    takes under `c` from a state satisfying the obligation `G` must be a step under `c'`. `G` must
    hold at a returned program and under a longer stack, as it does for an obligation on the
    innermost activation alone. -/
theorem and_contract (ht : I.TContract p c G f Pre Post Stop) (hp : I.Contract p c' f Pre' Post')
    (hstep : ∀ s t es, G s → I.step p c s (.ok (t, es)) → ∃ es', I.step p c' s (.ok (t, es')))
    (hG0 : ∀ regs m, G ⟨[], regs, m⟩)
    (hG : ∀ fr st rest regs m, G ⟨fr :: st, regs, m⟩ → G ⟨fr :: st ++ rest, regs, m⟩) :
    I.TContract p c G f (fun ret top regs m => Pre ret top regs m ∧ Pre' ret top regs m)
      (fun ret top regs m r' m' => Post ret top regs m r' m' ∧ Post' ret top regs m r' m')
      Stop := by
  intro Q ret top rest regs m ⟨hpre, hpre'⟩ hstop hk
  have hs : ∀ n, I.SafeN p c' (fun _ => True) n
      (fun s => s.stack = [] → Post' ret top regs m s.regs s.m) ⟨[⟨f, 0, ret, top⟩], regs, m⟩ :=
    fun _ => hp.run hpre' fun _ _ hq => SafeN.returned fun _ => hq
  have h := (ht.total hpre hG0).and_safeN hs (fun s t hg ⟨es, h⟩ => hstep s t es hg h)
    fun _ _ => trivial
  refine Total.append (hG · · rest) (fun r' m' ⟨hq, hq'⟩ => ?_) (fun fr st r' m' ha ⟨hq, _⟩ => ?_) h
  · rcases hq with ⟨-, hq⟩ | ⟨hne, -⟩
    · exact hk r' m' ⟨hq, hq' (.inl rfl) rfl⟩
    · exact absurd rfl hne
  · rcases hq with ⟨hne, -⟩ | ⟨-, hq⟩
    · cases hne
    · exact hstop fr (st ++ rest) r' m' hq (accept_append ha)

end Isa.TContract

end Lprog

/-- info: 'Lprog.Isa.TContract.and_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lprog.Isa.TContract.and_contract

/-- info: 'Lprog.Total.append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lprog.Total.append

/-- info: 'Lprog.Ascent.Total.and_safeN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lprog.Ascent.Total.and_safeN

/-- info: 'Lprog.Isa.step_ok_of_ext_not_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lprog.Isa.step_ok_of_ext_not_ok
