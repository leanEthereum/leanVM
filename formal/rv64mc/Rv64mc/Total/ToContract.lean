/-
  Rv64mc.Total.ToContract

  A total contract gives the partial one with the same pre- and postcondition, for any instruction set, when the
  total one's context can trap at every external call and the function never ends the run (its stopping set is
  empty where the precondition holds). Written against machine-checked's `lprog` package only, in its namespaces, so
  that it can move there unchanged.

  The partial contract may be over any context `c'`. A total run never passes an external call: there the step under
  `c` may trap, which `Ascent.Total` excludes, and it may not end there either, since it ends only returned or in its
  stopping set. Away from an external call a step does not depend on the context but for its events
  (`Isa.step_of_not_ext`), so every run under `c'` from the entry is one the total judgement covers, and the partial
  judgement holds of it for every budget (`Total.safeN_append`, under any caller's stack).

  ## Main results

  * `Isa.step_of_not_ext`: a step away from an external call, in another context
  * `Total.safeN_append`: a total run is safe under a longer stack, in another context
  * `Isa.TContract.contract`: a total contract with no stopping state gives the partial one
-/

import Rv64mc.Total.Combine

namespace Lprog

namespace Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E E' : Type} {c : Context I E} {c' : Context I E'}

/-- An outcome with its events dropped. -/
def Outcome.forget : Ascent.Outcome (State I × List E') → Ascent.Outcome (State I × List E)
  | .ok (t, _) => .ok (t, [])
  | .trap => .trap
  | .wrong => .wrong

/-- **A step away from an external call is a step in any context**, with no events. -/
theorem step_of_not_ext {s : State I} (hne : ∀ k, I.fetch p s ≠ some (.Lext k))
    {o : Ascent.Outcome (State I × List E')} (h : I.step p c' s o) : I.step p c s (Outcome.forget o) := by
  obtain ⟨_ | ⟨fr, st⟩, regs, m⟩ := s
  · exact h.elim
  cases hf : p[fr.fn]? with
  | none => simp only [Isa.step, hf] at h ⊢; subst h; rfl
  | some fd =>
    cases hi : fd.body[fr.pc]? with
    | none => simp only [Isa.step, hf, hi] at h ⊢; subst h; rfl
    | some i =>
      rw [SafeN.step_eq hf hi] at h ⊢
      cases i
      case Lext k => exact absurd (SafeN.fetch_eq hf hi) (hne k)
      all_goals simp only [Isa.stepI] at h ⊢; (repeat' split at h) <;> subst h <;> simp_all [Outcome.forget]

/-- A state at an external call that may trap under `c` traps under `c`. -/
theorem step_trap_of_ext {s : State I} (hc : ∀ k regs m, c.ext k regs m .trap) {k : Nat}
    (h : I.fetch p s = some (.Lext k)) : I.step p c s .trap := by
  obtain ⟨_ | ⟨fr, st⟩, regs, m⟩ := s
  · cases h
  simp only [Isa.fetch] at h
  cases hf : p[fr.fn]? with
  | none => simp [hf] at h
  | some fd =>
    rw [hf, Option.bind_some] at h
    rw [SafeN.step_eq hf h]
    exact hc k regs m

end Isa

namespace Total

open Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E E' : Type} {c : Context I E} {c' : Context I E'}

/-- **A total run is safe under a longer stack, in another context**: a run from `s` total under `c`, whose
    external calls may all trap, ending only returned, is safe under `c'` within a budget from `s` with `rest`
    appended, if every state it returns to `rest` in is. -/
theorem safeN_append (hc : ∀ k regs m, c.ext k regs m .trap) {G Q G' Q' : State I → Prop} {rest : List Frame}
    {n : Nat} (hQ : ∀ s, I.accept p c s → Q s → s.stack = [])
    (hret : ∀ regs m, Q ⟨[], regs, m⟩ → I.SafeN p c' G' n Q' ⟨rest, regs, m⟩)
    {s : State I} (h : I.Total p c G Q s) : ∀ k ≤ n, I.SafeN p c' G' k Q' (s.append rest) := by
  induction h with
  | @done s _ ha hq =>
    obtain ⟨stk, regs, m⟩ := s
    obtain rfl : stk = [] := hQ _ ha hq
    exact fun k hk => Ascent.SafeN.mono hk (hret regs m hq)
  | @next s _ ht hw hex _ ih =>
    obtain ⟨_ | ⟨fr, st⟩, regs, m⟩ := s
    · obtain ⟨_, _, ⟨⟩⟩ := hex
    have hne : ∀ k, I.fetch p ⟨fr :: st, regs, m⟩ ≠ some (.Lext k) := fun k he =>
      ht (step_trap_of_ext hc he)
    intro k hk
    cases k with
    | zero => exact Ascent.SafeN.zero
    | succ k =>
      refine Ascent.SafeN.intro (fun ha => ?_) fun o ho => ?_
      · rcases ha with ha | ⟨k, he, -⟩
        · cases ha
        · exact absurd (by simpa [Isa.fetch, State.append] using he) (hne k)
      · cases o with
        | ok t =>
          obtain ⟨es, h'⟩ := ho
          obtain ⟨t₀, h₀, rfl⟩ := step_append_ok_inv (rest := rest) h'
          exact ih t₀ ⟨[], step_of_not_ext hne h₀⟩ k (by omega)
        | trap => trivial
        | wrong => exact hw (step_of_not_ext (o := .wrong) hne (step_append_of_not_ok nofun ho))

end Total

namespace Isa.TContract

variable {I : Isa} {p : Lprog I.Op I.Reg} {E E' : Type} {c : Context I E} {c' : Context I E'}
  {G : State I → Prop} {f : Nat} {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
  {Post Stop : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}

/-- **A total contract with no stopping state gives the partial one**, over any context, if every external call
    may trap under the total one's context and the obligation holds at a returned program. -/
theorem contract (ht : I.TContract p c G f Pre Post Stop) (hc : ∀ k regs m, c.ext k regs m .trap)
    (hG0 : ∀ regs m, G ⟨[], regs, m⟩)
    (hstop : ∀ ret top regs m r' m', Pre ret top regs m → ¬ Stop ret top regs m r' m') :
    I.Contract p c' f Pre Post := by
  intro G' n Q' ret top rest regs m hpre hk
  exact Total.safeN_append (rest := rest) hc
    (fun s _ hq => hq.elim (·.1) fun h => absurd h.2 (hstop _ _ _ _ _ _ hpre))
    (fun r' m' hq => hk r' m' (hq.resolve_right fun h => h.1 rfl).2) (ht.total hpre hG0) n (Nat.le_refl n)

end Isa.TContract

end Lprog

/-- info: 'Lprog.Isa.TContract.contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lprog.Isa.TContract.contract
