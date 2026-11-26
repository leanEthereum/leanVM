/-
  Rv64mc.Model.Extra.Samples

  `Model.TM.samples` read the way `samples`' loop runs it, a challenge at a time at the end: it always succeeds
  with `n` challenges (`samples_some`), and one more sample appends its challenge (`samples_snoc`).
-/

import Rv64mc.Model.Transcript

namespace Rv64mc.Model

theorem samples_run_succ (n : Nat) (t : TState) :
    (TM.samples (n + 1)).run t = ((TM.samples n).run { t with sponge := t.sponge.sample.2 }).map
      fun r => (t.sponge.sample.1 :: r.1, r.2) := by
  simp only [TM.samples, StateT.run_bind, StateT.run_pure]
  rw [show TM.sample.run t = some (t.sponge.sample.1, { t with sponge := t.sponge.sample.2 }) from rfl]
  cases h : (TM.samples n).run { t with sponge := t.sponge.sample.2 } <;> simp [h]

/-- **`samples` always succeeds**, with `n` challenges. -/
theorem samples_some : ∀ (n : Nat) (t : TState), ∃ xs t', (TM.samples n).run t = some (xs, t') ∧ xs.length = n
  | 0, t => ⟨[], t, rfl, rfl⟩
  | n + 1, t => by
    obtain ⟨xs, t', h, hl⟩ := samples_some n { t with sponge := t.sponge.sample.2 }
    exact ⟨_, t', by rw [samples_run_succ, h]; rfl, by simp [hl]⟩

/-- **One more challenge at the end.** -/
theorem samples_snoc : ∀ (j : Nat) {t tj : TState} {xs : List LeanVM.Parameters.E},
    (TM.samples j).run t = some (xs, tj) →
      (TM.samples (j + 1)).run t = some (xs ++ [tj.sponge.sample.1], { tj with sponge := tj.sponge.sample.2 })
  | 0, t, tj, xs, h => by
    simp only [TM.samples, StateT.run_pure] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [samples_run_succ]; rfl
  | j + 1, t, tj, xs, h => by
    rw [samples_run_succ] at h ⊢
    cases h2 : (TM.samples j).run { t with sponge := t.sponge.sample.2 } with
    | none => rw [h2] at h; cases h
    | some q =>
      rw [h2] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [samples_snoc j h2]; rfl

end Rv64mc.Model
