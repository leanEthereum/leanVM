/-
  Rv64mc.Model.Extra.NextScalars

  `Model.TM.nextScalars` read the way `next_scalars`' loop runs it, a scalar at a time at the end: one more read
  appends its scalar (`nextScalars_snoc`), and a read that fails fails every longer one (`nextScalars_fail`).
-/

import Rv64mc.Model.Transcript

namespace Rv64mc.Model

theorem nextScalars_run_succ (n : Nat) (t : TState) :
    (TM.nextScalars (n + 1)).run t = (match TM.nextScalar.run t with
      | some (x, t1) => ((TM.nextScalars n).run t1).map fun r => (x :: r.1, r.2)
      | none => none) := by
  simp only [TM.nextScalars, StateT.run_bind, StateT.run_pure]
  cases h : TM.nextScalar.run t with
  | none => simp
  | some p =>
    obtain ⟨x, t1⟩ := p
    cases h2 : (TM.nextScalars n).run t1 <;> simp [h2]

/-- **One more scalar read at the end.** -/
theorem nextScalars_snoc : ∀ (j : Nat) {t tj tj' : TState} {xs : List LeanVM.Parameters.E}
    {v : LeanVM.Parameters.E}, (TM.nextScalars j).run t = some (xs, tj) → TM.nextScalar.run tj = some (v, tj') →
    (TM.nextScalars (j + 1)).run t = some (xs ++ [v], tj')
  | 0, t, tj, tj', xs, v, h, hs => by
    simp only [TM.nextScalars, StateT.run_pure] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [nextScalars_run_succ, hs]; rfl
  | j + 1, t, tj, tj', xs, v, h, hs => by
    rw [nextScalars_run_succ] at h ⊢
    cases h1 : TM.nextScalar.run t with
    | none => rw [h1] at h; cases h
    | some p =>
      obtain ⟨x, t1⟩ := p
      rw [h1] at h
      simp only at h ⊢
      cases h2 : (TM.nextScalars j).run t1 with
      | none => rw [h2] at h; cases h
      | some q =>
        rw [h2] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [nextScalars_snoc j h2 hs]; rfl

/-- **A scalar the stream does not give fails every longer read.** -/
theorem nextScalars_fail : ∀ (j k : Nat) {t tj : TState} {xs : List LeanVM.Parameters.E},
    (TM.nextScalars j).run t = some (xs, tj) → TM.nextScalar.run tj = none →
    (TM.nextScalars (j + 1 + k)).run t = none
  | 0, k, t, tj, xs, h, hs => by
    simp only [TM.nextScalars, StateT.run_pure] at h
    obtain ⟨-, rfl⟩ := h
    rw [Nat.zero_add, Nat.add_comm, nextScalars_run_succ, hs]
  | j + 1, k, t, tj, xs, h, hs => by
    rw [show j + 1 + 1 + k = (j + 1 + k) + 1 by omega, nextScalars_run_succ]
    rw [nextScalars_run_succ] at h
    cases h1 : TM.nextScalar.run t with
    | none => rfl
    | some p =>
      obtain ⟨x, t1⟩ := p
      rw [h1] at h
      simp only at h ⊢
      cases h2 : (TM.nextScalars j).run t1 with
      | none => rw [h2] at h; cases h
      | some q =>
        rw [h2] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [nextScalars_fail j k h2 hs, Option.map_none]

end Rv64mc.Model
