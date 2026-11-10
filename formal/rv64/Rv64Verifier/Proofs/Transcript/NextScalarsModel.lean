import Rv64Verifier.Model.Transcript

/-!
# `TM.nextScalars` read one scalar at a time

The machine's loop appends one scalar per `next_scalar`: `nextScalars_snoc` extends a run by a
scalar read, `nextScalars_fail` makes a failed read fail every longer run.
-/

namespace Rv64Verifier.Transcript
open LeanVM.Parameters Rv64Verifier.Model

theorem nextScalars_run_succ (n : ℕ) (T : TState) : (TM.nextScalars (n + 1)).run T =
    (TM.nextScalar.run T).bind fun p ↦
      ((TM.nextScalars n).run p.2).bind fun r ↦ some (p.1 :: r.1, r.2) := by
  simp only [TM.nextScalars, StateT.run_bind, StateT.run_pure]
  rfl

/-- A run of `d` reads, then `k` more. -/
theorem nextScalars_run_add : ∀ (d : ℕ) (T T' : TState) (xs : List E),
    (TM.nextScalars d).run T = some (xs, T') → ∀ k, (TM.nextScalars (d + k)).run T =
      ((TM.nextScalars k).run T').bind fun r ↦ some (xs ++ r.1, r.2)
  | 0, T, T', xs, h, k => by
    have h' : (some ([], T) : Option (List E × TState)) = some (xs, T') := h
    cases h'
    rw [Nat.zero_add]
    cases (TM.nextScalars k).run T <;> rfl
  | d + 1, T, T', xs, h, k => by
    rw [nextScalars_run_succ] at h
    rw [show d + 1 + k = (d + k) + 1 by omega, nextScalars_run_succ]
    cases h1 : TM.nextScalar.run T with
    | none => rw [h1] at h; cases h
    | some p =>
      rw [h1] at h
      simp only [Option.bind_some] at h ⊢
      cases h2 : (TM.nextScalars d).run p.2 with
      | none => rw [h2] at h; cases h
      | some r =>
        rw [h2] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        rw [nextScalars_run_add d p.2 r.2 r.1 h2 k]
        cases (TM.nextScalars k).run r.2 with
        | none => rfl
        | some q => simp

theorem nextScalars_snoc {d : ℕ} {T T' T'' : TState} {xs : List E} {x : E}
    (h : (TM.nextScalars d).run T = some (xs, T')) (hx : TM.nextScalar.run T' = some (x, T'')) :
    (TM.nextScalars (d + 1)).run T = some (xs ++ [x], T'') := by
  rw [nextScalars_run_add d T T' xs h 1, nextScalars_run_succ, hx]
  rfl

theorem nextScalars_fail {d n : ℕ} {T T' : TState} {xs : List E}
    (h : (TM.nextScalars d).run T = some (xs, T')) (hx : TM.nextScalar.run T' = none)
    (hn : d < n) : (TM.nextScalars n).run T = none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = d + (k + 1) := ⟨n - d - 1, by omega⟩
  rw [nextScalars_run_add d T T' xs h (k + 1), nextScalars_run_succ, hx]
  rfl

end Rv64Verifier.Transcript
