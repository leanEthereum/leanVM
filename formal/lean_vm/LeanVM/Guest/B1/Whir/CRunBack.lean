/-
  LeanVM.Guest.B1.Whir.CRunBack

  The carried run read backwards through a bind and an option, and the fold rounds forward.
-/

module

public import LeanVM.Guest.B1.Whir.CTrace

/-!
# The carried run, and the fold rounds forward

* `rT_bind_some`, `rT_liftOption`: the carried run (`Tables.runT`) read backwards through a bind
  and `liftOption`.
* `foldRounds_run`: the fold rounds forward from `RoundsOk`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Tables (TSt runT runT_bind)

@[expose] public section

variable {α : Type}

/-! ## The carried run, backwards -/

theorem rT_bind_some {β : Type} {p : VerifierProgram α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runT (p.bind f) st = some r) :
    ∃ a st1, runT p st = some (a, st1) ∧ runT (f a) st1 = some r := by
  rw [runT_bind] at h
  obtain ⟨⟨a, st1⟩, h1, h2⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨a, st1, h1, h2⟩

theorem rT_liftOption {β : Type} {o : Option α} {f : α → VerifierProgram β} {st : TSt}
    {r : β × TSt} (h : runT ((liftOption o).bind f) st = some r) :
    ∃ a, o = some a ∧ runT (f a) st = some r := by
  cases o with
  | none =>
    change runT VerifierProgram.fail st = some r at h
    simp [runT] at h
  | some a => exact ⟨a, rfl, h⟩

/-! ## The fold rounds -/

/-- **The fold rounds forward**, every round passing. -/
theorem foldRounds_run : ∀ (n : ℕ) (s : WhirState) (fs ws : List E), ws.length = 6 * n →
    RoundsOk n fs ws →
    RunsTo (foldRounds n s) ⟨fs, []⟩ ws (roundsSpec n s fs ws) ⟨roundsCap n fs ws, []⟩
  | 0, s, fs, ws, hl, _ => by
    obtain rfl : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    exact runsTo_ret _ _
  | n + 1, s, fs, ws, hl, hok => by
    obtain ⟨hg, -, hok'⟩ := hok
    obtain ⟨u0, v0, c0, v1, c1, n2, he⟩ : ∃ u0 v0 c0 v1 c1 n2,
        ws.take 6 = [u0, v0, c0, v1, c1, n2] := by
      have : (ws.take 6).length = 6 := by simp; omega
      match ws.take 6, this with
      | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
    rw [he] at hg
    have h1 := opening_round_run s fs u0 v0 c0 v1 c1 n2 hg
    have ih := foldRounds_run n (roundSpec s fs (ws.take 6)).1 (roundSponge fs (ws.take 6)).cap
      (ws.drop 6) (by simp; omega) hok'
    rw [he] at ih
    have h := h1.bind (f := fun x ↦ match x with
        | (s, round) => do
          let (s, rounds) ← foldRounds n s
          return (s, round :: rounds))
      (ih.bind (f := fun x ↦ match x with
        | (s', rounds) => (pure (s', (roundSpec s fs [u0, v0, c0, v1, c1, n2]).2 :: rounds) :
          VerifierProgram (WhirState × List FoldRound))) (runsTo_ret _ _))
    refine RunsTo.of_eq h rfl ?_ ?_ ?_
    · rw [← he, List.append_nil, List.take_append_drop]
    · simp only [roundsSpec, he]
    · simp only [roundsCap, he]

end
end LeanVM.Guest.B1.Whir
