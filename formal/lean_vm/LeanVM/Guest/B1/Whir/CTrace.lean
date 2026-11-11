/-
  LeanVM.Guest.B1.Whir.CTrace

  An accepting run's levels as data: each level's round words and its message, nonces and
  openings.
-/

module

public import LeanVM.Guest.B1.Whir.CInvOpen

/-!
# The run's levels as data

`LvD`: a level's honest data, its round words with a `NextW` (non-final) or a `FinW` (final).
`LvsRunD … ds`: `LvsRun` with the data `ds` named; `LvsRun.data`: every `LvsRun` has its data.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A level's honest data. -/
inductive LvD where
  | next (rw : List E) (W : NextW)
  | fin (rw : List E) (W : FinW)

/-- **`LvsRun` with its data named.** -/
def LvsRunD (logN lane : ℕ) : ℕ → List Whir.Level → WhirState → List E → List (Digest × ℕ × ℕ) →
    List E → List (List Opening) → WhirEnd → List LvD → Prop
  | index, [level], s, cap, R, xs, os, w, [LvD.fin rw W] =>
    rw.length = 6 * level.fold ∧ RoundsOk level.fold cap rw ∧
      xs = rw ++ W.words ∧ os = [W.phase] ∧
      FinOk logN index level (rsSt level s cap rw) (rsRounds level s cap rw) (rsF level cap rw) R W ∧
      w = W.wend logN lane level (rsSt level s cap rw) (rsF level cap rw)
  | index, level :: next :: rest, s, cap, R, xs, os, w, LvD.next rw W :: ds =>
    ∃ (xs' : List E) (os' : List (List Opening)),
      rw.length = 6 * level.fold ∧ RoundsOk level.fold cap rw ∧
      xs = rw ++ W.words ++ xs' ∧ os = W.phase :: os' ∧
      NextOk logN index level (rsSt level s cap rw) (rsF level cap rw) R W ∧
      LvsRunD logN lane (index + 1) (next :: rest)
        (W.glued logN index level (rsSt level s cap rw) (rsF level cap rw) (rsRounds level s cap rw))
        (capOf ((W.F3 (rsF level cap rw) (logN - (rsSt level s cap rw).alphas.length)
          (logN - (rsSt level s cap rw).alphas.length + level.logInvRate) level.queries).nonceState W.n2))
        (W.roots (logN - (rsSt level s cap rw).alphas.length) next R) xs' os' w ds
  | _, _, _, _, _, _, _, _, _ => False

/-- **Every `LvsRun` has its data.** -/
theorem LvsRun.data (logN lane : ℕ) : ∀ (levels : List Whir.Level) (index : ℕ) (s : WhirState)
    (cap : List E) (R : List (Digest × ℕ × ℕ)) (xs : List E) (os : List (List Opening)) (w : WhirEnd),
    LvsRun logN lane index levels s cap R xs os w → ∃ ds, LvsRunD logN lane index levels s cap R xs os w ds
  | [], _, _, _, _, _, _, _, h => absurd h (by simp [LvsRun])
  | [_], _, _, _, _, _, _, _, h => by
    obtain ⟨rw, W, h⟩ := h
    exact ⟨[LvD.fin rw W], h⟩
  | _ :: next :: rest, _, _, _, _, _, _, _, h => by
    obtain ⟨rw, W, xs', os', h1, h2, h3, h4, h5, h6⟩ := h
    obtain ⟨ds, hd⟩ := LvsRun.data logN lane (next :: rest) _ _ _ _ _ _ _ h6
    exact ⟨LvD.next rw W :: ds, xs', os', h1, h2, h3, h4, h5, hd⟩

end
end LeanVM.Guest.B1.Whir
