/-
  LeanVM.Protocol.Whir.Sound.Defs

  The shapes of the WHIR commitments, the doom at the start of a level, and the escape bounds of
  each group of challenges of a level.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Protocol.Whir.Sound.Interface

/-!
# Level doom and escape bounds

A level `i` of the deployed WHIR opening (`LeanVM.Protocol.Verifier.whirLevels`, leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`) opens commitment `i`, a matrix of `2^(κ_i + R_i)` rows
of `wdOf i ℓ_i` words: `2^ℓ₀` `K`-words at level `0` (the stack's lanes), `3·2^ℓ_i` words (the lanes
in `E`) deeper. `ShapeOK` records that the history has exactly the commitments `0..i` and that the
`i`-th has this shape; `LevelPre` is the doom at the start of a level: `A(i, 0)` and `ShapeOK`.

The escape bounds of a level's groups, each a probability over the group's challenges:

* `eFold P ℓ` (`LeanVM.Protocol.Whir.Sound.Folds`): `(2·L + 2^(ℓ−1)·E_mca) / |E|` per fold;
* `eOod P' κ`: `C(L', 2)·κ / |E|` for the out-of-domain point on `κ` coordinates;
* `eQuery P P' t`: `((A − 1)/n)^t + (t + 1)·L' / |E|` for the query positions and `λ`,
  `A` the Johnson threshold and `n` the block length of the current level;
* `eQueryFinal P t`: `((A − 1)/n)^t + t / |E|` on the final level;
* `eTail`: `2 / |E|` per tail round.

The proof of work before the query group discounts `eQuery` by `2^-17`.
-/

namespace LeanVM.Protocol.Whir.Sound

open LeanVM.Parameters LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
  LeanVM.Protocol.Whir Finset

@[expose] public section

/-- The width of commitment `i`: `2^ℓ` words at level `0`, `3·2^ℓ` deeper. -/
def wdOf (i ℓ : ℕ) : ℕ := if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ

/-- The history has the commitments `0..i`, the `i`-th of `2^(κ+R)` rows of `wdOf i ℓ` words. -/
def ShapeOK (i : ℕ) (P : LevelCode) (ℓ : ℕ) (cs : List (ℕ × ℕ × Word)) : Prop :=
  cs.length = i + 1 ∧ ∃ W, cs[i]? = some (P.κ + P.R, wdOf i ℓ, W) ∧ WellShaped (wdOf i ℓ) W

/-- **The doom at the start of level `i`**: `A(i, 0)` and the commitments' shape. -/
def LevelPre (μ ℓ₀ : ℕ) (w : List E → E) (i : ℕ) (P : LevelCode) (ℓ pre : ℕ) (s : WhirStateT)
    (cs : List (ℕ × ℕ × Word)) : Prop :=
  FoldInv μ ℓ₀ w i P ℓ pre s [] cs ∧ ShapeOK i P ℓ cs

/-- The out-of-domain escape: `C(L', 2)·κ / |E|`. -/
noncomputable def eOod (P' : LevelCode) (κ : ℕ) : ENNReal :=
  ((P'.listMax.choose 2 * κ : ℕ) : ENNReal) / Fintype.card E

/-- The query group's escape: `((A − 1)/n)^t + (t + 1)·L' / |E|`. -/
noncomputable def eQuery (P P' : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (((t + 1) * P'.listMax : ℕ) : ENNReal) / Fintype.card E

/-- The final query group's escape: `((A − 1)/n)^t + t / |E|`. -/
noncomputable def eQueryFinal (P : LevelCode) (t : ℕ) : ENNReal :=
  (((P.thr - 1 : ℕ) : ENNReal) / P.n) ^ t + (t : ENNReal) / Fintype.card E

/-- A tail round's escape: `2 / |E|`. -/
noncomputable def eTail : ENNReal := (2 : ENNReal) / Fintype.card E

/-! ## Shape lemmas -/

theorem shapeOK_word {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) : cs[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) ∧
      WellShaped (wdOf i ℓ) (wordOf cs i) := by
  obtain ⟨-, W, hW, hws⟩ := h
  rw [wordOf_eq hW]
  exact ⟨hW, hws⟩

theorem shapeOK_append {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (x : ℕ × ℕ × Word) :
    (cs ++ [x])[i]? = some (P.κ + P.R, wdOf i ℓ, wordOf cs i) := by
  rw [List.getElem?_append_left (by rw [h.1]; omega)]
  exact (shapeOK_word h).1

/-- The rows of a well-shaped leaf of commitment `i` give `2^ℓ` lanes. -/
theorem length_wordOf {i : ℕ} {P : LevelCode} {ℓ : ℕ} {cs : List (ℕ × ℕ × Word)}
    (h : ShapeOK i P ℓ cs) (q : ℕ) :
    (wordOf cs i q).length = if i = 0 then 2 ^ ℓ else 3 * 2 ^ ℓ :=
  (shapeOK_word h).2 q

end
end LeanVM.Protocol.Whir.Sound
