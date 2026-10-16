module

public import LeanVMCircuits.Rec.CrScale

@[expose] public section

/-!
A prover trying several transcripts.

In the random-oracle model two transcripts that absorb different words query the oracle at different points, so a prover that tries `m` transcripts draws an oracle per try: an outcome is `(ρ, H)`, `ρ : Fin m → X` the tries' oracles on their transcripts' words and `H` the compression oracle they share. Each try `i` has its event `B i`, which may read every try's oracle, and the prover outputs a try `pick (ρ, H)`, any function of the outcome.

`Bind.frac_fix_le`: if at every value of the other tries' oracles the outcomes `(ρ i, H)` at which `B i` holds are at most an `ε` fraction, so are the outcomes at which it holds. With the other tries' oracles fixed as whole functions, try `i` is an oracle algorithm on its own oracle and `H` alone, which is the setting of the run theorems (`Bind.Run`) and of `AirLink.tree_sound_end`, a try reading another try's answers reading a fixed function. `Bind.frac_pick_le`: the outcomes at which the output try's event holds are at most the sum of the tries' bounds, `frac_pick_le_mul` at most `m · ε`. `Edges.tries_bound_deployed` folds this into the end-to-end bound: with each try's failure, at every value of the other tries' oracles, within `tree_sound_end`'s bound at `tree_bound_deployed`'s sizes, the output try fails on at most an `m / 2^19` fraction with #551 budgets `2^20` per binding shape and `m / 2^7` with `2^32`. A try's compression queries `Q` count every query the prover makes, the other tries' included, since they share `H`.
-/

namespace LeanVMCircuits.Rec.Bind

open Finset

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Re-pairing an outcome's try `i` with a fresh oracle: `(ρ, x, y) ↦ ((ρ[i ↦ x], y), ρ i)`. -/
def swapTry {m : ℕ} (i : Fin m) : (Fin m → X) × X × Y ≃ ((Fin m → X) × Y) × X where
  toFun a := ((Function.update a.1 i a.2.1, a.2.2), a.1 i)
  invFun b := (Function.update b.1.1 i b.2, b.1.1 i, b.1.2)
  left_inv a := by simp
  right_inv b := by simp

/-- Counting an event through try `i`'s oracle: its outcomes, times `|X|`, are the sum over every value of the tries'
oracles of the outcomes `(x, y)` at which it holds with try `i`'s oracle replaced by `x`. -/
theorem card_fix_mul {m : ℕ} (i : Fin m) (P : (Fin m → X) × Y → Prop) [DecidablePred P] :
    #{ω | P ω} * Fintype.card X = ∑ ρ : Fin m → X, #{p : X × Y | P (Function.update ρ i p.1, p.2)} := by
  have h1 : ({b : ((Fin m → X) × Y) × X | P b.1} : Finset _) = ({ω | P ω} : Finset _) ×ˢ univ := by
    ext b
    simp
  have h2 : #{b : ((Fin m → X) × Y) × X | P b.1} =
      #{a : (Fin m → X) × X × Y | P (Function.update a.1 i a.2.1, a.2.2)} :=
    (card_equiv (s := ({a : (Fin m → X) × X × Y | P (Function.update a.1 i a.2.1, a.2.2)} : Finset _))
      (t := ({b : ((Fin m → X) × Y) × X | P b.1} : Finset _)) (swapTry i) fun a => by simp [swapTry]).symm
  rw [← card_univ, ← card_product, ← h1, h2, card_filter, Fintype.sum_prod_type]
  simp only [card_filter]

/-- The bound through try `i`: an event at most an `ε` fraction of the outcomes `(x, y)` at every value of the other
tries' oracles is at most an `ε` fraction of all outcomes. -/
theorem frac_fix_le {m : ℕ} (i : Fin m) (P : (Fin m → X) × Y → Prop) [DecidablePred P] {ε : ℚ≥0}
    (h : ∀ ρ : Fin m → X, (#{p : X × Y | P (Function.update ρ i p.1, p.2)} : ℚ≥0) / Fintype.card (X × Y) ≤ ε) :
    (#{ω | P ω} : ℚ≥0) / Fintype.card ((Fin m → X) × Y) ≤ ε := by
  rcases Nat.eq_zero_or_pos (Fintype.card X) with hX | hX
  · have : IsEmpty X := Fintype.card_eq_zero_iff.mp hX
    have : IsEmpty (Fin m → X) := ⟨fun ρ => isEmptyElim (ρ i)⟩
    simp
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hY | hY
  · have : IsEmpty Y := Fintype.card_eq_zero_iff.mp hY
    simp
  have hXY : (0 : ℚ≥0) < Fintype.card (X × Y) := by
    rw [Fintype.card_prod]
    exact_mod_cast Nat.mul_pos hX hY
  have hXq : (0 : ℚ≥0) < Fintype.card X := by exact_mod_cast hX
  have hsum : (#{ω | P ω} : ℚ≥0) * Fintype.card X ≤
      Fintype.card (Fin m → X) * (ε * Fintype.card (X × Y)) := by
    have hc := congrArg (Nat.cast (R := ℚ≥0)) (card_fix_mul i P)
    push_cast at hc
    rw [hc]
    calc ∑ ρ : Fin m → X, (#{p : X × Y | P (Function.update ρ i p.1, p.2)} : ℚ≥0)
        ≤ ∑ _ρ : Fin m → X, ε * Fintype.card (X × Y) := sum_le_sum fun ρ _ => (div_le_iff₀ hXY).mp (h ρ)
      _ = Fintype.card (Fin m → X) * (ε * Fintype.card (X × Y)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
  have : Nonempty X := Fintype.card_pos_iff.mp hX
  have : Nonempty Y := Fintype.card_pos_iff.mp hY
  rw [div_le_iff₀ (by exact_mod_cast Fintype.card_pos)]
  refine le_of_mul_le_mul_right (hsum.trans_eq ?_) hXq
  rw [Fintype.card_prod, Fintype.card_prod]
  push_cast
  ring

/-- The union bound over tries: the outcomes at which the output try `pick ω`'s event holds are at most the sum of
each try's bound at every value of the other tries' oracles. -/
theorem frac_pick_le {m : ℕ} (B : Fin m → (Fin m → X) × Y → Prop) [∀ i, DecidablePred (B i)] (pick : (Fin m → X) × Y → Fin m)
    (ε : Fin m → ℚ≥0)
    (hB : ∀ i ρ, (#{p : X × Y | B i (Function.update ρ i p.1, p.2)} : ℚ≥0) / Fintype.card (X × Y) ≤ ε i) :
    (#{ω | B (pick ω) ω} : ℚ≥0) / Fintype.card ((Fin m → X) × Y) ≤ ∑ i, ε i := by
  classical
  have hsub : ({ω | B (pick ω) ω} : Finset ((Fin m → X) × Y)) ⊆ univ.biUnion fun i => ({ω | B i ω} : Finset _) :=
    fun ω hω => mem_biUnion.mpr ⟨pick ω, mem_univ _, by simpa using hω⟩
  have hc : (#{ω | B (pick ω) ω} : ℚ≥0) ≤ ∑ i, (#{ω | B i ω} : ℚ≥0) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  calc (#{ω | B (pick ω) ω} : ℚ≥0) / Fintype.card ((Fin m → X) × Y)
      ≤ (∑ i, (#{ω | B i ω} : ℚ≥0)) / Fintype.card ((Fin m → X) × Y) := div_le_div_of_nonneg_right hc (by positivity)
    _ = ∑ i, (#{ω | B i ω} : ℚ≥0) / Fintype.card ((Fin m → X) × Y) := sum_div _ _ _
    _ ≤ ∑ i, ε i := sum_le_sum fun i _ => frac_fix_le i (B i) (hB i)

/-- With each try's event at most an `ε` fraction at every value of the other tries' oracles, the output try's is at
most `m · ε`. -/
theorem frac_pick_le_mul {m : ℕ} (B : Fin m → (Fin m → X) × Y → Prop) [∀ i, DecidablePred (B i)] (pick : (Fin m → X) × Y → Fin m) {ε : ℚ≥0}
    (hB : ∀ i ρ, (#{p : X × Y | B i (Function.update ρ i p.1, p.2)} : ℚ≥0) / Fintype.card (X × Y) ≤ ε) :
    (#{ω | B (pick ω) ω} : ℚ≥0) / Fintype.card ((Fin m → X) × Y) ≤ m * ε :=
  (frac_pick_le B pick (fun _ => ε) hB).trans (by simp)

/-- The tries' example: two tries of a fair bit, the output the first try whose bit is set, each try's event its bit
set. -/
def bitPick (ω : (Fin 2 → Bool) × Unit) : Fin 2 := if ω.1 0 then 0 else 1

/-- Non-vacuity: in the example each try's event is half of the outcomes at every value of the other try's bit, so
`frac_pick_le_mul` applies with `ε = 1/2`, and the output try's event is three of the four outcomes. -/
theorem bitPick_frac :
    (#{ω : (Fin 2 → Bool) × Unit | ω.1 (bitPick ω) = true} : ℚ≥0) / Fintype.card ((Fin 2 → Bool) × Unit) ≤
      2 * (1 / 2) ∧ #{ω : (Fin 2 → Bool) × Unit | ω.1 (bitPick ω) = true} = 3 := by
  refine ⟨(frac_pick_le_mul (ε := 1 / 2) (fun i ω => ω.1 i = true) bitPick fun i ρ => ?_).trans_eq
    (show ((2 : ℕ) : ℚ≥0) * (1 / 2) = 2 * (1 / 2) by norm_num),
    by decide⟩
  simp only [Function.update_self]
  have : #{p : Bool × Unit | p.1 = true} = 1 := by decide
  rw [this]
  norm_num [Fintype.card_prod]

end LeanVMCircuits.Rec.Bind

namespace LeanVMCircuits.Rec.Edges

open Finset LeanVMCircuits.Rec LeanVMCircuits.Rec.Bind

/-- The end-to-end bound over tries: a prover trying `m` transcripts, try `i` failing (`fail i`, some node's statement
or input claims false in its tree, as in `AirLink.tree_sound_end`) on at most `tree_sound_end`'s bound for its tree
`S i ρ` at every value `ρ` of the other tries' oracles, at `tree_bound_deployed`'s sizes. Whichever try it outputs,
the output try fails on at most an `m / 2^19` fraction of the outcomes with #551 budgets `2^20` per binding shape and
`m / 2^7` with `2^32`. -/
theorem tries_bound_deployed {X ι : Type} [Fintype X] {m : ℕ}
    (fail : Fin m → (Fin m → X) × ((Fin 14 → K) → Fin 4 → K) → Prop) [∀ i, DecidablePred (fail i)]
    (pick : (Fin m → X) × ((Fin 14 → K) → Fin 4 → K) → Fin m) (S : Fin m → (Fin m → X) → Finset ι)
    (hS : ∀ i ρ, (S i ρ).card ≤ 2 ^ 10) (D Q B : Fin m → (Fin m → X) → ι → ℕ)
    (Qp : Fin m → (Fin m → X) → ι → Fin 4 → ℕ) (hD : ∀ i ρ, ∀ v ∈ S i ρ, D i ρ v ≤ 2 ^ 40)
    (hQ : ∀ i ρ, ∀ v ∈ S i ρ, Q i ρ v ≤ 2 ^ 64) (hB : ∀ i ρ, ∀ v ∈ S i ρ, B i ρ v ≤ 2 ^ 86)
    (hend : ∀ i ρ, (#{p : X × ((Fin 14 → K) → Fin 4 → K) | fail i (Function.update ρ i p.1, p.2)} : ℚ≥0) /
      Fintype.card (X × ((Fin 14 → K) → Fin 4 → K)) ≤
      ∑ v ∈ S i ρ, ((D i ρ v : ℚ≥0) / Fintype.card E + (∑ k, finalBound (Qp i ρ v k)).toNNRat +
        epsCR K (Q i ρ v) + epsLate K (Q i ρ v) (B i ρ v))) :
    ((∀ i ρ, ∀ v ∈ S i ρ, ∀ k, Qp i ρ v k ≤ 2 ^ 20) → (#{ω | fail (pick ω) ω} : ℚ≥0) /
      Fintype.card ((Fin m → X) × ((Fin 14 → K) → Fin 4 → K)) ≤ m * (1 / 2 ^ 19)) ∧
    ((∀ i ρ, ∀ v ∈ S i ρ, ∀ k, Qp i ρ v k ≤ 2 ^ 32) → (#{ω | fail (pick ω) ω} : ℚ≥0) /
      Fintype.card ((Fin m → X) × ((Fin 14 → K) → Fin 4 → K)) ≤ m * (1 / 2 ^ 7)) :=
  ⟨fun h => frac_pick_le_mul fail pick fun i ρ => (hend i ρ).trans
      ((tree_bound_deployed (S i ρ) (hS i ρ) (D i ρ) (Q i ρ) (B i ρ) (Qp i ρ) (hD i ρ) (hQ i ρ) (hB i ρ)).1 (h i ρ)),
    fun h => frac_pick_le_mul fail pick fun i ρ => (hend i ρ).trans
      ((tree_bound_deployed (S i ρ) (hS i ρ) (D i ρ) (Q i ρ) (B i ρ) (Qp i ρ) (hD i ρ) (hQ i ρ) (hB i ρ)).2 (h i ρ))⟩

end LeanVMCircuits.Rec.Edges
