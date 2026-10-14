import Whir.CandidateFolding
import Whir.VerifierInvariant

/-! One actual adversarial fold combines the checked same-set MCA provider with
the actual compact-message root bound. Neither is a soundness hypothesis. -/
namespace Whir.FoldSoundness
open Concrete Protocol CandidateFolding VerifierInvariant

private theorem probability_mono {Ω : Type*} [Fintype Ω] (a b : Finset Ω) (h : a ⊆ b) :
    Soundness.uniformProb a ≤ Soundness.uniformProb b := by
  unfold Soundness.uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card h) (by positivity)

private theorem probability_union {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a b : Finset Ω) :
    Soundness.uniformProb (a ∪ b) ≤ Soundness.uniformProb a + Soundness.uniformProb b := by
  unfold Soundness.uniformProb
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_union_le a b) (by positivity)

open Classical in
private theorem fold_escape_union {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Inhabited F] [CharP F 2] (old : Finset (Array F)) (following : F → Finset (Array F))
    (state : VerifierState F) (block lanes : Nat) (next : F → Message F) (bad : Finset F)
    (shape : ∀ witness ∈ old, witness.size = (lanes * 2) * block)
    (weights : ∀ witness ∈ old, state.weight.size = witness.size)
    (lifting : ∀ r ∉ bad, ∀ witness ∈ following r,
      ∃ previous ∈ old, witness = foldValues previous block r)
    (lost : Lost old state) :
    Soundness.uniformProb (Finset.univ.filter fun r =>
      ¬ Lost (following r) (state.fold block r (next r))) ≤
      (old.card : ℚ) * (2 / Fintype.card F) + Soundness.uniformProb bad := by
  classical
  let collision := roundBad old state block
  have subset : (Finset.univ.filter fun r =>
      ¬ Lost (following r) (state.fold block r (next r))) ⊆ collision ∪ bad := by
    intro r hr
    by_cases hc : r ∈ collision
    · exact Finset.mem_union.mpr (Or.inl hc)
    by_cases hb : r ∈ bad
    · exact Finset.mem_union.mpr (Or.inr hb)
    exact False.elim ((Finset.mem_filter.mp hr).2
      (fold_lost old (following r) state block lanes r (next r)
        shape weights (lifting r hb) hc))
  exact ((probability_mono _ _ subset).trans (probability_union collision bad)).trans
    (add_le_add (roundBad_probability old state block lost) le_rfl)

open Classical in
/-- Pending next messages may depend arbitrarily on the sampled fold challenge.
The old oracle and incoming state are fixed first, as required by the causal game. -/
theorem concrete_fold_escape (top : Bool) (n rate : Nat) (depth : n + rate ≤ 64)
    {lanes : Nat} (degree_pos : 1 ≤ 2 ^ n - 1)
    (degree_bound : 2 ^ n - 1 ≤ 2 ^ (n + rate) - 2)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (johnson : radius < 1 - Real.sqrt (((2 ^ n - 1 : Nat) : ℝ) / 2 ^ (n + rate)))
    (oracle : Fin (lanes * 2) → Fin (2 ^ (n + rate)) → E)
    (state : VerifierState E) (next : E → Message E)
    (weightSize : state.weight.size = (lanes * 2) * 2 ^ n)
    (lost : Lost (arrayCandidates top (concreteEncoder n rate) oracle
      ⌈((2 ^ (n + rate) : Nat) : ℝ) * (1 - radius)⌉₊) state) :
    let threshold := ⌈((2 ^ (n + rate) : Nat) : ℝ) * (1 - radius)⌉₊
    let old := arrayCandidates top (concreteEncoder n rate) oracle threshold
    (Soundness.uniformProb (Finset.univ.filter fun r : E =>
      ¬ Lost (arrayCandidates top (concreteEncoder n rate) (foldOracle oracle r) threshold)
        (state.fold (CandidateFolding.foldBlock top (2 ^ n)) r (next r))) : ℝ) ≤
      (old.card : ℝ) * (2 / (Fintype.card E : ℝ)) +
        MutualAgreement.johnsonNumerator (2 ^ (n + rate)) (2 ^ n) radius / Fintype.card E := by
  classical
  dsimp only
  let threshold := ⌈((2 ^ (n + rate) : Nat) : ℝ) * (1 - radius)⌉₊
  let old := arrayCandidates top (concreteEncoder n rate) oracle threshold
  let following := fun r => arrayCandidates top (concreteEncoder n rate)
    (foldOracle oracle r) threshold
  obtain ⟨bad, bound, lifting⟩ := concrete_candidate_provider top n rate depth degree_pos
    degree_bound radius radius_nonneg johnson oracle
  have result := fold_escape_union old following state (CandidateFolding.foldBlock top (2 ^ n))
    (if top then lanes else lanes * 2 ^ n) next bad
    (fun witness hw => arrayCandidates_round_shape top (concreteEncoder n rate)
      oracle threshold witness hw)
    (fun witness hw => weightSize.trans (arrayCandidates_size top
      (concreteEncoder n rate) oracle threshold witness hw).symm)
    lifting lost
  have resultReal : (Soundness.uniformProb (Finset.univ.filter fun r =>
      ¬ Lost (following r) (state.fold (CandidateFolding.foldBlock top (2 ^ n)) r (next r))) : ℝ) ≤
      (old.card : ℝ) * (2 / Fintype.card E) + (Soundness.uniformProb bad : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_le (K := ℝ)).mpr result
  exact resultReal.trans (add_le_add le_rfl bound)

end Whir.FoldSoundness
