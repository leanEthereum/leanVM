import Whir.RingMapSoundness

/-!
# Gamma batching before the six-stage ring map

The error matrix, sent slices, and candidate list are fixed outside both random
challenges. Gamma powers stay inside the additive ring map, as in Annex A.
-/
namespace Whir.RingMapBatching

open scoped BigOperators

variable {E : Type*} [Field E]

/-- Gamma batches claims before the ring map is applied to each binary slice. -/
def batchErrors {m : ℕ} (γ : E) (δ : Fin m → Fin 64 → E) : Fin 64 → E :=
  fun i => ∑ j, γ ^ j.val * δ j i

variable [Fintype E] [DecidableEq E]

/-- A genuinely wrong family cannot vanish under gamma batching except at roots
of a nonzero degree-at-most-`m-1` polynomial from one of its erroneous slices. -/
theorem batch_zero_probability {m : ℕ} (δ : Fin m → Fin 64 → E) (hne : δ ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun γ : E => batchErrors γ δ = 0) ≤
      ((m - 1 : ℕ) : ℚ) / Fintype.card E := by
  classical
  have hex : ∃ j i, δ j i ≠ 0 := by
    contrapose! hne
    ext j i
    exact hne j i
  obtain ⟨j, i, hji⟩ := hex
  let p : Polynomial E := ∑ j : Fin m, Polynomial.monomial j.val (δ j i)
  have hp : p ≠ 0 := by
    intro hp
    have hc := congrArg (fun q : Polynomial E => q.coeff j.val) hp
    exact hji (by simpa [p, Polynomial.coeff_monomial, ← Fin.ext_iff] using hc)
  have hd : p.natDegree ≤ m - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)
  have hs : (Finset.univ.filter fun γ : E => batchErrors γ δ = 0) ⊆
      Finset.univ.filter fun γ : E => p.eval γ = 0 := by
    intro γ hγ
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hi := congrFun (Finset.mem_filter.mp hγ).2 i
    simpa [batchErrors, p, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      mul_comm] using hi
  exact (show Soundness.uniformProb (Finset.univ.filter fun γ : E => batchErrors γ δ = 0) ≤
      Soundness.uniformProb (Finset.univ.filter fun γ : E => p.eval γ = 0) from
    div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hs) (by positivity)).trans
      (Soundness.root_error p hp (m - 1) hd)

/-- Exact averaging over the independent gamma and map-challenge coordinates. -/
theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    (P : A × B → Prop) [DecidablePred P] :
    Soundness.uniformProb (Finset.univ.filter P) =
      (∑ a : A, Soundness.uniformProb (Finset.univ.filter fun b : B => P (a, b))) /
        Fintype.card A := by
  classical
  simp only [Soundness.uniformProb, Finset.card_filter, Fintype.card_prod,
    Fintype.sum_prod_type, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Nat.cast_mul, ← Finset.sum_div]
  ring

/-- Fiber bounds compose with an exceptional gamma event, without requiring
independence of the acceptance predicate itself. -/
theorem conditional_error {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (bad : A → Prop) [DecidablePred bad]
    (P : A × B → Prop) [DecidablePred P] (a b : ℚ) (hb : 0 ≤ b)
    (hbad : Soundness.uniformProb (Finset.univ.filter bad) ≤ a)
    (hgood : ∀ x, ¬ bad x →
      Soundness.uniformProb (Finset.univ.filter fun y : B => P (x, y)) ≤ b) :
    Soundness.uniformProb (Finset.univ.filter P) ≤ a + b := by
  classical
  have hf (x : A) :
      Soundness.uniformProb (Finset.univ.filter fun y : B => P (x, y)) ≤
        (if bad x then 1 else 0) + b := by
    by_cases hx : bad x
    · have hle : Soundness.uniformProb (Finset.univ.filter fun y : B => P (x, y)) ≤ 1 := by
        unfold Soundness.uniformProb
        apply (div_le_one (by positivity)).mpr
        exact_mod_cast Finset.card_le_univ _
      simpa [hx] using hle.trans (le_add_of_nonneg_right hb)
    · simpa [hx] using hgood x hx
  rw [uniform_product]
  calc
    _ ≤ (∑ x : A, ((if bad x then 1 else 0 : ℚ) + b)) / Fintype.card A :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hf x) (by positivity)
    _ = Soundness.uniformProb (Finset.univ.filter bad) + b := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Soundness.uniformProb, Finset.card_filter, Nat.cast_sum,
        Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      rw [add_div, mul_div_cancel_left₀ _ (by positivity)]
    _ ≤ a + b := by linarith

variable [CharP E 2]

/-- The two independently sampled challenges bound the actual batched map error. -/
theorem batched_map_error_probability {m : ℕ} (x : E)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (δ : Fin m → Fin 64 → E) (hne : δ ≠ 0) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      (∑ i : Fin 64, x ^ i.val * RingSwitch.composedMap r.2 (batchErrors r.1 δ i)) = 0) ≤
      ((m - 1 : ℕ) : ℚ) / Fintype.card E + (2 : ℚ)^32 / Fintype.card E := by
  apply conditional_error (fun γ : E => batchErrors γ δ = 0) _ _ _ (by positivity)
    (batch_zero_probability δ hne)
  intro γ hγ
  exact RingMapSoundness.map_error_probability x conjugates (batchErrors γ δ) hγ

/-- Collision probability for the actual family targets, derived from unequal
slice matrices rather than an assumed nonzero target discrepancy. -/
theorem family_error_probability {m : ℕ} (x : E)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (sent honest : Fin m → Fin 64 → E) (hne : sent ≠ honest) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
        (fun j : Fin m => r.1 ^ j.val) sent =
      RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
        (fun j : Fin m => r.1 ^ j.val) honest) ≤
      ((m - 1 : ℕ) : ℚ) / Fintype.card E + (2 : ℚ)^32 / Fintype.card E := by
  convert batched_map_error_probability x conjugates (sent - honest)
    (sub_ne_zero.mpr hne) using 1
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← sub_eq_zero, RingMapSoundness.family_target_discrepancy]
  rfl

/-- The honest comparison is the packed opening target from `honest_family`,
including arbitrary point weights, not a fresh target-error assumption. -/
theorem honest_family_error_probability {m : ℕ} {U : Type*} [Fintype U] (x : E)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (bits : Fin m → Fin 64 → U → Bool) (weights : Fin m → U → E)
    (sent : Fin m → Fin 64 → E)
    (hne : sent ≠ fun j => RingSwitch.slice (weights j) (bits j)) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
        (fun j : Fin m => r.1 ^ j.val) sent =
      ∑ j : Fin m, ∑ u : U, RingSwitch.composedMap r.2 (r.1 ^ j.val * weights j u) *
        RingSwitch.packed (fun i : Fin 64 => x ^ i.val) (bits j) u) ≤
      ((m - 1 : ℕ) : ℚ) / Fintype.card E + (2 : ℚ)^32 / Fintype.card E := by
  simpa only [RingSwitch.honest_family] using
    family_error_probability x conjugates sent (fun j => RingSwitch.slice (weights j) (bits j)) hne

/-- The candidate list and sent matrix are fixed before gamma and all six map
challenges. Candidates already equal to the sent matrix cause no false-claim event. -/
theorem family_fixed_list {m : ℕ} (x : E)
    (conjugates : Function.Injective (fun k : Fin 64 => x ^ (2 ^ k.val)))
    (sent : Fin m → Fin 64 → E) (candidates : Finset (Fin m → Fin 64 → E)) :
    Soundness.uniformProb (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      ∃ honest ∈ candidates, sent ≠ honest ∧
        RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
          (fun j : Fin m => r.1 ^ j.val) sent =
        RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
          (fun j : Fin m => r.1 ^ j.val) honest) ≤
      (candidates.card : ℚ) *
        (((m - 1 : ℕ) : ℚ) / Fintype.card E + (2 : ℚ)^32 / Fintype.card E) := by
  classical
  let events : ↥candidates → Finset (E × (Fin 6 → E)) := fun honest =>
    Finset.univ.filter fun r => sent ≠ honest.val ∧
      RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
        (fun j : Fin m => r.1 ^ j.val) sent =
      RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
        (fun j : Fin m => r.1 ^ j.val) honest.val
  have he : (Finset.univ.filter fun r : E × (Fin 6 → E) =>
      ∃ honest ∈ candidates, sent ≠ honest ∧
        RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
          (fun j : Fin m => r.1 ^ j.val) sent =
        RingSwitch.familyTarget (RingSwitch.composedMap r.2) (fun i : Fin 64 => x ^ i.val)
          (fun j : Fin m => r.1 ^ j.val) honest) = Finset.univ.biUnion events := by
    ext r
    simp [events, and_left_comm]
  rw [he]
  calc
    _ ≤ ∑ honest, Soundness.uniformProb (events honest) := Soundness.union_bound events
    _ ≤ ∑ _honest : ↥candidates,
        (((m - 1 : ℕ) : ℚ) / Fintype.card E + (2 : ℚ)^32 / Fintype.card E) := by
      apply Finset.sum_le_sum
      intro honest _
      by_cases hne : sent = honest.val
      · simp [events, hne, Soundness.uniformProb]
        positivity
      · simpa only [events, hne, ne_eq, not_false_eq_true, true_and] using
          family_error_probability x conjugates sent honest.val hne
    _ = _ := by simp; ring

end Whir.RingMapBatching
