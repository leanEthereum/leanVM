import Whir.Algebra
import Whir.Soundness
import Whir.CodingBounds
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Powerset

/-! OOD separation for the existing `Whir.mle`, over a supplied finite field.
Candidate sets are fixed inputs, not functions of the sampled evaluation point. -/
namespace Whir.OODBounds
open scoped BigOperators Classical
open MvPolynomial
variable {F : Type*} [Field F]

/-- The existing multilinear extension evaluated symbolically. -/
noncomputable def mlePolynomial {n : ℕ} (f : Cube n → F) : MvPolynomial (Fin n) F :=
  mle (fun u => C (f u)) X

theorem eval_mlePolynomial {n : ℕ} (f : Cube n → F) (r : Fin n → F) :
    eval r (mlePolynomial f) = mle f r := by
  classical
  simp [mlePolynomial, mle, innerProduct, eqWeight, map_sum, map_prod, apply_ite]

theorem mlePolynomial_degree {n : ℕ} (f : Cube n → F) :
    (mlePolynomial f).totalDegree ≤ n := by
  classical
  unfold mlePolynomial mle innerProduct
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro u _
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, add_zero]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases h : u i
      · simp [h]
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        exact (totalDegree_sub _ _).trans (by simp)
    _ = n := by simp

theorem mlePolynomial_injective (n : ℕ) :
    Function.Injective (mlePolynomial (F := F) (n := n)) := by
  intro f g h
  funext u
  have he := congrArg (eval (fun i => if u i then 1 else 0)) h
  simpa only [eval_mlePolynomial, mle_boolean] using he

variable [Fintype F] [DecidableEq F]

/-- Schwartz-Zippel for actual multilinear evaluations, including zero variables. -/
theorem mle_collision_probability {n : ℕ} (f g : Cube n → F) (hne : f ≠ g) :
    Soundness.uniformProb (Finset.univ.filter fun r => mle f r = mle g r) ≤
      (n : ℚ) / Fintype.card F := by
  classical
  have hp : mlePolynomial f - mlePolynomial g ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (mlePolynomial_injective n h))
  have hd : (mlePolynomial f - mlePolynomial g).totalDegree ≤ n :=
    (totalDegree_sub _ _).trans (max_le (mlePolynomial_degree f) (mlePolynomial_degree g))
  have hs := schwartz_zippel_totalDegree hp (Finset.univ : Finset F)
  simp [eval_sub, eval_mlePolynomial, sub_eq_zero] at hs
  have hs' :
      ((Finset.univ.filter fun r => mle f r = mle g r).card : ℚ) /
        (Fintype.card F : ℚ)^n ≤
      ((mlePolynomial f - mlePolynomial g).totalDegree : ℚ) / Fintype.card F := by
    exact_mod_cast hs
  unfold Soundness.uniformProb
  simpa [Fintype.card_fun] using hs'.trans
    (div_le_div_of_nonneg_right (by exact_mod_cast hd) (by positivity))

/-- Exact integer Schwartz-Zippel count, without division or a nonzero-dimension
side condition. -/
theorem mle_collision_count {n : ℕ} (f g : Cube n → F) (hne : f ≠ g) :
    (Finset.univ.filter fun r => mle f r = mle g r).card * Fintype.card F ≤
      n * Fintype.card (Fin n → F) := by
  have h := mle_collision_probability f g hne
  unfold Soundness.uniformProb at h
  have hq : (0 : ℚ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hr : (0 : ℚ) < Fintype.card (Fin n → F) := by exact_mod_cast Fintype.card_pos
  exact_mod_cast (div_le_div_iff₀ hr hq).mp h

/-- A fixed finite candidate list fails OOD separation with probability at most
`choose L 2 * n / |F|`; unordered pairs are charged once, not twice. -/
theorem candidate_separation {n : ℕ} (list : Finset (Cube n → F)) :
    Soundness.uniformProb (Finset.univ.filter fun r =>
      ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧ mle f r = mle g r) ≤
      (list.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card F) := by
  classical
  let events : ↥(list.powersetCard 2) → Finset (Fin n → F) := fun p =>
    Finset.univ.filter fun r =>
      ∃ f ∈ p.val, ∃ g ∈ p.val, f ≠ g ∧ mle f r = mle g r
  have cover : (Finset.univ.filter fun r =>
      ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧ mle f r = mle g r) ⊆
      Finset.univ.biUnion events := by
    intro r hr
    obtain ⟨f, hf, g, hg, hne, he⟩ := (Finset.mem_filter.mp hr).2
    have hp : ({f, g} : Finset (Cube n → F)) ∈ list.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨by
        intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hf
        · exact (Finset.mem_singleton.mp ha) ▸ hg,
        Finset.card_pair hne⟩
    exact Finset.mem_biUnion.mpr ⟨⟨{f, g}, hp⟩, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, f, by simp, g, by simp, hne, he⟩⟩
  have each (p : ↥(list.powersetCard 2)) :
      Soundness.uniformProb (events p) ≤ (n : ℚ) / Fintype.card F := by
    obtain ⟨f, g, hne, hp⟩ :=
      Finset.card_eq_two.mp (Finset.mem_powersetCard.mp p.property).2
    have he : events p = Finset.univ.filter (fun r => mle f r = mle g r) := by
      ext r
      simp only [events, hp, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨a, ha, b, hb, hab, he⟩
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all [eq_comm]
      · intro h
        exact ⟨f, Or.inl rfl, g, Or.inr rfl, hne, h⟩
    rw [he]
    exact mle_collision_probability f g hne
  calc
    _ ≤ Soundness.uniformProb (Finset.univ.biUnion events) := by
      unfold Soundness.uniformProb
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card cover)
        (by positivity)
    _ ≤ ∑ p, Soundness.uniformProb (events p) := Soundness.union_bound events
    _ ≤ ∑ _p : ↥(list.powersetCard 2), (n : ℚ) / Fintype.card F :=
      Finset.sum_le_sum fun p _ => each p
    _ = _ := by simp [Finset.card_powersetCard]

/-- Coefficient-table decoding preserves the candidate count when injective. -/
theorem decoded_candidate_separation {M : Type*} {n : ℕ} (list : Finset M)
    (decode : M → Cube n → F) (hinj : Function.Injective decode) :
    Soundness.uniformProb (Finset.univ.filter fun r =>
      ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧ mle (decode f) r = mle (decode g) r) ≤
      (list.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card F) := by
  classical
  have h := candidate_separation (list.image decode)
  have he : (Finset.univ.filter fun r =>
      ∃ f ∈ list.image decode, ∃ g ∈ list.image decode,
        f ≠ g ∧ mle f r = mle g r) =
      (Finset.univ.filter fun r =>
        ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧ mle (decode f) r = mle (decode g) r) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, _, ⟨g, hg, rfl⟩, hne, he⟩
      exact ⟨f, hf, g, hg, fun h => hne (congrArg decode h), he⟩
    · rintro ⟨f, hf, g, hg, hne, he⟩
      exact ⟨decode f, ⟨f, hf, rfl⟩, decode g, ⟨g, hg, rfl⟩,
        fun h => hne (hinj h), he⟩
  rw [he, Finset.card_image_of_injective _ hinj] at h
  exact h

/-- A single commitment-fixed candidate construction simultaneously provides the
Johnson list bound and OOD separation. Neither strategies nor challenge tapes
are arguments to the candidate construction. -/
theorem committed_candidates_bounds {M X A : Type*} [Fintype M] [Fintype X]
    {n : ℕ} (encode : M → X → A) (oracle : X → A) (t d : ℕ)
    (decode : M → Cube n → F) (hinj : Function.Injective decode)
    (hd : d ≤ Fintype.card X)
    (pairwise : ∀ i j, i ≠ j →
      CodingBounds.agreement (encode i) (encode j) ≤ d)
    (threshold : (Fintype.card X : ℚ) * d < (t : ℚ)^2) :
    let list := CodingBounds.candidates encode oracle t
    (list.card : ℚ) ≤ (Fintype.card X * (Fintype.card X - (d : ℚ))) /
      ((t : ℚ)^2 - Fintype.card X * d) ∧
    Soundness.uniformProb (Finset.univ.filter fun r =>
      ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧ mle (decode f) r = mle (decode g) r) ≤
      (list.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card F) := by
  classical
  exact ⟨CodingBounds.candidates_card encode oracle t d hd pairwise threshold,
    decoded_candidate_separation _ decode hinj⟩

/-- Reindex the actual coefficient table as a Boolean-cube message. The supplied
equivalence records the layout, rather than assuming decoding injective. -/
def decodeCoefficients {n lanes k : ℕ} (index : Cube n ≃ (Fin lanes × Fin k))
    (v : Fin lanes → Fin k → F) : Cube n → F :=
  fun u => v (index u).1 (index u).2

omit [Field F] [Fintype F] [DecidableEq F] in
theorem decodeCoefficients_injective {n lanes k : ℕ}
    (index : Cube n ≃ (Fin lanes × Fin k)) :
    Function.Injective (decodeCoefficients (F := F) index) := by
  intro u v h
  funext j i
  have he := congrFun h (index.symm (j, i))
  simpa [decodeCoefficients] using he

/-- RS/interleaved PCS coding and OOD endpoint: both bounds follow from the
encoder, root bound, and existing MLE definitions. There are no incidence,
list-size, decoding-injectivity, or OOD hypotheses. -/
theorem interleaved_committed_bounds {n lanes k : ℕ}
    (index : Cube n ≃ (Fin lanes × Fin k))
    (domain : Finset F) (oracle : ↥domain → Fin lanes → F) (t : ℕ)
    (hk : 0 < k) (hd : k - 1 ≤ domain.card)
    (threshold : (domain.card : ℚ) * (k - 1 : ℕ) < (t : ℚ)^2) :
    let list := CodingBounds.candidates
      (fun v : Fin lanes → Fin k → F =>
        fun x : ↥domain => CodingBounds.interleavedEncode v x) oracle t
    (list.card : ℚ) ≤ (domain.card * (domain.card - (k - 1 : ℕ) : ℚ)) /
      ((t : ℚ)^2 - domain.card * (k - 1 : ℕ)) ∧
    Soundness.uniformProb (Finset.univ.filter fun r =>
      ∃ f ∈ list, ∃ g ∈ list, f ≠ g ∧
        mle (decodeCoefficients index f) r = mle (decodeCoefficients index g) r) ≤
      (list.card.choose 2 : ℚ) * ((n : ℚ) / Fintype.card F) := by
  simpa using committed_candidates_bounds
    (fun v : Fin lanes → Fin k → F =>
      fun x : ↥domain => CodingBounds.interleavedEncode v x)
    oracle t (k - 1) (decodeCoefficients index) (decodeCoefficients_injective index)
    (by simpa using hd)
    (fun u v hne => CodingBounds.interleaved_domain_agreement domain u v hne hk)
    (by simpa using threshold)

end Whir.OODBounds
