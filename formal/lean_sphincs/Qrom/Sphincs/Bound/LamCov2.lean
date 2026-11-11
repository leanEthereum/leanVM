module

public import Qrom.Sphincs.Bound.LamCov

@[expose] public section

/-!
# The second moment of the covered fraction

The square of `Λ(δ) = ∑_t c_t^k / (2^h 2^(k a))` counts pairs of `k`-tuples of signatures, the
first all at an index `t` and the second all at an index `t'`. Pairs at one index are `2k`-tuples
all at that index, whose average count is the `2k`-th moment; pairs at two distinct indices have
disjoint signatures, which the presampled digests place independently. So the average of `Λ(δ)²` is
at most `lamS² + lamS2`, with `lamS2 = ∑_j S(2k, j) N^j 2^(h (2k - j)) / (2^(2 k a) 2^(h (2k + 1)))`
(`Qrom.Sphincs.avg_sq_le`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-- The presampled digests putting a set of signatures at prescribed indices. -/
theorem card_at (A : Finset (Fin signatureLimit)) (τ : Fin signatureLimit → Index) :
    ((Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ i ∈ A, idxD (δ i) = τ i).card : ℝ) =
      (Fintype.card DigV : ℝ) ^ signatureLimit * ((Fintype.card Index : ℝ)⁻¹) ^ A.card := by
  classical
  set S : Fin signatureLimit → Finset DigV := fun i ↦
    if i ∈ A then Finset.univ.filter fun v ↦ idxD v = τ i else Finset.univ
  have hset : (Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ i ∈ A, idxD (δ i) = τ i) =
      Fintype.piFinset S := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, S]
    constructor
    · intro h i
      split_ifs with hi
      · simpa using h i hi
      · exact Finset.mem_univ _
    · intro h i hi
      have := h i
      rw [ite_eq_left hi] at this
      simpa using this
  have hI : (0 : ℝ) < Fintype.card Index := by exact_mod_cast Fintype.card_pos
  have hS : ∀ i, ((S i).card : ℝ) = Fintype.card DigV *
      (if i ∈ A then (Fintype.card Index : ℝ)⁻¹ else 1) := by
    intro i
    simp only [S]
    split_ifs
    · have h := card_index_eq (τ i)
      rw [eq_mul_inv_iff_mul_eq₀ hI.ne']
      exact_mod_cast h
    · rw [Finset.card_univ, mul_one]
  rw [hset, Fintype.card_piFinset]
  push_cast
  rw [Finset.prod_congr rfl fun i _ ↦ hS i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Two tuples of signatures at two indices: at most the count at one index when they are equal,
the product of the counts when they are not. -/
theorem card_pair_le (f f' : FTree → Fin signatureLimit) (t t' : Index) :
    ((Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦
        (∀ κ, idxD (δ (f κ)) = t) ∧ ∀ κ, idxD (δ (f' κ)) = t').card : ℝ) ≤
      if t = t' then (Fintype.card DigV : ℝ) ^ signatureLimit *
          ((Fintype.card Index : ℝ)⁻¹) ^ (Finset.univ.image f ∪ Finset.univ.image f').card
        else (Fintype.card DigV : ℝ) ^ signatureLimit *
          ((Fintype.card Index : ℝ)⁻¹) ^ (Finset.univ.image f).card *
          ((Fintype.card Index : ℝ)⁻¹) ^ (Finset.univ.image f').card := by
  classical
  have hI : (0 : ℝ) < Fintype.card Index := by exact_mod_cast Fintype.card_pos
  split_ifs with htt
  · subst htt
    rw [← card_at (Finset.univ.image f ∪ Finset.univ.image f') fun _ ↦ t]
    refine le_of_eq (congrArg _ (congrArg _ ?_))
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩ i (⟨κ, rfl⟩ | ⟨κ, rfl⟩)
      · exact h1 κ
      · exact h2 κ
    · intro h
      exact ⟨fun κ ↦ h _ (Or.inl ⟨κ, rfl⟩), fun κ ↦ h _ (Or.inr ⟨κ, rfl⟩)⟩
  · by_cases hdis : Disjoint (Finset.univ.image f) (Finset.univ.image f')
    · rw [mul_assoc, ← pow_add, ← Finset.card_union_of_disjoint hdis,
        ← card_at (Finset.univ.image f ∪ Finset.univ.image f')
          fun i ↦ if i ∈ Finset.univ.image f then t else t']
      refine le_of_eq (congrArg _ (congrArg _ ?_))
      ext δ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · rintro ⟨h1, h2⟩ i (hi | hi)
        · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi
          rw [ite_eq_left hi]
          exact h1 κ
        · have hn : i ∉ Finset.univ.image f := fun h ↦ Finset.disjoint_left.mp hdis h hi
          obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi
          rw [ite_eq_right hn]
          exact h2 κ
      · intro h
        refine ⟨fun κ ↦ ?_, fun κ ↦ ?_⟩
        · have hi : f κ ∈ Finset.univ.image f := Finset.mem_image_of_mem f (Finset.mem_univ κ)
          have := h (f κ) (Or.inl hi)
          rwa [ite_eq_left hi] at this
        · have hi : f' κ ∈ Finset.univ.image f' := Finset.mem_image_of_mem f' (Finset.mem_univ κ)
          have hn : f' κ ∉ Finset.univ.image f := fun h ↦ Finset.disjoint_left.mp hdis h hi
          have := h (f' κ) (Or.inr hi)
          rwa [ite_eq_right hn] at this
    · have hempty : (Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦
          (∀ κ, idxD (δ (f κ)) = t) ∧ ∀ κ, idxD (δ (f' κ)) = t') = ∅ := by
        rw [Finset.not_disjoint_iff] at hdis
        obtain ⟨i, hi, hi'⟩ := hdis
        obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨κ', -, hκ'⟩ := Finset.mem_image.mp hi'
        ext δ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro h1 h2
        have := h2 κ'
        rw [hκ', h1 κ] at this
        exact htt this
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      positivity

/-- Pairs of tuples as one tuple of twice the length. -/
def pairEquiv : (FTree → Fin signatureLimit) × (FTree → Fin signatureLimit) ≃
    (Fin (forsTrees + forsTrees) → Fin signatureLimit) :=
  (Equiv.sumArrowEquivProdArrow FTree FTree (Fin signatureLimit)).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))

theorem pairEquiv_apply (f f' : FTree → Fin signatureLimit) (a : FTree ⊕ FTree) :
    pairEquiv (f, f') (finSumFinEquiv a) = Sum.elim f f' a := by
  show (Equiv.sumArrowEquivProdArrow FTree FTree (Fin signatureLimit)).symm (f, f')
    (finSumFinEquiv.symm (finSumFinEquiv a)) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem image_pairEquiv (f f' : FTree → Fin signatureLimit) :
    Finset.univ.image (pairEquiv (f, f')) = Finset.univ.image f ∪ Finset.univ.image f' := by
  classical
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨j, rfl⟩
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective j
    rw [pairEquiv_apply]
    rcases a with a | a
    · exact Or.inl ⟨a, rfl⟩
    · exact Or.inr ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨finSumFinEquiv (Sum.inl a), by rw [pairEquiv_apply]; rfl⟩
    · exact ⟨finSumFinEquiv (Sum.inr a), by rw [pairEquiv_apply]; rfl⟩

/-- **The second-moment bound**, `∑_j S(2k, j) N^j 2^(h (2k - j)) / (2^(2 k a) 2^(h (2k + 1)))`. -/
def lamS2 : ℝ :=
  ((∑ j ∈ Finset.range (forsTrees + forsTrees + 1),
      Nat.stirlingSecond (forsTrees + forsTrees) j * signatureLimit ^ j *
        Fintype.card Index ^ (forsTrees + forsTrees - j) : ℕ) : ℝ) /
    ((Fintype.card (FTree → FLeaf) ^ 2 * Fintype.card Index ^ (forsTrees + forsTrees + 1) : ℕ) : ℝ)

theorem lamS2_nonneg : 0 ≤ lamS2 := by
  unfold lamS2
  positivity

/-- **The average of the squared fraction**, for fractions below `Λ(δ)`. -/
theorem avg_sq_le (r : (Fin signatureLimit → DigV) → ℝ) (hr : ∀ δ, 0 ≤ r δ)
    (hle : ∀ δ, r δ ≤ ∑ t, (cnt δ t : ℝ) ^ forsTrees /
      (Fintype.card Index * Fintype.card (FTree → FLeaf))) :
    (Fintype.card (Fin signatureLimit → DigV) : ℝ)⁻¹ * ∑ δ, r δ ^ 2 ≤ lamS ^ 2 + lamS2 := by
  classical
  set cΔ := (Fintype.card (Fin signatureLimit → DigV) : ℝ)
  have hΔ : 0 < cΔ := Nat.cast_pos.mpr Fintype.card_pos
  have hcΔ : cΔ = (Fintype.card DigV : ℝ) ^ signatureLimit := by
    simp only [cΔ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  set F := (Fintype.card (FTree → FLeaf) : ℝ)
  set I := (Fintype.card Index : ℝ)
  have hF : 0 < F := Nat.cast_pos.mpr Fintype.card_pos
  have hI : 0 < I := Nat.cast_pos.mpr Fintype.card_pos
  set k := forsTrees
  set M1 : ℝ := ∑ f : FTree → Fin signatureLimit, I⁻¹ ^ (Finset.univ.image f).card
  set M2 : ℝ := ∑ g : Fin (k + k) → Fin signatureLimit, I⁻¹ ^ (Finset.univ.image g).card
  have hM1 : 0 ≤ M1 := Finset.sum_nonneg fun _ _ ↦ by positivity
  -- the `k`-th power of a count counts the tuples of signatures there
  have hpow : ∀ δ t, (cnt δ t : ℝ) ^ k =
      ∑ f : FTree → Fin signatureLimit, if ∀ κ, idxD (δ (f κ)) = t then (1 : ℝ) else 0 := by
    intro δ t
    have : (Finset.univ.filter fun f : FTree → Fin signatureLimit ↦ ∀ κ, idxD (δ (f κ)) = t) =
        Fintype.piFinset fun _ : FTree ↦ Finset.univ.filter fun i ↦ idxD (δ i) = t := by
      ext f; simp [Fintype.mem_piFinset]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, this, Fintype.card_piFinset,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, cnt]
    push_cast; ring
  -- the pairs, over the presampled digests and the two indices
  have hpair : ∀ t t', ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k ≤
      ∑ f : FTree → Fin signatureLimit, ∑ f' : FTree → Fin signatureLimit,
        if t = t' then cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card
          else cΔ * I⁻¹ ^ (Finset.univ.image f).card * I⁻¹ ^ (Finset.univ.image f').card := by
    intro t t'
    simp only [hpow, Finset.sum_mul_sum, ite_mul, one_mul, zero_mul, ← ite_and]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun f' _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hcΔ]
    exact card_pair_le f f' t t'
  -- summed over the two indices
  have hpair' : ∑ t, ∑ t', ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k ≤
      cΔ * (I * M2 + (I * M1) ^ 2) := by
    calc ∑ t, ∑ t', ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k
        ≤ ∑ t : Index, ∑ t' : Index, ∑ f : FTree → Fin signatureLimit,
            ∑ f' : FTree → Fin signatureLimit,
              ((if t = t' then cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card else 0) +
                cΔ * I⁻¹ ^ (Finset.univ.image f).card * I⁻¹ ^ (Finset.univ.image f').card) := by
          refine Finset.sum_le_sum fun t _ ↦ Finset.sum_le_sum fun t' _ ↦ (hpair t t').trans ?_
          refine Finset.sum_le_sum fun f _ ↦ Finset.sum_le_sum fun f' _ ↦ ?_
          split_ifs
          · exact le_add_of_nonneg_right (by positivity)
          · rw [zero_add]
      _ = cΔ * (I * M2 + (I * M1) ^ 2) := by
          simp only [Finset.sum_add_distrib]
          have h1 : ∑ t : Index, ∑ t' : Index, ∑ f : FTree → Fin signatureLimit,
              ∑ f' : FTree → Fin signatureLimit,
                (if t = t' then cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card else 0) =
              cΔ * (I * M2) := by
            have e1 : ∀ t t' : Index, (∑ f : FTree → Fin signatureLimit,
                ∑ f' : FTree → Fin signatureLimit,
                  (if t = t' then cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card
                    else 0)) =
                if t = t' then ∑ f : FTree → Fin signatureLimit, ∑ f' : FTree → Fin signatureLimit,
                  cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card else 0 := by
              intro t t'
              split_ifs <;> simp
            rw [Finset.sum_congr rfl fun t _ ↦ Finset.sum_congr rfl fun t' _ ↦ e1 t t']
            simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
              Finset.card_univ, nsmul_eq_mul]
            have e2 : ∑ f : FTree → Fin signatureLimit, ∑ f' : FTree → Fin signatureLimit,
                cΔ * I⁻¹ ^ (Finset.univ.image f ∪ Finset.univ.image f').card = cΔ * M2 := by
              rw [← Fintype.sum_prod_type' (f := fun f f' ↦ cΔ * I⁻¹ ^
                (Finset.univ.image f ∪ Finset.univ.image f').card)]
              rw [← Equiv.sum_comp pairEquiv.symm (fun p : (FTree → Fin signatureLimit) ×
                (FTree → Fin signatureLimit) ↦ cΔ * I⁻¹ ^
                  (Finset.univ.image p.1 ∪ Finset.univ.image p.2).card)]
              simp only [M2, Finset.mul_sum]
              refine Finset.sum_congr rfl fun g _ ↦ ?_
              rw [← image_pairEquiv, Prod.mk.eta, Equiv.apply_symm_apply]
            rw [e2]
            simp only [I]
            ring
          have h2 : ∑ t : Index, ∑ t' : Index, ∑ f : FTree → Fin signatureLimit,
              ∑ f' : FTree → Fin signatureLimit,
                cΔ * I⁻¹ ^ (Finset.univ.image f).card * I⁻¹ ^ (Finset.univ.image f').card =
              cΔ * (I * M1) ^ 2 := by
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
              ← Finset.sum_mul, M1, I]
            ring
          rw [h1, h2]
          ring
  -- the average of `Λ(δ)²`
  have hsq : ∀ δ, r δ ^ 2 ≤ (I * F)⁻¹ ^ 2 * ∑ t, ∑ t', (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k := by
    intro δ
    have h := hle δ
    have h0 := hr δ
    calc r δ ^ 2 ≤ (∑ t, (cnt δ t : ℝ) ^ k / (I * F)) ^ 2 := pow_le_pow_left₀ h0 h 2
      _ = _ := by
          rw [← Finset.sum_div, div_pow, sq (∑ t, (cnt δ t : ℝ) ^ k), Finset.sum_mul_sum]
          ring
  have hM1le : M1 ≤ ∑ j ∈ Finset.range (k + 1),
      ((Nat.stirlingSecond k j * signatureLimit ^ j : ℕ) : ℝ) * I⁻¹ ^ j :=
    sum_pow_card_image signatureLimit (inv_nonneg.mpr hI.le) k
  have hM2le : M2 ≤ ∑ j ∈ Finset.range (k + k + 1),
      ((Nat.stirlingSecond (k + k) j * signatureLimit ^ j : ℕ) : ℝ) * I⁻¹ ^ j :=
    sum_pow_card_image signatureLimit (inv_nonneg.mpr hI.le) (k + k)
  -- `lamS = (I M1-bound) / (I F)` and `lamS2 = I M2-bound / (I F)²`
  have hlamS : (I * F)⁻¹ * (I * ∑ j ∈ Finset.range (k + 1),
      ((Nat.stirlingSecond k j * signatureLimit ^ j : ℕ) : ℝ) * I⁻¹ ^ j) = lamS := by
    rw [lamS]
    push_cast
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (Nat.stirlingSecond k j : ℝ) * (signatureLimit : ℝ) ^ j * I ^ (k - j) =
          I ^ k * ((Nat.stirlingSecond k j : ℝ) * (signatureLimit : ℝ) ^ j * I⁻¹ ^ j) := by
      intro j hj
      rw [pow_sub₀ _ hI.ne' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), inv_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    simp only [F, I, k]
    field_simp
  have hlamS2 : (I * F)⁻¹ ^ 2 * (I * ∑ j ∈ Finset.range (k + k + 1),
      ((Nat.stirlingSecond (k + k) j * signatureLimit ^ j : ℕ) : ℝ) * I⁻¹ ^ j) = lamS2 := by
    rw [lamS2]
    push_cast
    have hterm : ∀ j ∈ Finset.range (k + k + 1),
        (Nat.stirlingSecond (k + k) j : ℝ) * (signatureLimit : ℝ) ^ j * I ^ (k + k - j) =
          I ^ (k + k) * ((Nat.stirlingSecond (k + k) j : ℝ) * (signatureLimit : ℝ) ^ j * I⁻¹ ^ j) := by
      intro j hj
      rw [pow_sub₀ _ hI.ne' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), inv_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    simp only [F, I, k]
    field_simp
    ring
  calc cΔ⁻¹ * ∑ δ, r δ ^ 2
      ≤ cΔ⁻¹ * ∑ δ, (I * F)⁻¹ ^ 2 * ∑ t, ∑ t', (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun δ _ ↦ hsq δ) (inv_nonneg.mpr hΔ.le)
    _ = (I * F)⁻¹ ^ 2 * (cΔ⁻¹ * ∑ t, ∑ t', ∑ δ : Fin signatureLimit → DigV,
          (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k) := by
        have hc : ∑ δ : Fin signatureLimit → DigV, ∑ t, ∑ t',
            (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k =
            ∑ t, ∑ t', ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ k * (cnt δ t' : ℝ) ^ k := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun t _ ↦ Finset.sum_comm
        rw [← Finset.mul_sum, hc]
        ring
    _ ≤ (I * F)⁻¹ ^ 2 * (cΔ⁻¹ * (cΔ * (I * M2 + (I * M1) ^ 2))) := by
        gcongr
    _ = (I * F)⁻¹ ^ 2 * (I * M2) + ((I * F)⁻¹ * (I * M1)) ^ 2 := by
        rw [← mul_assoc cΔ⁻¹, inv_mul_cancel₀ hΔ.ne', one_mul]
        ring
    _ ≤ lamS2 + lamS ^ 2 := by
        rw [← hlamS, ← hlamS2]
        gcongr
    _ = lamS ^ 2 + lamS2 := add_comm _ _

/-- `lamS2` is at most `a 2^-b` when the naturals say so. -/
theorem lamS2_le {a b : ℕ} (hn : (∑ j ∈ Finset.range (forsTrees + forsTrees + 1),
      Nat.stirlingSecond (forsTrees + forsTrees) j * signatureLimit ^ j *
        Fintype.card Index ^ (forsTrees + forsTrees - j)) * 2 ^ b ≤
      a * (Fintype.card (FTree → FLeaf) ^ 2 * Fintype.card Index ^ (forsTrees + forsTrees + 1))) :
    lamS2 ≤ a * (2 : ℝ)⁻¹ ^ b := by
  have hd : (0 : ℝ) < ((Fintype.card (FTree → FLeaf) ^ 2 *
      Fintype.card Index ^ (forsTrees + forsTrees + 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos (Nat.pow_pos Fintype.card_pos) (Nat.pow_pos Fintype.card_pos))
  unfold lamS2
  rw [div_le_iff₀ hd, inv_pow, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact_mod_cast hn

end Qrom.Sphincs
