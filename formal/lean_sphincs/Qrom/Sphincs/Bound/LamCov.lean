module

public import Qrom.Sphincs.Bound.Cover

@[expose] public section

/-!
# Counting covered digests

A digest at index `t` is covered by the presampled digests when each of its leaves is one that a
presampled digest at `t` opens, so the covered digests are a fraction at most `∑_t c_t^k / (2^h 2^(k a))`
of all, with `c_t` the number of presampled digests at `t`. The average of `c_t^k` over the presampled
digests is the `k`-th moment of a binomial count, at most `∑_j S(k, j) (N / 2^h)^j` for `N` signatures
with `S` the Stirling numbers of the second kind (`Qrom.Sphincs.sum_pow_card_image`), so such
averages are at most `lamS = ∑_j S(k, j) (N / 2^h)^j / 2^(k a)` (`Qrom.Sphincs.avg_le_lamS`).
-/

open OracleComp OracleSpec FORS FORS.Security Concrete Quantum
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace Qrom.Sphincs

variable [Params]

/-! ## Counting digest views -/

/-- The digest calls, as the digest's view and the bits it drops. -/
def viewEquiv : DigV ≃ FullDigestView × (DroppedBit → Bool) :=
  (Equiv.ofBijective splitCalls splitCalls_bijective).trans
    (Equiv.prodCongr (Equiv.ofBijective fullDigestView fullDigestView_bijective)
      (Equiv.refl (DroppedBit → Bool)))

theorem viewEquiv_fst (v : DigV) : (viewEquiv v).1 = fullDigestView (truncateMessageDigest v) := rfl

/-- A property of the view holds on a fraction of the digest calls equal to its fraction of the
views. -/
theorem card_view_filter (R : FullDigestView → Prop) [DecidablePred R] :
    (Finset.univ.filter fun v : DigV ↦ R (fullDigestView (truncateMessageDigest v))).card *
      Fintype.card FullDigestView = Fintype.card DigV * (Finset.univ.filter R).card := by
  have h1 : (Finset.univ.filter fun v : DigV ↦ R (fullDigestView (truncateMessageDigest v))).card =
      (Finset.univ.filter R).card * Fintype.card (DroppedBit → Bool) := by
    rw [Finset.card_filter, Finset.card_filter,
      Fintype.sum_equiv viewEquiv _ (fun p : FullDigestView × (DroppedBit → Bool) ↦ if R p.1 then 1 else 0)
        (fun v ↦ by rw [viewEquiv_fst]),
      Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    show (∑ _y : DroppedBit → Bool, if R w then 1 else 0) = _
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have h2 : Fintype.card DigV = Fintype.card FullDigestView * Fintype.card (DroppedBit → Bool) := by
    rw [Fintype.card_congr viewEquiv, Fintype.card_prod]
  rw [h1, h2]
  ring

/-- A digest lands at a given index for a fraction `2^-h` of the digest calls. -/
theorem card_index_eq (t : Index) :
    (Finset.univ.filter fun v : DigV ↦ digestIndex (truncateMessageDigest v) = t).card *
      Fintype.card Index = Fintype.card DigV := by
  have h := card_view_filter (fun w ↦ w.1 = t)
  have hc : (Finset.univ.filter fun w : FullDigestView ↦ w.1 = t).card =
      Fintype.card (FTree → FLeaf) := by
    rw [show (Finset.univ.filter fun w : FullDigestView ↦ w.1 = t) =
        ({t} : Finset Index) ×ˢ (Finset.univ : Finset (FTree → FLeaf)) from by
      ext w; simp; exact ⟨fun h ↦ ⟨w.2, by rw [← h]⟩, fun ⟨a, ha⟩ ↦ by rw [← ha]⟩, Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_univ]
  rw [hc, Fintype.card_prod] at h
  have hpos : 0 < Fintype.card (FTree → FLeaf) := Fintype.card_pos
  have h' : (Finset.univ.filter fun v : DigV ↦ digestIndex (truncateMessageDigest v) = t).card *
      Fintype.card Index * Fintype.card (FTree → FLeaf) =
      Fintype.card DigV * Fintype.card (FTree → FLeaf) := by
    rw [mul_assoc, ← h]
    rfl
  exact Nat.eq_of_mul_eq_mul_right hpos h'

/-! ## Tuples with few distinct entries -/

/-- The tuples with `j` distinct entries number at most `S(k, j) q^j`. -/
theorem card_image_eq_le (q : ℕ) : ∀ k j : ℕ,
    (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card = j).card ≤
      Nat.stirlingSecond k j * q ^ j
  | 0, j => by
    cases j with
    | zero => simp
    | succ j => simp
  | k + 1, j => by
    rw [Finset.card_filter, ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (k + 1) ↦ Fin q),
      Fintype.sum_prod_type, Finset.sum_comm]
    have himg : ∀ (v : Fin q) (f : Fin k → Fin q), Finset.univ.image (Fin.cons v f : Fin (k + 1) → Fin q) =
        insert v (Finset.univ.image f) := by
      intro v f
      ext w
      simp [Fin.exists_fin_succ, eq_comm]
    have hc : ∀ v f, (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin q)) (v, f) = Fin.cons v f := fun _ _ ↦ rfl
    simp only [hc, himg]
    have hstep : ∀ S : Finset (Fin q), ∑ v : Fin q, (if (insert v S).card = j then 1 else 0) ≤
        j * (if S.card = j then 1 else 0) + q * (if S.card + 1 = j then 1 else 0) := by
      intro S
      have hpt : ∀ v, (if (insert v S).card = j then 1 else 0) =
          if v ∈ S then (if S.card = j then 1 else 0) else (if S.card + 1 = j then 1 else 0) := by
        intro v
        by_cases hv : v ∈ S
        · simp [hv]
        · simp [hv, Finset.card_insert_of_notMem hv]
      rw [Finset.sum_congr rfl fun v _ ↦ hpt v, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
        smul_eq_mul, smul_eq_mul]
      have h1 : (Finset.univ.filter fun v ↦ v ∈ S) = S := by ext; simp
      have h2 : (Finset.univ.filter fun v ↦ v ∉ S).card ≤ q :=
        (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_fin])
      have h3 : S.card * (if S.card = j then 1 else 0) = j * (if S.card = j then 1 else 0) := by
        split_ifs with h <;> simp [h]
      rw [h1, h3]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h2) _
    calc ∑ f : Fin k → Fin q, ∑ v : Fin q, (if (insert v (Finset.univ.image f)).card = j then 1 else 0)
        ≤ ∑ f : Fin k → Fin q, (j * (if (Finset.univ.image f).card = j then 1 else 0) +
            q * (if (Finset.univ.image f).card + 1 = j then 1 else 0)) :=
          Finset.sum_le_sum fun f _ ↦ hstep _
      _ = j * (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card = j).card +
            q * (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card + 1 = j).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.card_filter,
            Finset.card_filter]
      _ ≤ _ := by
          cases j with
          | zero => simp
          | succ j =>
            have he : (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card + 1 = j + 1) =
                Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card = j := by
              ext f; simp
            rw [he, Nat.stirlingSecond_succ_succ]
            calc (j + 1) * (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card = j + 1).card +
                  q * (Finset.univ.filter fun f : Fin k → Fin q ↦ (Finset.univ.image f).card = j).card ≤
                (j + 1) * (Nat.stirlingSecond k (j + 1) * q ^ (j + 1)) + q * (Nat.stirlingSecond k j * q ^ j) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ (card_image_eq_le q k (j + 1)))
                    (Nat.mul_le_mul_left _ (card_image_eq_le q k j))
              _ = _ := by ring

/-- The `k`-th moment of the number of hits: `∑_f x^|im f| ≤ ∑_j S(k, j) (q x)^j`. -/
theorem sum_pow_card_image (q : ℕ) {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ∑ f : Fin k → Fin q, x ^ (Finset.univ.image f).card ≤
      ∑ j ∈ Finset.range (k + 1), ((Nat.stirlingSecond k j * q ^ j : ℕ) : ℝ) * x ^ j := by
  have hmap : ∀ f ∈ (Finset.univ : Finset (Fin k → Fin q)), (Finset.univ.image f).card ∈ Finset.range (k + 1) := by
    intro f _
    have := Finset.card_image_le (s := Finset.univ) (f := f)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le this)
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_le_sum fun j _ ↦ ?_
  rw [Finset.sum_congr rfl fun f hf ↦ by rw [(Finset.mem_filter.mp hf).2], Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_image_eq_le q k j) (pow_nonneg hx _)

/-- Row `k` of the Stirling numbers of the second kind, computed row by row. -/
def stirRow : ℕ → List ℕ
  | 0 => [1]
  | k + 1 => let r := stirRow k
    (List.range (k + 2)).map fun j ↦ j * r.getD j 0 + if j = 0 then 0 else r.getD (j - 1) 0

theorem stirRow_getD : ∀ k j : ℕ, (stirRow k).getD j 0 = Nat.stirlingSecond k j
  | 0, j => by cases j <;> simp [stirRow]
  | k + 1, j => by
    by_cases hj : j < k + 2
    · rw [stirRow, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
      cases j with
      | zero => simp
      | succ j =>
        show (j + 1) * (stirRow k).getD (j + 1) 0 +
          (if j + 1 = 0 then 0 else (stirRow k).getD (j + 1 - 1) 0) = _
        rw [stirRow_getD, ite_eq_right (Nat.succ_ne_zero j), Nat.add_sub_cancel, stirRow_getD,
          Nat.stirlingSecond_succ_succ]
    · rw [Nat.stirlingSecond_eq_zero_of_lt (by omega),
        List.getD_eq_default _ _ (by rw [stirRow, List.length_map, List.length_range]; omega)]

/-! ## The bound -/

/-- The index of the digest of some digest call outputs. -/
abbrev idxD (v : DigV) : Index := digestIndex (truncateMessageDigest v)

/-- The number of presampled digests at the index `t`. -/
def cnt (δ : Fin signatureLimit → DigV) (t : Index) : ℕ :=
  (Finset.univ.filter fun i ↦ idxD (δ i) = t).card

/-- **The cover bound**: `∑_j S(k, j) (N / 2^h)^j / 2^(k a)`, as a quotient of naturals. -/
def lamS : ℝ :=
  ((∑ j ∈ Finset.range (forsTrees + 1),
      Nat.stirlingSecond forsTrees j * signatureLimit ^ j * Fintype.card Index ^ (forsTrees - j) : ℕ) : ℝ) /
    ((Fintype.card (FTree → FLeaf) * Fintype.card Index ^ forsTrees : ℕ) : ℝ)

theorem card_leavesAll_le (δ : Fin signatureLimit → DigV) (t : Index) (κ : FTree) :
    (leavesAll δ t κ).card ≤ cnt δ t := by
  classical
  refine (Finset.card_le_card fun leaf hl ↦ ?_).trans
    (Finset.card_image_le (s := Finset.univ.filter fun i ↦ idxD (δ i) = t)
      (f := fun i ↦ digestLeaves (truncateMessageDigest (δ i)) κ))
  simp only [leavesAll, Finset.mem_filter, Finset.mem_univ, true_and] at hl
  obtain ⟨i, hi, hk⟩ := hl
  exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hk⟩

/-- The presampled digests that put the digests of a tuple's signatures at `t`. -/
theorem card_tuple_at (f : FTree → Fin signatureLimit) (t : Index) :
    ((Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ κ, idxD (δ (f κ)) = t).card : ℝ) =
      (Fintype.card DigV : ℝ) ^ signatureLimit *
        ((Fintype.card Index : ℝ)⁻¹) ^ (Finset.univ.image f).card := by
  classical
  set S : Fin signatureLimit → Finset DigV := fun i ↦
    if i ∈ Finset.univ.image f then Finset.univ.filter fun v ↦ idxD v = t else Finset.univ
  have hset : (Finset.univ.filter fun δ : Fin signatureLimit → DigV ↦ ∀ κ, idxD (δ (f κ)) = t) =
      Fintype.piFinset S := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, S]
    constructor
    · intro h i
      split_ifs with hi
      · obtain ⟨κ, -, rfl⟩ := Finset.mem_image.mp hi
        simpa using h κ
      · exact Finset.mem_univ _
    · intro h κ
      have := h (f κ)
      rw [ite_eq_left (Finset.mem_image_of_mem f (Finset.mem_univ κ))] at this
      simpa using this
  have hI : (0 : ℝ) < Fintype.card Index := by exact_mod_cast Fintype.card_pos
  have hn : ((Finset.univ.filter fun v : DigV ↦ idxD v = t).card : ℝ) =
      Fintype.card DigV * (Fintype.card Index : ℝ)⁻¹ := by
    have h := card_index_eq t
    rw [eq_mul_inv_iff_mul_eq₀ hI.ne']
    exact_mod_cast h
  rw [hset, Fintype.card_piFinset]
  push_cast
  have hS : ∀ i, ((S i).card : ℝ) = Fintype.card DigV *
      (if i ∈ Finset.univ.image f then (Fintype.card Index : ℝ)⁻¹ else 1) := by
    intro i
    simp only [S]
    split_ifs
    · exact hn
    · rw [Finset.card_univ, mul_one]
  rw [Finset.prod_congr rfl fun i _ ↦ hS i, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **An average of fractions below the `k`-th powers of the counts is at most `lamS`.** -/
theorem avg_le_lamS (r : (Fin signatureLimit → DigV) → ℝ) (hr : ∀ δ, 0 ≤ r δ)
    (hle : ∀ δ, r δ ≤ ∑ t, (cnt δ t : ℝ) ^ forsTrees /
      (Fintype.card Index * Fintype.card (FTree → FLeaf))) :
    (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)⁻¹ * ∑ δ, ENNReal.ofReal (r δ) ≤
      ENNReal.ofReal lamS := by
  set cΔ := (Fintype.card (Fin signatureLimit → DigV) : ℝ)
  have hΔ : 0 < cΔ := Nat.cast_pos.mpr Fintype.card_pos
  have hcΔ : cΔ = (Fintype.card DigV : ℝ) ^ signatureLimit := by
    simp only [cΔ, Fintype.card_fun, Fintype.card_fin]; push_cast; ring
  have hlam : (Fintype.card (Fin signatureLimit → DigV) : ℝ≥0∞)⁻¹ * ∑ δ, ENNReal.ofReal (r δ) =
      ENNReal.ofReal (cΔ⁻¹ * ∑ δ, r δ) := by
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hΔ.le), ENNReal.ofReal_inv_of_pos hΔ,
      ENNReal.ofReal_sum_of_nonneg fun δ _ ↦ hr δ]
    simp only [cΔ, ENNReal.ofReal_natCast]
  rw [hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  set F := (Fintype.card (FTree → FLeaf) : ℝ)
  set I := (Fintype.card Index : ℝ)
  have hF : 0 < F := Nat.cast_pos.mpr Fintype.card_pos
  have hI : 0 < I := Nat.cast_pos.mpr Fintype.card_pos
  -- the `k`-th power of a count counts the tuples of signatures there
  have hpow : ∀ δ t, (cnt δ t : ℝ) ^ forsTrees =
      ((Finset.univ.filter fun f : FTree → Fin signatureLimit ↦ ∀ κ, idxD (δ (f κ)) = t).card : ℝ) := by
    intro δ t
    classical
    have : (Finset.univ.filter fun f : FTree → Fin signatureLimit ↦ ∀ κ, idxD (δ (f κ)) = t) =
        Fintype.piFinset fun _ : FTree ↦ Finset.univ.filter fun i ↦ idxD (δ i) = t := by
      ext f; simp [Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, cnt]
    push_cast; ring
  have hswap : ∀ t, ∑ δ : Fin signatureLimit → DigV, (cnt δ t : ℝ) ^ forsTrees =
      ∑ f : FTree → Fin signatureLimit, cΔ * I⁻¹ ^ (Finset.univ.image f).card := by
    intro t
    simp only [hpow, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ ↦ ?_
    have h := card_tuple_at f t
    rw [Finset.card_filter] at h
    push_cast at h
    rw [h, hcΔ]
  set C : ℝ := (I * F)⁻¹
  have hC : 0 ≤ C := by positivity
  calc cΔ⁻¹ * ∑ δ, r δ ≤ cΔ⁻¹ * ∑ δ, ∑ t, (cnt δ t : ℝ) ^ forsTrees / (I * F) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun δ _ ↦ hle δ) (inv_nonneg.mpr hΔ.le)
    _ = C * ∑ t : Index, (cΔ⁻¹ * ∑ δ, (cnt δ t : ℝ) ^ forsTrees) := by
        rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun δ _ ↦ ?_
        simp only [C]
        ring
    _ = C * (I * ∑ f : FTree → Fin signatureLimit, I⁻¹ ^ (Finset.univ.image f).card) := by
        simp only [hswap]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← mul_assoc cΔ⁻¹,
          inv_mul_cancel₀ hΔ.ne', one_mul]
    _ ≤ C * (I * ∑ j ∈ Finset.range (forsTrees + 1),
          ((Nat.stirlingSecond forsTrees j * signatureLimit ^ j : ℕ) : ℝ) * I⁻¹ ^ j) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hI.le) hC
        exact sum_pow_card_image signatureLimit (inv_nonneg.mpr hI.le) forsTrees
    _ = lamS := by
        rw [lamS]
        push_cast
        have hterm : ∀ j ∈ Finset.range (forsTrees + 1),
            (Nat.stirlingSecond forsTrees j : ℝ) * (signatureLimit : ℝ) ^ j * I ^ (forsTrees - j) =
              I ^ forsTrees * ((Nat.stirlingSecond forsTrees j : ℝ) * (signatureLimit : ℝ) ^ j * I⁻¹ ^ j) := by
          intro j hj
          rw [pow_sub₀ _ hI.ne' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), inv_pow]
          ring
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
        simp only [C, F, I]
        field_simp

/-- `lamS` is at most `a 2^-b` when the naturals say so. -/
theorem lamS_le {a b : ℕ} (hn : (∑ j ∈ Finset.range (forsTrees + 1),
      Nat.stirlingSecond forsTrees j * signatureLimit ^ j * Fintype.card Index ^ (forsTrees - j)) * 2 ^ b ≤
      a * (Fintype.card (FTree → FLeaf) * Fintype.card Index ^ forsTrees)) :
    lamS ≤ a * (2 : ℝ)⁻¹ ^ b := by
  have hd : (0 : ℝ) < ((Fintype.card (FTree → FLeaf) * Fintype.card Index ^ forsTrees : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.mul_pos Fintype.card_pos (Nat.pow_pos Fintype.card_pos))
  unfold lamS
  rw [div_le_iff₀ hd, inv_pow, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact_mod_cast hn

end Qrom.Sphincs
