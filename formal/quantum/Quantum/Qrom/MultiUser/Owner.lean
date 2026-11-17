module

public import Quantum.Xmss.Hybrid.Seed

@[expose] public section

/-!
# Owners of inputs and multiplicities of public data

`n` users hold public data `P : Fin n → α` (leanXMSS: the public parameters); an input `x` carries
a prefix `pre x : Option α` (the public datum it is hashed under, if any).

* `ownerOf P pre x`: the least user whose datum is the prefix of `x`; with distinct data, the only
  one (`ownerOf_eq_some`).
* `mult P`: the largest number of users sharing a datum; `mult_le_one_iff`, `mult_eq_one_iff`:
  multiplicity one is distinct data. `collPairs P`: the colliding pairs `i < j`;
  `mult_le_one_add_card_collPairs`.
* For data `g ∘ f` with `f` uniform and every fiber of `g` of at most `c` points
  (`uavg_card_collPairs_le`): the expected number of colliding pairs is at most
  `C(n,2) · c / |β|`, hence `uavg_not_injective_le` (probability of a collision) and
  `uavg_mult_le` (`E mult ≤ 1 + C(n,2) · c / |β|`).
* `uavg_restrict_injective`: averaging over tables a function of the entries at injective
  positions averages over those entries.
-/

open scoped ENNReal

namespace Quantum.Qrom.MultiUser

open Quantum.Xmss.Hybrid (uavg uavg_mono uavg_add)

/-! ## Owners -/

section owner

variable {n : ℕ} {α D : Type} [DecidableEq α]

/-- **The owner of an input**: the least user whose public datum is the input's prefix. -/
def ownerOf (P : Fin n → α) (pre : D → Option α) (x : D) : Option (Fin n) :=
  (pre x).bind fun a ↦ if h : ∃ i, P i = a then some (Fin.find (fun i ↦ P i = a) h) else none

theorem prefix_of_ownerOf {P : Fin n → α} {pre : D → Option α} {x : D} {i : Fin n}
    (h : ownerOf P pre x = some i) : pre x = some (P i) := by
  unfold ownerOf at h
  cases hx : pre x with
  | none => rw [hx] at h; exact absurd h (by simp)
  | some a =>
    rw [hx, Option.bind_some] at h
    by_cases he : ∃ i, P i = a
    · rw [dite_eq_left he, Option.some.injEq] at h
      rw [← h, Fin.find_spec he]
    · rw [dite_eq_right he] at h
      exact absurd h (by simp)

/-- With distinct data, the owner of an input with prefix `P i` is `i`. -/
theorem ownerOf_eq_some {P : Fin n → α} (hP : Function.Injective P) {pre : D → Option α}
    {x : D} {i : Fin n} (h : pre x = some (P i)) : ownerOf P pre x = some i := by
  have he : ∃ j, P j = P i := ⟨i, rfl⟩
  unfold ownerOf
  rw [h, Option.bind_some, dite_eq_left he]
  exact congrArg some (hP (Fin.find_spec he))

theorem ownerOf_eq_none_iff {P : Fin n → α} {pre : D → Option α} {x : D} :
    ownerOf P pre x = none ↔ ∀ i, pre x ≠ some (P i) := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ ?_⟩
  · unfold ownerOf at h
    rw [hi, Option.bind_some, dite_eq_left ⟨i, rfl⟩] at h
    exact absurd h (by simp)
  · cases ho : ownerOf P pre x with
    | none => rfl
    | some i => exact absurd (prefix_of_ownerOf ho) (h i)

end owner

/-! ## Multiplicities and colliding pairs -/

section mult

variable {n : ℕ} {α : Type} [DecidableEq α]

/-- **The multiplicity of the data**: the largest number of users sharing a datum. -/
def mult (P : Fin n → α) : ℕ :=
  Finset.univ.sup fun i ↦ (Finset.univ.filter fun j ↦ P j = P i).card

/-- The colliding pairs `i < j`, `P i = P j`. -/
def collPairs (P : Fin n → α) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p ↦ p.1 < p.2 ∧ P p.1 = P p.2

/-- The users sharing any datum number at most the multiplicity. -/
theorem card_filter_eq_le_mult (P : Fin n → α) (a : α) :
    (Finset.univ.filter fun j ↦ P j = a).card ≤ mult P := by
  by_cases h : ∃ i, P i = a
  · obtain ⟨i, rfl⟩ := h
    exact Finset.le_sup (f := fun i ↦ (Finset.univ.filter fun j ↦ P j = P i).card)
      (Finset.mem_univ i)
  · push Not at h
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun j _ ↦ h j)]
    exact Nat.zero_le _

theorem mult_le_one_iff {P : Fin n → α} : mult P ≤ 1 ↔ Function.Injective P := by
  refine ⟨fun h i j hij ↦ ?_, fun h ↦ Finset.sup_le fun i _ ↦ ?_⟩
  · have hc := (card_filter_eq_le_mult P (P j)).trans h
    exact Finset.card_le_one.mp hc i (by simp [hij]) j (by simp)
  · refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact h (ha.trans hb.symm)

theorem one_le_mult {P : Fin n → α} (hn : 0 < n) : 1 ≤ mult P :=
  le_trans (Finset.card_pos.mpr ⟨⟨0, hn⟩, by simp⟩) (card_filter_eq_le_mult P (P ⟨0, hn⟩))

/-- **Multiplicity one is distinct data.** -/
theorem mult_eq_one_iff {P : Fin n → α} (hn : 0 < n) : mult P = 1 ↔ Function.Injective P :=
  ⟨fun h ↦ mult_le_one_iff.mp h.le, fun h ↦ le_antisymm (mult_le_one_iff.mpr h) (one_le_mult hn)⟩

/-- **The multiplicity is at most one plus the number of colliding pairs.** -/
theorem mult_le_one_add_card_collPairs (P : Fin n → α) : mult P ≤ 1 + (collPairs P).card := by
  refine Finset.sup_le fun i _ ↦ ?_
  have hsplit : (Finset.univ.filter fun j ↦ P j = P i) ⊆
      insert i (Finset.univ.filter fun j ↦ j ≠ i ∧ P j = P i) := fun j hj ↦ by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases hji : j = i
    · exact Finset.mem_insert.mpr (.inl hji)
    · exact Finset.mem_insert_of_mem (by simp [hji, hj])
  refine (Finset.card_le_card hsplit).trans ((Finset.card_insert_le _ _).trans ?_)
  rw [add_comm]
  refine Nat.add_le_add_left (Finset.card_le_card_of_injOn (fun j ↦ (min i j, max i j))
    (fun j hj ↦ ?_) (fun j hj k hk hjk ↦ ?_)) 1
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj
    simp only [collPairs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨min_lt_max.mpr (Ne.symm hj.1), ?_⟩
    rcases min_choice i j with h1 | h1 <;> rcases max_choice i j with h2 | h2 <;>
      simp only [h1, h2, hj.2]
  · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hj hk
    simp only [Prod.mk.injEq] at hjk
    rcases le_total i j with h1 | h1 <;> rcases le_total i k with h2 | h2
    · rw [max_eq_right h1, max_eq_right h2] at hjk; exact hjk.2
    · rw [max_eq_right h1, max_eq_left h2, min_eq_left h1, min_eq_right h2] at hjk
      exact absurd hjk.2 hj.1
    · rw [max_eq_left h1, max_eq_right h2, min_eq_right h1, min_eq_left h2] at hjk
      exact absurd hjk.1 hj.1
    · rw [min_eq_right h1, min_eq_right h2] at hjk; exact hjk.1

/-- A collision of the data gives a colliding pair. -/
theorem one_le_card_collPairs {P : Fin n → α} (h : ¬Function.Injective P) :
    1 ≤ (collPairs P).card := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  refine Finset.card_pos.mpr ?_
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact ⟨(i, j), by simp [collPairs, hlt, hij]⟩
  · exact ⟨(j, i), by simp [collPairs, hlt, hij]⟩

end mult

/-! ## Averages -/

section average

/-- The average of a function of the first factor of a product is its average. -/
theorem uavg_comp_fst' {A B : Type*} [Fintype A] [Fintype B] [Nonempty B] (g : A → ℝ≥0∞) :
    uavg (fun p : A × B ↦ g p.1) = uavg g := by
  have hB : (Fintype.card B : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold uavg
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_assoc, ← mul_assoc ((Fintype.card B : ℝ≥0∞)⁻¹),
    ENNReal.inv_mul_cancel hB (ENNReal.natCast_ne_top _), one_mul]

/-- **Restriction to injective positions**: averaging over tables `P → V` a function of the
entries at the injective positions `e` averages over those entries. -/
theorem uavg_restrict_injective {ι P V : Type*} [Fintype ι] [DecidableEq ι] [Fintype P]
    [DecidableEq P] [Fintype V] [Nonempty V] (e : ι → P) (he : Function.Injective e)
    (g : (ι → V) → ℝ≥0∞) :
    uavg (fun θ : P → V ↦ g fun i ↦ θ (e i)) = uavg g := by
  classical
  let Φ : (P → V) ≃ (ι → V) × ({p // p ∉ Set.range e} → V) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range e) fun _ ↦ V).trans
      (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective e he).symm (Equiv.refl V))
        (Equiv.refl _))
  have hΦ : ∀ θ, (Φ θ).1 = fun i ↦ θ (e i) := fun _ ↦ rfl
  calc uavg (fun θ : P → V ↦ g fun i ↦ θ (e i))
      = uavg (fun θ ↦ (fun p : (ι → V) × ({p // p ∉ Set.range e} → V) ↦ g p.1) (Φ θ)) := by
        simp only [hΦ]
    _ = uavg (fun p : (ι → V) × ({p // p ∉ Set.range e} → V) ↦ g p.1) := by
        unfold uavg
        rw [Fintype.card_congr Φ, Equiv.sum_comp Φ (fun p ↦ g p.1)]
    _ = uavg g := uavg_comp_fst' g

theorem uavg_finset_sum {Θ ι : Type*} [Fintype Θ] (s : Finset ι) (f : ι → Θ → ℝ≥0∞) :
    uavg (fun θ ↦ ∑ k ∈ s, f k θ) = ∑ k ∈ s, uavg (f k) := by
  unfold uavg
  rw [Finset.sum_comm, Finset.mul_sum]

variable {n : ℕ} {α β : Type} [DecidableEq α] [Fintype β] [Nonempty β] (g : β → α) {c : ℕ}
  (hc : ∀ a, (Finset.univ.filter fun b ↦ g b = a).card ≤ c)
include hc

/-- **One pair collides** with probability at most `c / |β|`. -/
theorem uavg_collide_le {i j : Fin n} (hij : i ≠ j) :
    uavg (fun f : Fin n → β ↦ if g (f i) = g (f j) then (1 : ℝ≥0∞) else 0) ≤
      c / Fintype.card β := by
  have he : Function.Injective ![i, j] := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [eq_comm]
  have hr : uavg (fun f : Fin n → β ↦ if g (f i) = g (f j) then (1 : ℝ≥0∞) else 0) =
      uavg (fun u : Fin 2 → β ↦ if g (u 0) = g (u 1) then (1 : ℝ≥0∞) else 0) :=
    uavg_restrict_injective ![i, j] he
      fun u : Fin 2 → β ↦ if g (u 0) = g (u 1) then (1 : ℝ≥0∞) else 0
  rw [hr]
  have hβ : (Fintype.card β : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hβt : (Fintype.card β : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑ u : Fin 2 → β, (if g (u 0) = g (u 1) then (1 : ℝ≥0∞) else 0) ≤
      Fintype.card β * c := by
    rw [← (finTwoArrowEquiv β).symm.sum_comp, Fintype.sum_prod_type_right]
    calc ∑ b', ∑ b, (if g ((finTwoArrowEquiv β).symm (b, b') 0) =
            g ((finTwoArrowEquiv β).symm (b, b') 1) then (1 : ℝ≥0∞) else 0)
        = ∑ b' : β, ((Finset.univ.filter fun b ↦ g b = g b').card : ℝ≥0∞) := by
          refine Finset.sum_congr rfl fun b' _ ↦ ?_
          rw [Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun b _ ↦ ?_
          change (if g b = g b' then (1 : ℝ≥0∞) else 0) = _
          split_ifs <;> simp
      _ ≤ ∑ _b' : β, (c : ℝ≥0∞) := Finset.sum_le_sum fun b' _ ↦ by exact_mod_cast hc (g b')
      _ = Fintype.card β * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold uavg
  rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, pow_two,
    ENNReal.mul_inv (.inl hβ) (.inl hβt)]
  calc (Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ *
        ∑ u : Fin 2 → β, (if g (u 0) = g (u 1) then (1 : ℝ≥0∞) else 0)
      ≤ (Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ * (Fintype.card β * c) := by
        gcongr
    _ = c / Fintype.card β := by
        rw [mul_assoc, ← mul_assoc _ (Fintype.card β : ℝ≥0∞), ENNReal.inv_mul_cancel hβ hβt,
          one_mul, ENNReal.div_eq_inv_mul]

/-- **The expected number of colliding pairs** is at most `C(n,2) · c / |β|`. -/
theorem uavg_card_collPairs_le :
    uavg (fun f : Fin n → β ↦ ((collPairs fun i ↦ g (f i)).card : ℝ≥0∞)) ≤
      n.choose 2 * (c / Fintype.card β) := by
  have hcard : ∀ f : Fin n → β, ((collPairs fun i ↦ g (f i)).card : ℝ≥0∞) =
      ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2,
        (if g (f p.1) = g (f p.2) then (1 : ℝ≥0∞) else 0) := fun f ↦ by
    rw [collPairs, ← Finset.filter_filter, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun p _ ↦ by split_ifs <;> simp
  simp only [hcard]
  rw [uavg_finset_sum]
  calc ∑ p ∈ Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2,
        uavg (fun f : Fin n → β ↦ if g (f p.1) = g (f p.2) then (1 : ℝ≥0∞) else 0)
      ≤ ∑ _p ∈ Finset.univ.filter fun p : Fin n × Fin n ↦ p.1 < p.2,
          (c / Fintype.card β : ℝ≥0∞) := Finset.sum_le_sum fun p hp ↦
        uavg_collide_le g hc (Finset.mem_filter.mp hp).2.ne
    _ = n.choose 2 * (c / Fintype.card β) := by
        rw [Finset.sum_const, Fintype.card_product_filter_lt, Fintype.card_fin, nsmul_eq_mul]

/-- **Distinct data except with probability `C(n,2) · c / |β|`.** -/
theorem uavg_not_injective_le
    [DecidablePred fun f : Fin n → β ↦ Function.Injective fun i ↦ g (f i)] :
    uavg (fun f : Fin n → β ↦
        if Function.Injective fun i ↦ g (f i) then (0 : ℝ≥0∞) else 1) ≤
      n.choose 2 * (c / Fintype.card β) := by
  refine (uavg_mono fun f ↦ ?_).trans (uavg_card_collPairs_le g hc)
  split_ifs with h
  · exact zero_le
  · exact_mod_cast one_le_card_collPairs h

/-- **The expected multiplicity** is at most `1 + C(n,2) · c / |β|`. -/
theorem uavg_mult_le :
    uavg (fun f : Fin n → β ↦ (mult fun i ↦ g (f i) : ℝ≥0∞)) ≤
      1 + n.choose 2 * (c / Fintype.card β) := by
  have hpt : ∀ f : Fin n → β, ((mult fun i ↦ g (f i)) : ℝ≥0∞) ≤
      1 + ((collPairs fun i ↦ g (f i)).card : ℝ≥0∞) := fun f ↦ by
    have h := mult_le_one_add_card_collPairs fun i ↦ g (f i)
    exact_mod_cast h
  have hone : uavg (fun _ : Fin n → β ↦ (1 : ℝ≥0∞)) ≤ 1 := by
    unfold uavg
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact (ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)).le
  calc uavg (fun f : Fin n → β ↦ ((mult fun i ↦ g (f i)) : ℝ≥0∞))
      ≤ uavg (fun f : Fin n → β ↦ 1 + ((collPairs fun i ↦ g (f i)).card : ℝ≥0∞)) :=
        uavg_mono hpt
    _ = uavg (fun _ : Fin n → β ↦ (1 : ℝ≥0∞)) +
          uavg (fun f : Fin n → β ↦ ((collPairs fun i ↦ g (f i)).card : ℝ≥0∞)) :=
        uavg_add _ _
    _ ≤ 1 + n.choose 2 * (c / Fintype.card β) := add_le_add hone (uavg_card_collPairs_le g hc)

end average

end Quantum.Qrom.MultiUser

end
