import Whir.Layout
import Whir.QuerySoundness

namespace Whir.StratifiedDensity

open scoped BigOperators

/-- The actual top-bit coset used by `Layout.placeQuery`. -/
def coset {depth : ℕ} (s : Layout.Stratum depth) : Finset (Fin (2 ^ depth)) :=
  Finset.univ.filter fun q => q.val / 2 ^ (depth - s.bits) = s.index

/-- Agreement density in the stratum, with its explicit low-bit cardinality. -/
noncomputable def density {depth : ℕ} (A : Finset (Fin (2 ^ depth)))
    (s : Layout.Stratum depth) : ℝ :=
  ((A ∩ coset s).card : ℝ) / (2 ^ (depth - s.bits) : ℕ)

noncomputable def globalDensity {depth : ℕ} (A : Finset (Fin (2 ^ depth))) : ℝ :=
  (A.card : ℝ) / (2 ^ depth : ℕ)

@[simp] theorem mem_coset {depth : ℕ} (s : Layout.Stratum depth)
    (q : Fin (2 ^ depth)) : q ∈ coset s ↔ q.val / 2 ^ (depth - s.bits) = s.index := by
  simp [coset]

/-- Low-bit choices enumerate the coset without collisions. -/
def cosetEquiv {depth : ℕ} (s : Layout.Stratum depth) :
    Fin (2 ^ (depth - s.bits)) ≃ {q : Fin (2 ^ depth) // q ∈ coset s} where
  toFun r := ⟨⟨Layout.placeQuery s r.val, Layout.placeQuery_bound s r.val⟩,
    (mem_coset s _).mpr (Layout.placeQuery_top s r.val)⟩
  invFun q := ⟨q.val.val % 2 ^ (depth - s.bits), Nat.mod_lt _ (by positivity)⟩
  left_inv r := by
    apply Fin.ext
    simp [Layout.placeQuery, Nat.mod_eq_of_lt r.isLt]
  right_inv q := by
    apply Subtype.ext
    apply Fin.ext
    have hq := (mem_coset s q.val).mp q.property
    simp only [Layout.placeQuery, Nat.mod_mod]
    rw [← hq]
    simpa [Nat.mul_comm] using Nat.mod_add_div q.val.val (2 ^ (depth - s.bits))

@[simp] theorem coset_card {depth : ℕ} (s : Layout.Stratum depth) :
    (coset s).card = 2 ^ (depth - s.bits) := by
  simpa only [Fintype.card_coe, Fintype.card_fin] using
    (Fintype.card_congr (cosetEquiv s)).symm

theorem density_eq_card_div {depth : ℕ} (A : Finset (Fin (2 ^ depth)))
    (s : Layout.Stratum depth) :
    density A s = ((A ∩ coset s).card : ℝ) / (coset s).card := by
  simp [density]

theorem density_nonneg {depth : ℕ} (A : Finset (Fin (2 ^ depth)))
    (s : Layout.Stratum depth) : 0 ≤ density A s := by
  unfold density
  positivity

theorem globalDensity_nonneg {depth : ℕ} (A : Finset (Fin (2 ^ depth))) :
    0 ≤ globalDensity A := by
  unfold globalDensity
  positivity

private theorem pow_split (depth bits : ℕ) (h : bits ≤ depth) :
    2 ^ depth = 2 ^ bits * 2 ^ (depth - bits) := by
  rw [← pow_add, Nat.add_sub_of_le h]

/-- Each agreement point belongs to exactly one coset at a fixed bit depth. -/
theorem sum_agreement_cards {depth bits : ℕ} (h : bits ≤ depth)
    (A : Finset (Fin (2 ^ depth))) :
    (∑ j ∈ Finset.range (2 ^ bits), (A ∩ coset (Layout.stratumAt depth bits j)).card) =
      A.card := by
  have hf : ∀ q ∈ A, q.val / 2 ^ (depth - bits) ∈ Finset.range (2 ^ bits) := by
    intro q _
    rw [Finset.mem_range, Nat.div_lt_iff_lt_mul (by positivity)]
    simp [← pow_split depth bits h]
  have hc := Finset.card_eq_sum_card_fiberwise hf
  rw [hc]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ext q
  simp [coset, Layout.stratumAt, Nat.min_eq_left h,
    Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]

/-- The sum of the concrete coset densities is obtained by counting agreement points. -/
theorem sum_densities {depth bits : ℕ} (h : bits ≤ depth)
    (A : Finset (Fin (2 ^ depth))) :
    (∑ j ∈ Finset.range (2 ^ bits), density A (Layout.stratumAt depth bits j)) =
      (2 ^ bits : ℕ) * globalDensity A := by
  simp only [density, Layout.stratumAt, Nat.min_eq_left h]
  rw [← Finset.sum_div]
  have hc := sum_agreement_cards h A
  simp only [Layout.stratumAt, Nat.min_eq_left h] at hc
  rw [← Nat.cast_sum, hc]
  unfold globalDensity
  conv_rhs => arg 2; arg 2; rw [pow_split depth bits h, Nat.cast_mul]
  field_simp

private theorem sum_range_mod (f : ℕ → ℝ) (n k : ℕ) :
    (∑ j ∈ Finset.range (n * k), f (j % n)) =
      k * ∑ j ∈ Finset.range n, f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have h : (∑ j ∈ Finset.range n, f ((n * k + j) % n)) =
        ∑ j ∈ Finset.range n, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Nat.add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
    rw [h, Nat.cast_add, Nat.cast_one]
    ring

/-- Larger binary groups repeat all top-bit cosets equally, rather than deduplicating. -/
theorem group_sum_densities (depth g : ℕ) (A : Finset (Fin (2 ^ depth))) :
    (∑ j ∈ Finset.range (2 ^ g), density A (Layout.stratumAt depth g j)) =
      (2 ^ g : ℕ) * globalDensity A := by
  let b := min g depth
  have hb : b ≤ depth := Nat.min_le_right _ _
  have hbg : b ≤ g := Nat.min_le_left _ _
  have hs (j : ℕ) : Layout.stratumAt depth g j =
      Layout.stratumAt depth b (j % 2 ^ b) := by
    simp [Layout.stratumAt, b]
  simp_rw [hs]
  conv_lhs => rw [pow_split g b hbg]
  rw [sum_range_mod (fun j => density A (Layout.stratumAt depth b j)),
    sum_densities hb]
  conv_rhs => rw [pow_split g b hbg, Nat.cast_mul]
  ring

private theorem list_prod_range (f : ℕ → ℝ) (n : ℕ) :
    ((List.range n).map f).prod = ∏ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.prod_range_succ, ih]

/-- AM-GM applied to the actual finite cosets of one binary group. -/
theorem group_product_le (depth g : ℕ) (A : Finset (Fin (2 ^ depth))) :
    ((Layout.stratumGroup depth g).map (density A)).prod ≤
      globalDensity A ^ (2 ^ g) := by
  let : NeZero (2 ^ g) := ⟨by positivity⟩
  have h := QuerySoundness.strata_amgm
    (fun j : Fin (2 ^ g) => density A (Layout.stratumAt depth g j.val))
    (fun _ => density_nonneg A _)
  have hs : (∑ j : Fin (2 ^ g), density A (Layout.stratumAt depth g j.val)) =
      (2 ^ g : ℕ) * globalDensity A := by
    rw [Fin.sum_univ_eq_sum_range (fun j => density A (Layout.stratumAt depth g j))]
    exact group_sum_densities depth g A
  rw [hs, Fintype.card_fin, mul_div_cancel_left₀ _ (by positivity)] at h
  unfold QuerySoundness.missProduct at h
  rw [Fin.prod_univ_eq_prod_range (fun j => density A (Layout.stratumAt depth g j))] at h
  simpa only [Layout.stratumGroup, List.map_map, Function.comp_def, list_prod_range] using h

/-- Every symbolic binary group contributes its exact query count to the exponent.
This includes zero count, depth zero, empty agreement, and groups larger than the domain. -/
theorem strataBits_product_le (width count depth : ℕ) (A : Finset (Fin (2 ^ depth)))
    (hc : count < 2 ^ width) :
    ((Layout.strataBits width count depth).map (density A)).prod ≤
      globalDensity A ^ count := by
  induction width generalizing count with
  | zero =>
    have : count = 0 := by simpa using hc
    simp [Layout.strataBits, this]
  | succ width ih =>
    have hp : 2 ^ (width + 1) = 2 ^ width * 2 := by rw [pow_succ]
    simp only [Layout.strataBits]
    split_ifs with h
    · rw [List.map_append, List.prod_append]
      have hn : 0 ≤ ((Layout.strataBits width (count - 2 ^ width) depth).map
          (density A)).prod := List.prod_nonneg (by
        intro x hx
        obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
        exact density_nonneg A s)
      calc
        _ ≤ globalDensity A ^ (2 ^ width) * globalDensity A ^ (count - 2 ^ width) :=
          mul_le_mul (group_product_le depth width A)
            (ih (count - 2 ^ width) (by omega)) hn
            (pow_nonneg (globalDensity_nonneg A) _)
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le h]
    · exact ih count (by omega)

/-- Finite-domain form of the exact query placement. -/
def placed {depth : ℕ} (s : Layout.Stratum depth) (raw : Fin (2 ^ depth)) :
    Fin (2 ^ depth) := ⟨Layout.placeQuery s raw.val, Layout.placeQuery_bound s raw.val⟩

/-- A successful raw sample is an agreement point in the coset and arbitrary discarded top bits. -/
def rawAgreementEquiv {depth : ℕ} (A : Finset (Fin (2 ^ depth)))
    (s : Layout.Stratum depth) :
    {raw : Fin (2 ^ depth) // placed s raw ∈ A} ≃
      Fin (2 ^ s.bits) × {q : Fin (2 ^ depth) // q ∈ A ∩ coset s} where
  toFun raw := (⟨raw.val.val / 2 ^ (depth - s.bits), by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    simp [← pow_split depth s.bits s.bits_le]⟩,
    ⟨placed s raw.val, Finset.mem_inter.mpr ⟨raw.property,
      (mem_coset s _).mpr (Layout.placeQuery_top s raw.val.val)⟩⟩)
  invFun p := by
    let r := p.2.val.val % 2 ^ (depth - s.bits) +
      p.1.val * 2 ^ (depth - s.bits)
    have hr : r < 2 ^ depth := by
      rw [pow_split depth s.bits s.bits_le]
      have hm := Nat.mod_lt p.2.val.val (show 0 < 2 ^ (depth - s.bits) by positivity)
      have ht := Nat.mul_le_mul_right (2 ^ (depth - s.bits)) p.1.isLt
      dsimp [r]
      nlinarith
    refine ⟨⟨r, hr⟩, ?_⟩
    have hp : placed s ⟨r, hr⟩ = p.2.val := by
      apply Fin.ext
      have hq := (mem_coset s p.2.val).mp (Finset.mem_inter.mp p.2.property).2
      simp only [placed, Layout.placeQuery, r, Nat.add_mod, Nat.mul_mod,
        Nat.mod_self, mul_zero, Nat.mod_mod]
      rw [← hq]
      simpa [Nat.mul_comm] using Nat.mod_add_div p.2.val.val (2 ^ (depth - s.bits))
    rw [hp]
    exact (Finset.mem_inter.mp p.2.property).1
  left_inv raw := by
    apply Subtype.ext
    apply Fin.ext
    simp only [placed, Layout.placeQuery]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.mod_mod]
    simpa [Nat.mul_comm] using Nat.mod_add_div raw.val.val (2 ^ (depth - s.bits))
  right_inv p := by
    apply Prod.ext
    · apply Fin.ext
      dsimp
      rw [Nat.add_mul_div_right _ _ (by positivity)]
      simp [Nat.div_eq_of_lt (Nat.mod_lt _ (show 0 < 2 ^ (depth - s.bits) by positivity))]
    · apply Subtype.ext
      apply Fin.ext
      have hq := (mem_coset s p.2.val).mp (Finset.mem_inter.mp p.2.property).2
      simp only [placed, Layout.placeQuery]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero, Nat.mod_mod]
      rw [← hq]
      simpa [Nat.mul_comm] using Nat.mod_add_div p.2.val.val (2 ^ (depth - s.bits))

/-- Uniform raw samples induce uniform sampling in the actual coset. -/
theorem raw_probability_eq_density {depth : ℕ} (A : Finset (Fin (2 ^ depth)))
    (s : Layout.Stratum depth) :
    (Fintype.card {raw : Fin (2 ^ depth) // placed s raw ∈ A} : ℝ) /
      (2 ^ depth : ℕ) = density A s := by
  have hc := Fintype.card_congr (rawAgreementEquiv A s)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] at hc
  rw [hc, Nat.cast_mul]
  unfold density
  conv_lhs => arg 2; rw [pow_split depth s.bits s.bits_le, Nat.cast_mul]
  field_simp

end Whir.StratifiedDensity
