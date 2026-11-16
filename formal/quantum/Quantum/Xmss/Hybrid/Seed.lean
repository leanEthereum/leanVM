module

public import Quantum.Xmss.Hybrid.View

@[expose] public section

/-!
# The hidden-cell hybrid at the seed level, averaged over the table

* **Averaging over the table** (`uavg`, the uniform average over a finite type). If
  `√P₁ θ ≤ √P₂ θ + ∑ⱼ √(4 μⱼ θ)` for every table `θ`, then `E √P₁ ≤ E √P₂ + ∑ⱼ √(4 E μⱼ)`
  (`uavg_sqrt_le_of_hybrid`, Jensen for the square root, `uavg_sqrt_le`) and
  `E P₁ ≤ (√(E P₂) + ∑ⱼ √(4 E μⱼ))²` (`uavg_le_of_hybrid`, Minkowski in `L²`, `l2_tsum_le`).
  `uavg_win_runtime1_le` applies this to `sqrt_win_runtime1_le`.
* **The challenger's data from the scheme seed** (`seedData Q`): the honest evaluations, results
  and reads, of hash computations `Q i S` from the scheme seed (not the seed derivation itself).
* **The good set** `seedGood Q zr`: no `Q i` reads `h` at the seed derivation's capacity `seedZ L`
  or at the reference cell `zr`. On it the data is a function of the public part of `seedSplit zr`
  (`seedData_eq_of_mem_seedGood`), which is the hypothesis of `avg_hiddenMass_masterSeed_le`.
* **Its complement** (`exists_seedGood_frac_le`): for some `zr`, at most the fraction of
  permutations with a rate count above `G`, plus `qsᵢ / 2^256 + (G + 1) qᵢ / |Z|` per computation,
  plus `∑ᵢ qᵢ / |Z|`, where `qᵢ` bounds the reads of `Q i` (`length_snd_honestEval`) and `qsᵢ` its
  reads at seed-shaped `k`-cells (`card_filter_seedShaped_kCells_le`: only inputs outside `41` to
  `135` bytes contribute). The proof: the scheme seed is a fresh `h` value, so the event for the
  table's own seed is the average of the events for fixed seeds (`card_mul_sum_seedHit_seed_eq`);
  for a fixed computation, resample `k` at the seed derivation's first cell (`S₀` is unknown to the
  computation: `qs / 2^256`), then its value (rate counts: `G q / |Z|`), then `k'` at the
  intermediate rate (`q / |Z|`) (`card_mul_sum_eq_sum_sum_update`); `zr` is averaged out.
* `avg_hiddenMass_masterSeed_le_of_seedData`: the master-seed mass bound end to end.

Not here: a reparametrization hiding the scheme seed `S` with every seed-keyed output (parameter,
chain starts, randomizer bases) a function of the public part. With the randomizer bases of all
`2^288` (layer, key, message) triples in the challenger's data, their final capacities collide
(about `2^63` pairs expected), and colliding outputs satisfy relations that depend on `S`, so such
a good set misses almost every table. It needs the randomizer bases restricted to the requested
messages (fresh coins, or a view lemma per branch of requests).
-/

open Matrix
open scoped ENNReal ComplexOrder

universe u v w

namespace Quantum.Xmss.Hybrid

open Quantum

/-! ## Averaging square roots over the table -/

section average

variable {Θ : Type*} [Fintype Θ]

/-- The uniform average over a finite type. -/
noncomputable def uavg (f : Θ → ℝ≥0∞) : ℝ≥0∞ :=
  (Fintype.card Θ : ℝ≥0∞)⁻¹ * ∑ θ, f θ

theorem uavg_mono {f g : Θ → ℝ≥0∞} (h : ∀ θ, f θ ≤ g θ) : uavg f ≤ uavg g := by
  unfold uavg
  gcongr with θ
  exact h θ

theorem uavg_add (f g : Θ → ℝ≥0∞) : uavg (fun θ ↦ f θ + g θ) = uavg f + uavg g := by
  simp only [uavg, Finset.sum_add_distrib, mul_add]

theorem uavg_const_mul (c : ℝ≥0∞) (f : Θ → ℝ≥0∞) : uavg (fun θ ↦ c * f θ) = c * uavg f := by
  simp only [uavg, ← Finset.mul_sum]
  ring

theorem uavg_tsum (f : ℕ → Θ → ℝ≥0∞) : uavg (fun θ ↦ ∑' j, f j θ) = ∑' j, uavg (f j) := by
  simp only [uavg]
  rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]

/-- **Jensen for the square root**: the average of square roots is at most the square root of the
average. -/
theorem uavg_sqrt_le (f : Θ → ℝ≥0∞) :
    uavg (fun θ ↦ f θ ^ (2⁻¹ : ℝ)) ≤ uavg f ^ (2⁻¹ : ℝ) := by
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · simp [uavg]
  set c : ℝ≥0∞ := (Fintype.card Θ : ℝ≥0∞)⁻¹
  have hw : ∑ _θ : Θ, c = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (by simp)
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow Finset.univ (fun _ ↦ c)
    (fun θ ↦ f θ ^ (2⁻¹ : ℝ)) hw (p := 2) (by norm_num)
  simp only [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ← Finset.mul_sum] at h
  calc uavg (fun θ ↦ f θ ^ (2⁻¹ : ℝ))
      = ((c * ∑ θ, f θ ^ (2⁻¹ : ℝ)) ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := by
        rw [ENNReal.rpow_rpow_inv (by norm_num)]
        rfl
    _ ≤ (c * ∑ θ, f θ) ^ (2⁻¹ : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)

/-- The unweighted `L²` norm of a function on a finite type. -/
noncomputable def l2 (f : Θ → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ θ, f θ ^ (2 : ℝ)) ^ (2⁻¹ : ℝ)

theorem le_l2 (f : Θ → ℝ≥0∞) (θ : Θ) : f θ ≤ l2 f := by
  calc f θ = (f θ ^ (2 : ℝ)) ^ (2⁻¹ : ℝ) := (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    _ ≤ l2 f := ENNReal.rpow_le_rpow
        (Finset.single_le_sum (f := fun θ ↦ f θ ^ (2 : ℝ)) (fun _ _ ↦ zero_le) (Finset.mem_univ θ))
        (by norm_num)

theorem l2_mul_self (f : Θ → ℝ≥0∞) : l2 f * l2 f = ∑ θ, f θ * f θ := by
  rw [l2, ← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.rpow_two, pow_two]

/-- **Cauchy-Schwarz.** -/
theorem sum_mul_le_l2_mul_l2 (f g : Θ → ℝ≥0∞) : ∑ θ, f θ * g θ ≤ l2 f * l2 g := by
  have h := ENNReal.inner_le_Lp_mul_Lq Finset.univ f g Real.HolderConjugate.two_two
  simpa only [l2, one_div] using h

/-- **Minkowski for two functions.** -/
theorem l2_add_le (f g : Θ → ℝ≥0∞) : l2 (fun θ ↦ f θ + g θ) ≤ l2 f + l2 g := by
  have h := ENNReal.Lp_add_le Finset.univ f g (p := 2) (by norm_num)
  simpa only [l2, one_div] using h

/-- **Minkowski for a countable family**: the `L²` norm of a sum is at most the sum of the norms. -/
theorem l2_tsum_le (f : ℕ → Θ → ℝ≥0∞) : l2 (fun θ ↦ ∑' j, f j θ) ≤ ∑' j, l2 (f j) := by
  set F : Θ → ℝ≥0∞ := fun θ ↦ ∑' j, f j θ
  set S := ∑' j, l2 (f j)
  have hsq : l2 F * l2 F ≤ l2 F * S := by
    calc l2 F * l2 F = ∑ θ, F θ * F θ := l2_mul_self F
      _ = ∑' j, ∑ θ, F θ * f j θ := by
        rw [Summable.tsum_finsetSum fun _ _ ↦ ENNReal.summable]
        simp only [F, ENNReal.tsum_mul_left]
      _ ≤ ∑' j, l2 F * l2 (f j) := ENNReal.tsum_le_tsum fun j ↦ sum_mul_le_l2_mul_l2 F (f j)
      _ = l2 F * S := ENNReal.tsum_mul_left
  by_cases h0 : l2 F = 0
  · rw [h0]
    exact zero_le
  by_cases ht : l2 F = ⊤
  · suffices hS : S = ⊤ by rw [hS]; exact le_top
    have hsum : ∑ θ, F θ ^ (2 : ℝ) = ⊤ := by
      by_contra hne
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hne ht
    obtain ⟨θ, -, hθ⟩ := ENNReal.sum_eq_top.mp hsum
    have hFθ : F θ = ⊤ := by
      by_contra hne
      exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hne hθ
    refine top_le_iff.mp ?_
    calc ⊤ = F θ := hFθ.symm
      _ ≤ S := ENNReal.tsum_le_tsum fun j ↦ le_l2 (f j) θ
  exact (ENNReal.mul_le_mul_iff_right h0 ht).mp hsq

/-- The average is the scaled square of the `L²` norm of the square root. -/
theorem uavg_eq_l2_sqrt (f : Θ → ℝ≥0∞) :
    uavg f = (Fintype.card Θ : ℝ≥0∞)⁻¹ * (l2 fun θ ↦ f θ ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [uavg, l2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [← ENNReal.rpow_mul, Nat.cast_ofNat, show (2⁻¹ : ℝ) * 2 = 1 by norm_num,
    ENNReal.rpow_one]

/-- The square root of the average is the scaled `L²` norm of the square root. -/
theorem uavg_sqrt_eq (f : Θ → ℝ≥0∞) :
    uavg f ^ (2⁻¹ : ℝ) =
      (Fintype.card Θ : ℝ≥0∞)⁻¹ ^ (2⁻¹ : ℝ) * l2 (fun θ ↦ f θ ^ (2⁻¹ : ℝ)) := by
  rw [uavg, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), l2]
  simp only [← ENNReal.rpow_mul, show (2⁻¹ : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]

/-- **The hybrid averaged over the table, square-root form.** If, for every table `θ`,
`√P₁ θ ≤ √P₂ θ + ∑ⱼ √(4 μⱼ θ)`, then the same holds for the averages of the square roots, with the
averaged masses: `E √P₁ ≤ E √P₂ + ∑ⱼ √(4 E μⱼ)` (Jensen for the concave square root). -/
theorem uavg_sqrt_le_of_hybrid (P₁ P₂ : Θ → ℝ≥0∞) (μ : Θ → ℕ → ℝ≥0∞)
    (h : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤ P₂ θ ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ θ j) ^ (2⁻¹ : ℝ)) :
    uavg (fun θ ↦ P₁ θ ^ (2⁻¹ : ℝ)) ≤
      uavg (fun θ ↦ P₂ θ ^ (2⁻¹ : ℝ)) + ∑' j, (4 * uavg (fun θ ↦ μ θ j)) ^ (2⁻¹ : ℝ) := by
  refine (uavg_mono h).trans ?_
  rw [uavg_add, uavg_tsum]
  gcongr with j
  rw [← uavg_const_mul]
  exact uavg_sqrt_le _

/-- **The hybrid averaged over the table, probability form.** If, for every table `θ`,
`√P₁ θ ≤ √P₂ θ + ∑ⱼ √(4 μⱼ θ)`, then `E P₁ ≤ (√(E P₂) + ∑ⱼ √(4 E μⱼ))²` (Minkowski in `L²` of the
uniform table). -/
theorem uavg_le_of_hybrid (P₁ P₂ : Θ → ℝ≥0∞) (μ : Θ → ℕ → ℝ≥0∞)
    (h : ∀ θ, P₁ θ ^ (2⁻¹ : ℝ) ≤ P₂ θ ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ θ j) ^ (2⁻¹ : ℝ)) :
    uavg P₁ ≤
      (uavg P₂ ^ (2⁻¹ : ℝ) + ∑' j, (4 * uavg (fun θ ↦ μ θ j)) ^ (2⁻¹ : ℝ)) ^ 2 := by
  set c : ℝ≥0∞ := (Fintype.card Θ : ℝ≥0∞)⁻¹
  have hl2 : l2 (fun θ ↦ P₁ θ ^ (2⁻¹ : ℝ)) ≤
      l2 (fun θ ↦ P₂ θ ^ (2⁻¹ : ℝ)) + ∑' j, l2 (fun θ ↦ (4 * μ θ j) ^ (2⁻¹ : ℝ)) := by
    calc l2 (fun θ ↦ P₁ θ ^ (2⁻¹ : ℝ))
        ≤ l2 (fun θ ↦ P₂ θ ^ (2⁻¹ : ℝ) + ∑' j, (4 * μ θ j) ^ (2⁻¹ : ℝ)) := by
          unfold l2
          gcongr with θ
          exact h θ
      _ ≤ l2 (fun θ ↦ P₂ θ ^ (2⁻¹ : ℝ)) + l2 (fun θ ↦ ∑' j, (4 * μ θ j) ^ (2⁻¹ : ℝ)) :=
          l2_add_le _ _
      _ ≤ _ := by
          gcongr
          exact l2_tsum_le fun j θ ↦ (4 * μ θ j) ^ (2⁻¹ : ℝ)
  have hsq : (c ^ (2⁻¹ : ℝ)) ^ 2 = c := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [uavg_eq_l2_sqrt, uavg_sqrt_eq]
  simp only [← uavg_const_mul, uavg_sqrt_eq]
  rw [ENNReal.tsum_mul_left, ← mul_add, mul_pow, hsq]
  gcongr

end average

section hybridAvg

open scoped Kronecker
open Quantum.Sponge

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X]
  [AddCommGroup Z] [Nonempty X] [Nonempty Z] {M : Type} [Fintype M] [DecidableEq M]
  {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Xf : QReg → Type w} {A : QReg} {γ : Type*} [MeasurableSpace γ]

/-- **Runtime 1 against runtime 2, averaged over the table.** For tables `L θ` covered by hidden
sets, runs `x θ` and masses `μ θ j` of the `j`-th call of the run against runtime 2,
`E P₁ ≤ (√(E P₂) + ∑ⱼ √(4 E μⱼ))²`. -/
theorem uavg_win_runtime1_le {Θ : Type*} [Fintype Θ] (L : Θ → Hw X Z) (Hh : Θ → Set Z)
    (Hk Hk' : Θ → Set X) (hL : ∀ θ, Covers (L θ) (Hh θ) (Hk θ) (Hk' θ)) (m₀ : M)
    (x : Θ → QuantumComp Λ (hwSpec X Z M) Xf A) (ρ : Θ → SubState A)
    (f : Θ → (Σ u, Xf u) → γ) {s : Set γ} (hs : MeasurableSet s) (μ : Θ → ℕ → ℝ≥0∞)
    (hHidden : ∀ θ j, (runtime2 X Z m₀).queryWeight I (hiddenMass (Hh θ) (Hk θ) (Hk' θ)) (x θ)
      ((ρ θ).matrix ⊗ₖ (runtime2 X Z m₀).init.matrix) j ≤ μ θ j) :
    uavg (fun θ ↦ (runtime1 X Z (L θ) m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ≤
      (uavg (fun θ ↦ (runtime2 X Z m₀).evalDistMap I (x θ) (ρ θ) (f θ) s) ^ (2⁻¹ : ℝ) +
        ∑' j, (4 * uavg (fun θ ↦ μ θ j)) ^ (2⁻¹ : ℝ)) ^ 2 :=
  uavg_le_of_hybrid _ _ μ fun θ ↦
    sqrt_win_runtime1_le I (L θ) m₀ (hL θ) (x θ) (ρ θ) (f θ) hs (hHidden θ)

end hybridAvg

/-! ## Resampling one value of a uniform function -/

section resample

/-- **Resampling one value.** Summing over a uniform function and a fresh value at `c` counts
every function `|B|` times. -/
theorem card_mul_sum_eq_sum_sum_update {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (F : (A → B) → ℕ) (c : A) :
    Fintype.card B * ∑ f : A → B, F f = ∑ f : A → B, ∑ b, F (Function.update f c b) := by
  let φ : (A → B) × B → (A → B) × B := fun p ↦ (Function.update p.1 c p.2, p.1 c)
  have hφ : Function.Involutive φ := fun p ↦ by
    simp only [φ, Function.update_idem, Function.update_eq_self, Function.update_self]
  rw [← Fintype.sum_prod_type' (fun f b ↦ F (Function.update f c b)),
    Fintype.sum_equiv hφ.toPerm (fun p ↦ F (Function.update p.1 c p.2)) (fun p ↦ F p.1)
      (fun _ ↦ rfl), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Finset.mul_sum, mul_comm]

/-- Counting the points of a finite set by indicators. -/
theorem sum_ite_mem_eq_card {A : Type*} [Fintype A] [DecidableEq A] (H : Finset A) :
    ∑ a, (if a ∈ H then 1 else 0) = H.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.card_eq_sum_ones]

/-- Translating a finite set does not change its count. -/
theorem sum_ite_add_mem_eq_card {A : Type*} [Fintype A] [DecidableEq A] [AddGroup A]
    (H : Finset A) (s : A) : ∑ a, (if s + a ∈ H then 1 else 0) = H.card := by
  rw [← sum_ite_mem_eq_card H]
  exact Fintype.sum_equiv (Equiv.addLeft s) _ _ fun _ ↦ rfl

/-- The points mapped into `K` by a map whose fibers have at most `G` points. -/
theorem sum_ite_comp_mem_le {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (K : Finset B)
    (G : ℕ) (hG : ∀ b, (Finset.univ.filter fun a ↦ f a = b).card ≤ G) :
    ∑ a, (if f a ∈ K then 1 else 0) ≤ K.card * G := by
  calc ∑ a, (if f a ∈ K then 1 else 0)
      = ∑ a, ∑ b ∈ K, (if f a = b then 1 else 0) :=
        Finset.sum_congr rfl fun a _ ↦ (Finset.sum_ite_eq K (f a) fun _ ↦ 1).symm
    _ = ∑ b ∈ K, (Finset.univ.filter fun a ↦ f a = b).card := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ ↦ (Finset.card_filter _ _).symm
    _ ≤ ∑ _b ∈ K, G := Finset.sum_le_sum fun b _ ↦ hG b
    _ = K.card * G := by rw [Finset.sum_const, smul_eq_mul]

/-- An injection into a finite set, landing in `P`, counts at most the points of `P` there. -/
theorem sum_ite_mem_le_card_filter {A B : Type*} [Fintype A] [DecidableEq B] (c : A → B)
    (hc : Function.Injective c) (K : Finset B) (P : B → Prop) [DecidablePred P]
    (hP : ∀ a, P (c a)) : ∑ a, (if c a ∈ K then 1 else 0) ≤ (K.filter P).card := by
  rw [← Finset.card_filter]
  refine Finset.card_le_card_of_injOn c (fun a ha ↦ ?_) hc.injOn
  rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
  exact ⟨ha.2, hP a⟩

/-- The points outside a finite set, counted by a function at least `1` there. -/
theorem card_sub_card_le_sum {A : Type*} [Fintype A] [DecidableEq A] (S : Finset A) (f : A → ℕ)
    (hf : ∀ a, a ∉ S → 1 ≤ f a) : Fintype.card A - S.card ≤ ∑ a, f a := by
  have h1 : ∀ a, 1 ≤ (if a ∈ S then 1 else 0) + f a := fun a ↦ by
    by_cases ha : a ∈ S
    · rw [ite_eq_left ha]
      omega
    · rw [ite_eq_right ha]
      have := hf a ha
      omega
  have h2 : ∑ _a : A, 1 ≤ ∑ a, ((if a ∈ S then 1 else 0) + f a) := Finset.sum_le_sum fun a _ ↦ h1 a
  rw [Finset.sum_add_distrib, sum_ite_mem_eq_card, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at h2
  omega

/-- Some point of a nonempty finite type is at most the average. -/
theorem exists_card_mul_le_of_sum_le {A : Type*} [Fintype A] [Nonempty A] (f : A → ℕ) (D : ℕ)
    (h : ∑ a, f a ≤ D) : ∃ a, Fintype.card A * f a ≤ D := by
  by_contra hne
  push Not at hne
  have hlt : ∑ _a : A, D < ∑ a, Fintype.card A * f a :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ ↦ hne a
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Finset.mul_sum] at hlt
  exact absurd (Nat.mul_le_mul_left _ h) (not_le.mpr hlt)

end resample

/-! ## The master seed's good set -/

section seedGood

open HashSig LeanXmss Quantum.Sponge

/-! ### The cells of a list of reads -/

/-- The `h`-cells of a list of reads. -/
def hCells (R : List (SpongeRead X Z)) : Finset Z :=
  (R.filterMap fun | .h z _ => some z | _ => none).toFinset

/-- The `k`-cells of a list of reads. -/
def kCells (R : List (SpongeRead X Z)) : Finset X :=
  (R.filterMap fun | .k x _ => some x | _ => none).toFinset

/-- The `k'`-cells of a list of reads. -/
def k'Cells (R : List (SpongeRead X Z)) : Finset X :=
  (R.filterMap fun | .k' x _ => some x | _ => none).toFinset

theorem mem_hCells {R : List (SpongeRead X Z)} {z : Z} :
    z ∈ hCells R ↔ ∃ a, SpongeRead.h z a ∈ R := by
  simp only [hCells, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hez⟩
    cases e with
    | h z' a =>
      rw [Option.some.injEq] at hez
      exact ⟨a, hez ▸ he⟩
    | k _ _ => exact absurd hez (by simp)
    | k' _ _ => exact absurd hez (by simp)
  · rintro ⟨a, ha⟩
    exact ⟨_, ha, rfl⟩

theorem mem_kCells {R : List (SpongeRead X Z)} {x : X} :
    x ∈ kCells R ↔ ∃ a, SpongeRead.k x a ∈ R := by
  simp only [kCells, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hex⟩
    cases e with
    | k x' a =>
      rw [Option.some.injEq] at hex
      exact ⟨a, hex ▸ he⟩
    | h _ _ => exact absurd hex (by simp)
    | k' _ _ => exact absurd hex (by simp)
  · rintro ⟨a, ha⟩
    exact ⟨_, ha, rfl⟩

theorem mem_k'Cells {R : List (SpongeRead X Z)} {x : X} :
    x ∈ k'Cells R ↔ ∃ a, SpongeRead.k' x a ∈ R := by
  simp only [k'Cells, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hex⟩
    cases e with
    | k' x' a =>
      rw [Option.some.injEq] at hex
      exact ⟨a, hex ▸ he⟩
    | h _ _ => exact absurd hex (by simp)
    | k _ _ => exact absurd hex (by simp)
  · rintro ⟨a, ha⟩
    exact ⟨_, ha, rfl⟩

theorem card_hCells_le (R : List (SpongeRead X Z)) : (hCells R).card ≤ R.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem card_k'Cells_le (R : List (SpongeRead X Z)) : (k'Cells R).card ≤ R.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

/-! ### The honest evaluation off one cell -/

variable {α : Type} (x : OracleComp LeanXmss.HashSpec α) (π : Equiv.Perm (X × Z))

/-- The honest evaluation does not depend on an `h`-cell it does not read. -/
theorem honestEval_update_h (h : Z → X) (k k' : X → Z) {z : Z}
    (hz : z ∉ hCells (honestEval (h, k, k') π x).2) (v : X) :
    honestEval (Function.update h z v, k, k') π x = honestEval (h, k, k') π x :=
  honestEval_congr π x fun e he ↦ by
    have ha := honestEval_answeredBy π (h, k, k') x e he
    cases e with
    | h z' a =>
      have hne : z' ≠ z := fun hh ↦ hz (mem_hCells.mpr ⟨a, hh ▸ he⟩)
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      rw [Function.update_of_ne hne]
      exact ha
    | k _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha
    | k' _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha

/-- The honest evaluation does not depend on a `k`-cell it does not read. -/
theorem honestEval_update_k (h : Z → X) (k k' : X → Z) {c : X}
    (hc : c ∉ kCells (honestEval (h, k, k') π x).2) (w : Z) :
    honestEval (h, Function.update k c w, k') π x = honestEval (h, k, k') π x :=
  honestEval_congr π x fun e he ↦ by
    have ha := honestEval_answeredBy π (h, k, k') x e he
    cases e with
    | k x' a =>
      have hne : x' ≠ c := fun hh ↦ hc (mem_kCells.mpr ⟨a, hh ▸ he⟩)
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      rw [Function.update_of_ne hne]
      exact ha
    | h _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha
    | k' _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha

/-- The honest evaluation does not depend on a `k'`-cell it does not read. -/
theorem honestEval_update_k' (h : Z → X) (k k' : X → Z) {c : X}
    (hc : c ∉ k'Cells (honestEval (h, k, k') π x).2) (a : Z) :
    honestEval (h, k, Function.update k' c a) π x = honestEval (h, k, k') π x :=
  honestEval_congr π x fun e he ↦ by
    have ha := honestEval_answeredBy π (h, k, k') x e he
    cases e with
    | k' x' b =>
      have hne : x' ≠ c := fun hh ↦ hc (mem_k'Cells.mpr ⟨b, hh ▸ he⟩)
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      rw [Function.update_of_ne hne]
      exact ha
    | h _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha
    | k _ _ =>
      simp only [SpongeRead.AnsweredBy] at ha ⊢
      exact ha

/-- Whether the honest evaluation reads `h` at `z` does not depend on the value there. -/
theorem mem_hCells_update_iff (h : Z → X) (k k' : X → Z) (z : Z) (v : X) :
    z ∈ hCells (honestEval (Function.update h z v, k, k') π x).2 ↔
      z ∈ hCells (honestEval (h, k, k') π x).2 := by
  constructor
  · intro hm
    by_contra hz
    rw [honestEval_update_h x π h k k' hz v] at hm
    exact hz hm
  · intro hm
    by_contra hz
    have he := honestEval_update_h x π (Function.update h z v) k k' hz (h z)
    rw [Function.update_idem, Function.update_eq_self] at he
    rw [he] at hm
    exact hz hm

/-- If the honest evaluation with `k c = w` does not read `k` at `c`, it is the evaluation
with `k`. -/
theorem honestEval_update_k_of_not_mem (h : Z → X) (k k' : X → Z) {c : X} {w : Z}
    (hc : c ∉ kCells (honestEval (h, Function.update k c w, k') π x).2) :
    honestEval (h, Function.update k c w, k') π x = honestEval (h, k, k') π x := by
  have he := honestEval_update_k x π h (Function.update k c w) k' hc (k c)
  rw [Function.update_idem, Function.update_eq_self] at he
  exact he.symm

/-- If the honest evaluation with `k' c = a` does not read `k'` at `c`, it is the evaluation
with `k'`. -/
theorem honestEval_update_k'_of_not_mem (h : Z → X) (k k' : X → Z) {c : X} {a : Z}
    (hc : c ∉ k'Cells (honestEval (h, k, Function.update k' c a) π x).2) :
    honestEval (h, k, Function.update k' c a) π x = honestEval (h, k, k') π x := by
  have he := honestEval_update_k' x π h k (Function.update k' c a) hc (k' c)
  rw [Function.update_idem, Function.update_eq_self] at he
  exact he.symm

/-! ### Counting the reads of an honest evaluation -/

theorem kCells_append (R R' : List (SpongeRead X Z)) : kCells (R ++ R') = kCells R ∪ kCells R' := by
  simp only [kCells, List.filterMap_append, List.toFinset_append]

theorem card_kCells_le (R : List (SpongeRead X Z)) : (kCells R).card ≤ R.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

theorem card_filter_kCells_flatMap_le {γ : Type} (P : X → Prop) [DecidablePred P]
    (f : γ → List (SpongeRead X Z)) :
    ∀ l : List γ, ((kCells (l.flatMap f)).filter P).card ≤
      (l.map fun a ↦ ((kCells (f a)).filter P).card).sum
  | [] => by simp [kCells]
  | a :: l => by
    rw [List.flatMap_cons, kCells_append, Finset.filter_union, List.map_cons, List.sum_cons]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (card_filter_kCells_flatMap_le P f l) _)

theorem sum_map_le_sum_map {γ : Type} (l : List γ) (f g : γ → ℕ) (h : ∀ a, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a) ih

open LeanVM.Protocol.KeccakHash (padBlock)

/-- A one-block input is read by `k` at its padded block only. -/
theorem kCells_inputReads_of_lt (t : SpongeKeys X Z) (inp : HashInput) (h : inp.length < 136) :
    kCells (inputReads t π inp) = {blockOf (padBlock inp)} := by
  have hb : blocks inp = [blockOf (padBlock inp)] := by
    have hl := length_blocks inp
    have hh := head?_blocks inp
    rw [firstBlock_of_lt _ h] at hh
    cases hbl : blocks inp with
    | nil => rw [hbl] at hh; simp at hh
    | cons b m =>
      rw [hbl, List.length_cons] at hl
      rw [hbl, List.head?_cons, Option.some.injEq] at hh
      rw [List.eq_nil_of_length_eq_zero (l := m) (by omega), hh]
  rw [inputReads, hb, show [blockOf (padBlock inp)] = [] ++ [blockOf (padBlock inp)] from rfl,
    spongeReads_append_singleton, spongeReads_nil]
  simp [kCells, roundReads, absorb]

/-- The reads of an honest evaluation: three per absorbed block. -/
theorem length_snd_honestEval (t : SpongeKeys X Z) :
    (honestEval t π x).2.length =
      ((queries (spongeOut (spongePerm t π)) x).map fun inp ↦ 3 * (blocks inp).length).sum := by
  rw [snd_honestEval, List.length_flatMap]
  simp only [inputReads, length_spongeReads]

/-- **Seed-shaped `k`-reads come from long inputs.** An input of `41` to `135` bytes is one
padded block, never seed-shaped; the others contribute at most their three reads per block. -/
theorem card_filter_seedShaped_kCells_le (t : SpongeKeys X Z) :
    ((kCells (honestEval t π x).2).filter SeedShaped).card ≤
      ((queries (spongeOut (spongePerm t π)) x).map fun inp ↦
        if 40 < inp.length ∧ inp.length < 136 then 0 else 3 * (blocks inp).length).sum := by
  rw [snd_honestEval]
  refine (card_filter_kCells_flatMap_le SeedShaped _ _).trans
    (sum_map_le_sum_map _ _ _ fun inp ↦ ?_)
  split_ifs with hs
  · rw [kCells_inputReads_of_lt π t inp hs.2, Finset.filter_singleton]
    simp [not_seedShaped_padBlock inp hs.1 hs.2]
  · refine (Finset.card_filter_le _ _).trans ((card_kCells_le _).trans ?_)
    rw [inputReads, length_spongeReads]

/-! ### The seed derivation's cells -/

/-- The seed derivation's first `k`-cell is seed-shaped. -/
theorem seedShaped_seedCell (S₀ : MasterSeed) : SeedShaped (seedCell S₀) := by
  have hlen : (seedTag ++ littleEndianBytes 32 S₀).length = 40 := by
    rw [List.length_append, show seedTag.length = 8 from rfl, length_littleEndianBytes]
  rw [seedCell, firstBlock_of_lt _ (by rw [hlen]; norm_num)]
  exact seedShaped_seedInput S₀

theorem seedCell_injective : Function.Injective seedCell := by
  intro S₀ S₁ h
  have h₀ := firstBlock_seedInput_mem_seedCells S₀
  have h₁ := firstBlock_seedInput_mem_seedCells S₁
  simp only [seedCells, Set.mem_ofPred_eq] at h₀ h₁
  rw [← h₀, ← h₁]
  exact congrArg (fun y ↦ rateSlice y 64 256 (by norm_num)) h

/-- The capacity at which the seed derivation reads `h`. -/
def seedZ (L : HonestTable) : Z :=
  (seedRound L.keys.2.1 L.keys.2.2 L.perm L.masterSeed).2

/-- The seed derivation's state after `π`. -/
def seedMid (L : HonestTable) : X × Z :=
  L.perm (seedCell L.masterSeed, L.keys.2.1 (seedCell L.masterSeed))

theorem seedZ_eq (L : HonestTable) : seedZ L = (seedMid L).2 + L.keys.2.2 (seedMid L).1 :=
  rfl

theorem seedMid_mk (h : Z → X) (k k' : X → Z) (π' : Equiv.Perm (X × Z)) (S₀ : MasterSeed) :
    seedMid ⟨(h, k, k'), π', S₀⟩ = π' (seedCell S₀, k (seedCell S₀)) :=
  rfl

theorem seedZ_mk (h : Z → X) (k k' : X → Z) (π' : Equiv.Perm (X × Z)) (S₀ : MasterSeed) :
    seedZ ⟨(h, k, k'), π', S₀⟩ =
      (π' (seedCell S₀, k (seedCell S₀))).2 + k' (π' (seedCell S₀, k (seedCell S₀))).1 :=
  rfl

theorem seed_mk (h : Z → X) (k k' : X → Z) (π' : Equiv.Perm (X × Z)) (S₀ : MasterSeed) :
    (⟨(h, k, k'), π', S₀⟩ : HonestTable).seed =
      out256 ((seedRound k k' π' S₀).1 + h (seedRound k k' π' S₀).2) :=
  seed_eq_seedRound _

/-! ### The table split around one key -/

/-- The table split into `k` and the rest. -/
def kSplit : HonestTable ≃ (X → Z) × ((Z → X) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed) where
  toFun L := (L.keys.2.1, L.keys.1, L.keys.2.2, L.perm, L.masterSeed)
  invFun p := ⟨(p.2.1, p.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The table split into `k'` and the rest. -/
def k'Split : HonestTable ≃ (X → Z) × ((Z → X) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed) where
  toFun L := (L.keys.2.2, L.keys.1, L.keys.2.1, L.perm, L.masterSeed)
  invFun p := ⟨(p.2.1, p.2.2.1, p.1), p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The table split into `h` and the rest. -/
def hSplit : HonestTable ≃ (Z → X) × ((X → Z) × (X → Z) × Equiv.Perm (X × Z) × MasterSeed) where
  toFun L := (L.keys.1, L.keys.2.1, L.keys.2.2, L.perm, L.masterSeed)
  invFun p := ⟨(p.1, p.2.1, p.2.2.1), p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem kSplit_symm_apply (k : X → Z) (h : Z → X) (k' : X → Z) (π' : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) : kSplit.symm (k, (h, k', π', S₀)) = ⟨(h, k, k'), π', S₀⟩ :=
  rfl

theorem k'Split_symm_apply (k' : X → Z) (h : Z → X) (k : X → Z) (π' : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) : k'Split.symm (k', (h, k, π', S₀)) = ⟨(h, k, k'), π', S₀⟩ :=
  rfl

theorem hSplit_symm_apply (h : Z → X) (k k' : X → Z) (π' : Equiv.Perm (X × Z))
    (S₀ : MasterSeed) : hSplit.symm (h, (k, k', π', S₀)) = ⟨(h, k, k'), π', S₀⟩ :=
  rfl

/-- A sum over tables, with the sum over one key inside. -/
theorem sum_table_eq {R V : Type*} [Fintype R] [Fintype V] (e : HonestTable ≃ V × R)
    (F : HonestTable → ℕ) : ∑ L, F L = ∑ r, ∑ v, F (e.symm (v, r)) := by
  rw [← Fintype.sum_prod_type_right (fun p : V × R ↦ F (e.symm p))]
  exact Fintype.sum_equiv e _ _ fun L ↦ by rw [Equiv.symm_apply_apply]

theorem card_table_eq {R V : Type*} [Fintype R] [Fintype V] (e : HonestTable ≃ V × R) :
    Fintype.card HonestTable = Fintype.card R * Fintype.card V := by
  rw [Fintype.card_congr e, Fintype.card_prod, mul_comm]

/-- A bound on the inner sums over one key bounds the sum over tables. -/
theorem mul_sum_table_le {R V : Type*} [Fintype R] [Fintype V] (e : HonestTable ≃ V × R)
    (F : HonestTable → ℕ) (d B : ℕ) (h : ∀ r, d * ∑ v, F (e.symm (v, r)) ≤ Fintype.card V * B) :
    d * ∑ L, F L ≤ Fintype.card HonestTable * B := by
  rw [sum_table_eq e, Finset.mul_sum, card_table_eq e, mul_assoc]
  calc ∑ r, d * ∑ v, F (e.symm (v, r)) ≤ ∑ _r : R, Fintype.card V * B :=
        Finset.sum_le_sum fun r _ ↦ h r
    _ = Fintype.card R * (Fintype.card V * B) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- A bound on the sums over the resampled value bounds the sum over functions. -/
theorem card_mul_sum_le_of_update {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (F : (A → B) → ℕ) (c : A) (D : ℕ) (h : ∀ f, ∑ b, F (Function.update f c b) ≤ D) :
    Fintype.card B * ∑ f, F f ≤ Fintype.card (A → B) * D := by
  rw [card_mul_sum_eq_sum_sum_update F c]
  calc ∑ f : A → B, ∑ b, F (Function.update f c b) ≤ ∑ _f : A → B, D :=
        Finset.sum_le_sum fun f _ ↦ h f
    _ = Fintype.card (A → B) * D := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

instance : Nonempty HonestTable :=
  ⟨⟨(fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0), Equiv.refl _, 0⟩⟩

/-- `d a ≤ N b` gives `a ≤ N (b / d)` in `ℝ≥0∞`. -/
theorem natCast_le_mul_div_of_mul_le {a b d N : ℕ} (hd : d ≠ 0) (h : d * a ≤ N * b) :
    (a : ℝ≥0∞) ≤ N * ((b : ℝ≥0∞) / d) := by
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hd))
    (Or.inl (ENNReal.natCast_ne_top d)), mul_comm]
  exact_mod_cast h

/-! ### The seed derivation's capacity is rarely read by a computation that ignores `S₀` -/

open scoped Classical

variable (G q qs : ℕ)

/-- A good permutation, and the computation `x` reads `h` at the seed derivation's capacity. -/
noncomputable def seedHit {β : Type} (x : OracleComp LeanXmss.HashSpec β) (L : HonestTable) : ℕ :=
  if PermGood L.perm G ∧ seedZ L ∈ hCells (honestEval L.keys L.perm x).2 then 1 else 0

theorem seedHit_mk {β : Type} (x : OracleComp LeanXmss.HashSpec β) (h : Z → X) (k k' : X → Z)
    (π' : Equiv.Perm (X × Z)) (S₀ : MasterSeed) :
    seedHit G x ⟨(h, k, k'), π', S₀⟩ =
      if PermGood π' G ∧ (seedRound k k' π' S₀).2 ∈ hCells (honestEval (h, k, k') π' x).2
      then 1 else 0 :=
  rfl

/-- Reads at a seed-shaped `k`-cell: at most `qs / 2^256` of the tables put the seed
derivation's first cell among them. -/
theorem card_mul_sum_seedCell_mem_le
    (hqs : ∀ t π, ((kCells (honestEval t π x).2).filter SeedShaped).card ≤ qs) :
    2 ^ 256 * ∑ L : HonestTable,
        (if seedCell L.masterSeed ∈ kCells (honestEval L.keys L.perm x).2 then 1 else 0) ≤
      Fintype.card HonestTable * qs := by
  refine mul_sum_table_le (tableEquiv.trans (Equiv.prodComm _ _)) _ _ _ fun p ↦ ?_
  rw [card_masterSeed]
  refine Nat.mul_le_mul_left _ ?_
  change ∑ S₀ : MasterSeed,
    (if seedCell S₀ ∈ kCells (honestEval p.1 p.2 x).2 then 1 else 0) ≤ qs
  exact (sum_ite_mem_le_card_filter seedCell seedCell_injective _ SeedShaped
    seedShaped_seedCell).trans (hqs p.1 p.2)

/-- The seed derivation's intermediate rate among the `k'`-cells read, without reading `k` at
its first cell: at most `G q / |Z|` of the tables, for permutations whose rate counts are at most
`G`. -/
theorem card_mul_sum_seedMid_mem_le (hq : ∀ t π, (honestEval t π x).2.length ≤ q) :
    Fintype.card Z * ∑ L : HonestTable,
        (if PermGood L.perm G ∧
            seedCell L.masterSeed ∉ kCells (honestEval L.keys L.perm x).2 ∧
            (seedMid L).1 ∈ k'Cells (honestEval L.keys L.perm x).2 then 1 else 0) ≤
      Fintype.card HonestTable * (G * q) := by
  refine mul_sum_table_le kSplit _ _ _ fun r ↦ ?_
  obtain ⟨h, k', π', S₀⟩ := r
  refine card_mul_sum_le_of_update _ (seedCell S₀) _ fun k ↦ ?_
  simp only [kSplit_symm_apply, seedMid_mk, Function.update_self]
  calc _ ≤ ∑ w, (if PermGood π' G ∧ (π' (seedCell S₀, w)).1 ∈
          k'Cells (honestEval (h, k, k') π' x).2 then 1 else 0) := by
        refine Finset.sum_le_sum fun w _ ↦ ?_
        split_ifs with hw hw' <;> try omega
        obtain ⟨hG, hc, hm⟩ := hw
        rw [honestEval_update_k_of_not_mem x π' h k k' hc] at hm
        exact absurd ⟨hG, hm⟩ hw'
    _ ≤ G * q := by
        by_cases hG : PermGood π' G
        · simp only [hG, true_and]
          refine (sum_ite_comp_mem_le (fun w ↦ (π' (seedCell S₀, w)).1) _ G
            fun x₂ ↦ hG.rate _ x₂).trans ?_
          rw [mul_comm]
          exact Nat.mul_le_mul_left _ ((card_k'Cells_le _).trans (hq _ _))
        · simp only [hG, false_and, ↓reduceIte, Finset.sum_const_zero]
          exact Nat.zero_le _

/-- The seed derivation's capacity among the `h`-cells read, without reading `k'` at its
intermediate rate: at most `q / |Z|` of the tables. -/
theorem card_mul_sum_seedZ_mem_le (hq : ∀ t π, (honestEval t π x).2.length ≤ q) :
    Fintype.card Z * ∑ L : HonestTable,
        (if (seedMid L).1 ∉ k'Cells (honestEval L.keys L.perm x).2 ∧
            seedZ L ∈ hCells (honestEval L.keys L.perm x).2 then 1 else 0) ≤
      Fintype.card HonestTable * q := by
  refine mul_sum_table_le k'Split _ _ _ fun r ↦ ?_
  obtain ⟨h, k, π', S₀⟩ := r
  refine card_mul_sum_le_of_update _ (π' (seedCell S₀, k (seedCell S₀))).1 _ fun k' ↦ ?_
  simp only [k'Split_symm_apply, seedMid_mk, seedZ_mk, Function.update_self]
  calc _ ≤ ∑ a, (if (π' (seedCell S₀, k (seedCell S₀))).2 + a ∈
          hCells (honestEval (h, k, k') π' x).2 then 1 else 0) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        split_ifs with ha ha' <;> try omega
        obtain ⟨hc, hm⟩ := ha
        rw [honestEval_update_k'_of_not_mem x π' h k k' hc] at hm
        exact absurd hm ha'
    _ ≤ q := by
        rw [sum_ite_add_mem_eq_card]
        exact (card_hCells_le _).trans (hq _ _)

/-- **The seed derivation's capacity is rarely read by a fixed computation.** For a hash
computation `x` (which does not depend on `S₀`) with at most `q` reads, of which at most `qs` are
at seed-shaped `k`-cells, the tables with a good permutation (rate counts at most `G`) on which
`x` reads `h` at the seed derivation's capacity are at most `qs / 2^256 + (G + 1) q / |Z|` of
all. -/
theorem sum_seedHit_le (hq : ∀ t π, (honestEval t π x).2.length ≤ q)
    (hqs : ∀ t π, ((kCells (honestEval t π x).2).filter SeedShaped).card ≤ qs) :
    ((∑ L : HonestTable, seedHit G x L : ℕ) : ℝ≥0∞) ≤
      Fintype.card HonestTable * ((qs : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q / Fintype.card Z) := by
  set S₁ := ∑ L : HonestTable,
    (if seedCell L.masterSeed ∈ kCells (honestEval L.keys L.perm x).2 then 1 else 0)
  set S₂ := ∑ L : HonestTable, (if PermGood L.perm G ∧
    seedCell L.masterSeed ∉ kCells (honestEval L.keys L.perm x).2 ∧
    (seedMid L).1 ∈ k'Cells (honestEval L.keys L.perm x).2 then 1 else 0)
  set S₃ := ∑ L : HonestTable, (if (seedMid L).1 ∉ k'Cells (honestEval L.keys L.perm x).2 ∧
    seedZ L ∈ hCells (honestEval L.keys L.perm x).2 then 1 else 0)
  have hsplit : ∑ L : HonestTable, seedHit G x L ≤ S₁ + S₂ + S₃ := by
    simp only [S₁, S₂, S₃, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun L _ ↦ ?_
    unfold seedHit
    split_ifs <;> simp_all
  calc ((∑ L : HonestTable, seedHit G x L : ℕ) : ℝ≥0∞)
      ≤ (S₁ : ℝ≥0∞) + S₂ + S₃ := by exact_mod_cast hsplit
    _ ≤ Fintype.card HonestTable * ((qs : ℝ≥0∞) / (2 ^ 256 : ℕ)) +
          Fintype.card HonestTable * (((G * q : ℕ) : ℝ≥0∞) / Fintype.card Z) +
          Fintype.card HonestTable * ((q : ℝ≥0∞) / Fintype.card Z) := by
        gcongr
        · exact natCast_le_mul_div_of_mul_le (by positivity)
            (card_mul_sum_seedCell_mem_le x qs hqs)
        · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
            (card_mul_sum_seedMid_mem_le x G q hq)
        · exact natCast_le_mul_div_of_mul_le Fintype.card_ne_zero
            (card_mul_sum_seedZ_mem_le x q hq)
    _ = Fintype.card HonestTable * ((qs : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q / Fintype.card Z) := by
        rw [add_assoc, ← mul_add, ← mul_add, ENNReal.div_add_div_same]
        simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
        rw [show (G : ℝ≥0∞) * q + q = (G + 1) * q by ring]

/-! ### The scheme seed is a fresh `h` value -/

/-- **The computations from the seed, against a fixed seed.** Reparametrizing `h` at the seed
derivation's capacity, the indicator for the table's own scheme seed sums to the average over
fixed seeds `out256 v`. -/
theorem card_mul_sum_seedHit_seed_eq {β : Type} (Q : MasterSeed → OracleComp LeanXmss.HashSpec β) :
    Fintype.card X * ∑ L : HonestTable, seedHit G (Q L.seed) L =
      ∑ v : X, ∑ L : HonestTable, seedHit G (Q (out256 v)) L := by
  have hr : ∀ r, Fintype.card X * ∑ h, seedHit G (Q (hSplit.symm (h, r)).seed) (hSplit.symm (h, r))
      = ∑ v, ∑ h, seedHit G (Q (out256 v)) (hSplit.symm (h, r)) := by
    rintro ⟨k, k', π', S₀⟩
    rw [card_mul_sum_eq_sum_sum_update _ (seedRound k k' π' S₀).2, Finset.sum_comm]
    simp only [hSplit_symm_apply, seed_mk, seedHit_mk, Function.update_self,
      mem_hCells_update_iff]
    exact Fintype.sum_equiv (Equiv.addLeft (seedRound k k' π' S₀).1) _ _ fun _ ↦ rfl
  calc Fintype.card X * ∑ L : HonestTable, seedHit G (Q L.seed) L
      = ∑ r, Fintype.card X * ∑ h, seedHit G (Q (hSplit.symm (h, r)).seed) (hSplit.symm (h, r)) := by
        rw [sum_table_eq hSplit, Finset.mul_sum]
    _ = ∑ r, ∑ v, ∑ h, seedHit G (Q (out256 v)) (hSplit.symm (h, r)) :=
        Finset.sum_congr rfl fun r _ ↦ hr r
    _ = ∑ v, ∑ r, ∑ h, seedHit G (Q (out256 v)) (hSplit.symm (h, r)) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun v _ ↦ (sum_table_eq hSplit _).symm

/-- **The seed derivation's capacity is rarely read by the computations from the seed.** A bound
for every fixed seed holds for the table's own scheme seed. -/
theorem sum_seedHit_seed_le {β : Type} (Q : MasterSeed → OracleComp LeanXmss.HashSpec β)
    (b : ℝ≥0∞) (hb : ∀ S, ((∑ L : HonestTable, seedHit G (Q S) L : ℕ) : ℝ≥0∞) ≤ b) :
    ((∑ L : HonestTable, seedHit G (Q L.seed) L : ℕ) : ℝ≥0∞) ≤ b := by
  have hX0 : (Fintype.card X : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine (ENNReal.mul_le_mul_iff_right hX0 (ENNReal.natCast_ne_top _)).mp ?_
  calc (Fintype.card X : ℝ≥0∞) * ((∑ L : HonestTable, seedHit G (Q L.seed) L : ℕ) : ℝ≥0∞)
      = ∑ v : X, ((∑ L : HonestTable, seedHit G (Q (out256 v)) L : ℕ) : ℝ≥0∞) := by
        rw [← Nat.cast_mul, card_mul_sum_seedHit_seed_eq, Nat.cast_sum]
    _ ≤ ∑ _v : X, b := Finset.sum_le_sum fun v _ ↦ hb (out256 v)
    _ = Fintype.card X * b := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### The good set and its complement -/

/-- **The challenger's honest data from the scheme seed**: the honest evaluations, results and
reads, of the hash computations `Q i S`. -/
def seedData {ι : Type} {β : ι → Type} (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i))
    (t : SpongeKeys X Z) (π : Equiv.Perm (X × Z)) (S : MasterSeed) :
    ∀ i, β i × List (SpongeRead X Z) :=
  fun i ↦ honestEval t π (Q i S)

/-- **The good set at the seed level** for the reference cell `zr`: the tables on which no
computation `Q i` from the table's scheme seed reads `h` at the seed derivation's capacity or at
`zr`. Irreducible: its membership does not unfold to the enumeration of all tables. -/
@[irreducible]
noncomputable def seedGood {ι : Type} {β : ι → Type}
    (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)) (zr : Z) : Finset HonestTable :=
  Finset.univ.filter fun L ↦ ∀ i, seedZ L ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2 ∧
    zr ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2

theorem mem_seedGood {ι : Type} {β : ι → Type}
    {Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)} {zr : Z} {L : HonestTable} :
    L ∈ seedGood Q zr ↔ ∀ i, seedZ L ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2 ∧
      zr ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2 := by
  unfold seedGood
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem seedSplit_fst_fst (zr : Z) (L : HonestTable) :
    (seedSplit zr L).1.1 = (seedReparam zr L).keys := by
  simp only [seedSplit, Equiv.trans_apply, tableEquiv, Equiv.coe_fn_mk]

theorem seedSplit_fst_snd (zr : Z) (L : HonestTable) : (seedSplit zr L).1.2 = L.perm := by
  simp only [seedSplit, Equiv.trans_apply, tableEquiv, Equiv.coe_fn_mk, seedReparam_perm]

/-- **On the good set, the challenger's data is a function of the public part** of
`seedSplit zr`: the reparametrized keys and `π`, the scheme seed read at `zr`. -/
theorem seedData_eq_of_mem_seedGood {ι : Type} {β : ι → Type}
    {Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)} {zr : Z} {L : HonestTable}
    (hL : L ∈ seedGood Q zr) :
    seedData Q L.keys L.perm L.seed =
      seedData Q (seedSplit zr L).1.1 (seedSplit zr L).1.2
        (out256 ((seedSplit zr L).1.1.1 zr)) := by
  rw [← seed_eq_seedSplit zr L, seedSplit_fst_snd, seedSplit_fst_fst]
  funext i
  obtain ⟨hz, hzr⟩ := mem_seedGood.mp hL i
  change honestEval L.keys L.perm (Q i L.seed) =
    honestEval (seedReparam zr L).keys L.perm (Q i L.seed)
  refine Eq.symm (honestEval_congr (t := L.keys) (t' := (seedReparam zr L).keys) L.perm
    (Q i L.seed) fun e he ↦ ?_)
  have ha := honestEval_answeredBy L.perm L.keys (Q i L.seed) e he
  cases e with
  | h z' a =>
    have hne : z' ≠ seedZ L := fun hh ↦ hz (mem_hCells.mpr ⟨a, hh ▸ he⟩)
    have hne' : z' ≠ zr := fun hh ↦ hzr (mem_hCells.mpr ⟨a, hh ▸ he⟩)
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [seedReparam_h_of_ne zr L hne hne']
    exact ha
  | k x' a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [seedReparam_keys_snd]
    exact ha
  | k' x' a =>
    simp only [SpongeRead.AnsweredBy] at ha ⊢
    rw [seedReparam_keys_snd]
    exact ha

/-- The tables outside the good set: a bad permutation, or a computation reading `h` at `zr`, or
at the seed derivation's capacity. -/
theorem card_sub_card_seedGood_le {ι : Type} [Fintype ι] {β : ι → Type}
    (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)) (zr : Z) :
    Fintype.card HonestTable - (seedGood Q zr).card ≤
      (∑ L : HonestTable, if ¬PermGood L.perm G then 1 else 0) +
        ∑ i, ((∑ L : HonestTable,
          if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) +
          ∑ L, seedHit G (Q i L.seed) L) := by
  refine (card_sub_card_le_sum (seedGood Q zr) (fun L ↦ (if ¬PermGood L.perm G then 1 else 0) +
    ∑ i, ((if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) +
      seedHit G (Q i L.seed) L)) fun L hL ↦ ?_).trans_eq ?_
  · by_cases hG : PermGood L.perm G
    · obtain ⟨i, hi⟩ : ∃ i, ¬(seedZ L ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2 ∧
          zr ∉ hCells (honestEval L.keys L.perm (Q i L.seed)).2) := by
        by_contra hall
        push Not at hall
        exact hL (mem_seedGood.mpr fun i ↦ by simpa using hall i)
      refine le_add_left (le_trans ?_ (Finset.single_le_sum (f := fun i ↦
        (if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) +
          seedHit G (Q i L.seed) L) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)))
      unfold seedHit
      split_ifs <;> simp_all
    · exact le_add_right (by rw [ite_eq_left hG])
  · rw [Finset.sum_add_distrib, Finset.sum_comm]
    simp only [Finset.sum_add_distrib]

/-- **A good reference cell exists.** Averaged over `zr`, the tables on which a computation reads
`h` at `zr` are at most `∑ᵢ qᵢ / |Z|` of all; some `zr` does at least as well. -/
theorem exists_card_sub_card_seedGood_le {ι : Type} [Fintype ι] {β : ι → Type}
    (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)) (q : ι → ℕ)
    (hq : ∀ i t π S, (honestEval t π (Q i S)).2.length ≤ q i) :
    ∃ zr : Z, Fintype.card Z * (Fintype.card HonestTable - (seedGood Q zr).card) ≤
      Fintype.card Z * ((∑ L : HonestTable, if ¬PermGood L.perm G then 1 else 0) +
        ∑ i, ∑ L, seedHit G (Q i L.seed) L) + Fintype.card HonestTable * ∑ i, q i := by
  refine exists_card_mul_le_of_sum_le _ _ ?_
  have hB1 : ∀ i, ∑ zr : Z, ∑ L : HonestTable,
      (if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) ≤
        Fintype.card HonestTable * q i := fun i ↦ by
    rw [Finset.sum_comm]
    calc ∑ L : HonestTable, ∑ zr : Z,
          (if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0)
        ≤ ∑ _L : HonestTable, q i := Finset.sum_le_sum fun L _ ↦ by
          rw [sum_ite_mem_eq_card]
          exact (card_hCells_le _).trans (hq _ _ _ _)
      _ = Fintype.card HonestTable * q i := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  calc ∑ zr : Z, (Fintype.card HonestTable - (seedGood Q zr).card)
      ≤ ∑ zr : Z, ((∑ L : HonestTable, if ¬PermGood L.perm G then 1 else 0) +
        ∑ i, ((∑ L : HonestTable,
          if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) +
          ∑ L, seedHit G (Q i L.seed) L)) :=
        Finset.sum_le_sum fun zr _ ↦ card_sub_card_seedGood_le G Q zr
    _ = Fintype.card Z * ((∑ L : HonestTable, if ¬PermGood L.perm G then 1 else 0) +
          ∑ i, ∑ L, seedHit G (Q i L.seed) L) + ∑ i, ∑ zr : Z, ∑ L : HonestTable,
          (if zr ∈ hCells (honestEval L.keys L.perm (Q i L.seed)).2 then 1 else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
        rw [Finset.sum_comm (s := Finset.univ (α := Z))]
        ring
    _ ≤ _ := by
        refine Nat.add_le_add_left ?_ _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ ↦ hB1 i

/-- The table split into `π` and the rest. -/
def permSplit : HonestTable ≃ Equiv.Perm (X × Z) × (SpongeKeys X Z × MasterSeed) where
  toFun L := (L.perm, L.keys, L.masterSeed)
  invFun p := ⟨p.2.1, p.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The tables with a bad permutation are the fraction of bad permutations. -/
theorem card_mul_sum_not_permGood :
    Fintype.card (Equiv.Perm (X × Z)) *
        ∑ L : HonestTable, (if ¬PermGood L.perm G then 1 else 0) =
      Fintype.card HonestTable *
        (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card := by
  rw [sum_table_eq permSplit, card_table_eq permSplit, Finset.card_filter]
  rw [Finset.sum_congr rfl fun r _ ↦ show ∑ π, (if ¬PermGood (permSplit.symm (π, r)).perm G
      then 1 else 0) = ∑ π : Equiv.Perm (X × Z), (if ¬PermGood π G then 1 else 0) from rfl,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

/-- **The good set's complement is small**: for some reference cell `zr`, the fraction of tables
outside `seedGood Q zr` is at most the fraction of permutations with a rate count above `G`, plus
`qsᵢ / 2^256 + (G + 1) qᵢ / |Z|` per computation, plus `∑ᵢ qᵢ / |Z|`, where `qᵢ` bounds the reads
of `Q i` and `qsᵢ` its reads at seed-shaped `k`-cells. -/
theorem exists_seedGood_frac_le {ι : Type} [Fintype ι] {β : ι → Type}
    (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)) (q qs : ι → ℕ)
    (hq : ∀ i t π S, (honestEval t π (Q i S)).2.length ≤ q i)
    (hqs : ∀ i t π S, ((kCells (honestEval t π (Q i S)).2).filter SeedShaped).card ≤ qs i) :
    ∃ zr : Z, (Fintype.card HonestTable : ℝ≥0∞)⁻¹ *
        ((Fintype.card HonestTable - (seedGood Q zr).card : ℕ) : ℝ≥0∞) ≤
      ((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
          Fintype.card (Equiv.Perm (X × Z)) +
        ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z) +
        (∑ i, q i : ℕ) / Fintype.card Z := by
  obtain ⟨zr, hzr⟩ := exists_card_sub_card_seedGood_le G Q q hq
  refine ⟨zr, ?_⟩
  set N := Fintype.card HonestTable
  set nb := (Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card
  set P := Fintype.card (Equiv.Perm (X × Z))
  set NPG := ∑ L : HonestTable, if ¬PermGood L.perm G then 1 else 0
  set Y := (nb : ℝ≥0∞) / P + ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z) +
    (∑ i, q i : ℕ) / Fintype.card Z
  generalize N - (seedGood Q zr).card = a at hzr ⊢
  have hN0 : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZ0 : (Fintype.card Z : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP0 : (P : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hNPG : (NPG : ℝ≥0∞) = N * (nb / P) := by
    rw [← mul_div_assoc, ENNReal.eq_div_iff hP0 (ENNReal.natCast_ne_top _)]
    exact_mod_cast card_mul_sum_not_permGood G
  have hB2 : ∀ i, ((∑ L : HonestTable, seedHit G (Q i L.seed) L : ℕ) : ℝ≥0∞) ≤
      N * ((qs i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z) := fun i ↦
    sum_seedHit_seed_le G (Q i) _ fun S ↦
      sum_seedHit_le (Q i S) G (q i) (qs i) (fun t π ↦ hq i t π S) (fun t π ↦ hqs i t π S)
  have hqZ : (N : ℝ≥0∞) * (∑ i, q i : ℕ) =
      Fintype.card Z * (N * ((∑ i, q i : ℕ) / Fintype.card Z)) := by
    rw [← mul_div_assoc, ENNReal.mul_div_cancel hZ0 (ENNReal.natCast_ne_top _)]
  suffices h : (a : ℝ≥0∞) ≤ N * Y by
    calc (N : ℝ≥0∞)⁻¹ * a ≤ (N : ℝ≥0∞)⁻¹ * (N * Y) := by gcongr
      _ = Y := ENNReal.inv_mul_cancel_left hN0 (ENNReal.natCast_ne_top _)
  refine (ENNReal.mul_le_mul_iff_right hZ0 (ENNReal.natCast_ne_top _)).mp ?_
  calc (Fintype.card Z : ℝ≥0∞) * a
      ≤ Fintype.card Z * (NPG + ∑ i, ((∑ L : HonestTable, seedHit G (Q i L.seed) L : ℕ) :
          ℝ≥0∞)) + N * (∑ i, q i : ℕ) := by exact_mod_cast hzr
    _ ≤ Fintype.card Z * (N * (nb / P) +
          ∑ i, N * ((qs i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z)) +
          Fintype.card Z * (N * ((∑ i, q i : ℕ) / Fintype.card Z)) := by
        rw [hNPG, hqZ]
        gcongr with i
        exact hB2 i
    _ = Fintype.card Z * (N * Y) := by
        simp only [Y, ← Finset.mul_sum]
        ring

/-! ### The master-seed cells, averaged -/

variable {M : Type} [Fintype M] [DecidableEq M] {Λ : LocalSig.{u, v}} (I : Λ.Interp)
  {Ω : QReg → Type w} {A : QReg}

/-- **The master-seed cells, end to end.** Let the run of runtime 2 depend on the table only
through `π` and the challenger's honest data from the scheme seed (`seedData Q`): computations
`Q i` from the scheme seed, with at most `qᵢ` reads of which at most `qsᵢ` are at seed-shaped
`k`-cells. Then the mass of its `j`-th call at the cells `seedCells S₀`, averaged over the uniform
table, is at most `2^-256` plus the fraction of permutations with a rate count above `G` plus
`∑ᵢ (qsᵢ / 2^256 + (G + 1) qᵢ / |Z|) + ∑ᵢ qᵢ / |Z|`. -/
theorem avg_hiddenMass_masterSeed_le_of_seedData {ι : Type} [Fintype ι] {β : ι → Type}
    (Q : ∀ i, MasterSeed → OracleComp LeanXmss.HashSpec (β i)) (q qs : ι → ℕ)
    (hq : ∀ i t π S, (honestEval t π (Q i S)).2.length ≤ q i)
    (hqs : ∀ i t π S, ((kCells (honestEval t π (Q i S)).2).filter SeedShaped).card ≤ qs i)
    (m₀ : M)
    (y : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      QuantumComp Λ (hwSpec X Z M) Ω A)
    (ρ : Equiv.Perm (X × Z) → (∀ i, β i × List (SpongeRead X Z)) →
      Matrix (A × QReg.of (HwReg X Z M)) (A × QReg.of (HwReg X Z M)) ℂ)
    (hρ : ∀ π d, (ρ π d).PosSemidef) (hρ₁ : ∀ π d, ENNReal.ofReal (ρ π d).trace.re ≤ 1)
    (j : ℕ) :
    (Fintype.card HonestTable : ℝ≥0∞)⁻¹ * ∑ L : HonestTable, (runtime2 X Z m₀).queryWeight I
        (hiddenMass ∅ (seedCells L.masterSeed) ∅) (y L.perm (seedData Q L.keys L.perm L.seed))
        (ρ L.perm (seedData Q L.keys L.perm L.seed)) j ≤
      (2 ^ 256 : ℝ≥0∞)⁻¹ +
        (((Finset.univ.filter fun π : Equiv.Perm (X × Z) ↦ ¬PermGood π G).card : ℝ≥0∞) /
            Fintype.card (Equiv.Perm (X × Z)) +
          ∑ i, ((qs i : ℝ≥0∞) / 2 ^ 256 + (G + 1) * q i / Fintype.card Z) +
          (∑ i, q i : ℕ) / Fintype.card Z) := by
  obtain ⟨zr, hzr⟩ := exists_seedGood_frac_le G Q q qs hq hqs
  refine (avg_hiddenMass_masterSeed_le I zr m₀
    (fun L ↦ y L.perm (seedData Q L.keys L.perm L.seed))
    (fun L ↦ ρ L.perm (seedData Q L.keys L.perm L.seed)) (fun _ ↦ hρ _ _) (fun _ ↦ hρ₁ _ _)
    (fun p ↦ y p.2 (seedData Q p.1 p.2 (out256 (p.1.1 zr))))
    (fun p ↦ ρ p.2 (seedData Q p.1 p.2 (out256 (p.1.1 zr)))) (fun _ ↦ hρ _ _)
    (fun _ ↦ hρ₁ _ _) (seedGood Q zr) (fun L hL ↦ ?_) j).trans (add_le_add_right hzr _)
  have hd := seedData_eq_of_mem_seedGood hL
  rw [seedSplit_fst_snd] at hd ⊢
  exact ⟨by rw [hd], by rw [hd]⟩

end seedGood

end Quantum.Xmss.Hybrid

end
