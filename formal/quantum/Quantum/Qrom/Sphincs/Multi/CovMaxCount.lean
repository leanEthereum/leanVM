module

public import Quantum.Qrom.Sphincs.Cov
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-!
# Averages of products over random loads

Generic tools for the worst user's coverage price (`Quantum.Qrom.Sphincs.Multi.CovMax`).

* `uavg_sum`, `uavg_comp_apply`, `uavg_prod_eq`, `uavg_pi_prod`: uniform averages of sums, of one
  coordinate, over products, of products of coordinates.
* `uavg_prod_fiber`: given an index stream `x : α → I`, functions of the disjoint fibers
  `{j | x j = i}` of a uniform stream `y : α → V` average independently.
* `loadSum H α K = Σ_x Π_i H(load_i x)` over the maps `x : α → Fin K`: the recursion over the bins
  (`loadSum_fin_succ`), the exponential generating function (`tsum_loadSum`), monotonicity in the
  stream length for monotone `H` (`pow_mul_loadSum_le`), and the Poissonized bound
  (`loadSum_poisson`): with Poisson mean `K ρ` above the stream length `N`, the mean product is
  at most `(e^{-ρ} Σ_m H(m) ρ^m / m!)^K` up to the lower tail of the Poisson law
  (`sum_pow_div_factorial_le`).
-/

open Finset Nat
open scoped ENNReal
open Quantum.Sphincs (uavg_comp_equiv)
open Quantum.Xmss.Hybrid (uavg uavg_mono)

namespace Quantum.Qrom.Sphincs.Multi

/-! ## Uniform averages -/

section average

theorem uavg_sum {Θ ι : Type*} [Fintype Θ] (s : Finset ι) (f : ι → Θ → ℝ≥0∞) :
    uavg (fun θ ↦ ∑ i ∈ s, f i θ) = ∑ i ∈ s, uavg (f i) := by
  simp only [uavg]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- Averaging one coordinate of a uniform tuple. -/
theorem uavg_comp_apply {Θ ι : Type*} [Fintype Θ] [Nonempty Θ] [Fintype ι] [DecidableEq ι]
    (i : ι) (f : Θ → ℝ≥0∞) : uavg (fun D : ι → Θ ↦ f (D i)) = uavg f :=
  (uavg_comp_restrict (fun _ : Unit ↦ i) (fun _ _ _ ↦ Subsingleton.elim _ _)
    fun h ↦ f (h ())).trans (uavg_comp_equiv (Equiv.funUnique Unit Θ) f)

/-- Averaging over a product, one factor after the other. -/
theorem uavg_prod_eq {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℝ≥0∞) :
    uavg f = uavg (fun a ↦ uavg fun b ↦ f (a, b)) := by
  simp only [uavg]
  rw [Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
    Fintype.sum_prod_type, mul_assoc]
  congr 1
  exact Finset.mul_sum _ _ _

/-- A product of functions of the coordinates averages factor by factor. -/
theorem uavg_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (f : ∀ i, β i → ℝ≥0∞) :
    uavg (fun Z : (∀ i, β i) ↦ ∏ i, f i (Z i)) = ∏ i, uavg (f i) := by
  simp only [uavg]
  rw [Fintype.card_pi, Nat.cast_prod,
    ENNReal.prod_inv_distrib fun _ _ _ _ _ ↦ Or.inr (ENNReal.natCast_ne_top _),
    ← Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- **Independent fibers**: for an index stream `x`, functions of the fibers `{j | x j = i}` of a
uniform stream `y` average independently. -/
theorem uavg_prod_fiber {α I V : Type*} [Fintype α] [DecidableEq α] [Fintype I] [DecidableEq I]
    [Fintype V] [Nonempty V] (x : α → I) (g : ∀ i, ({j // x j = i} → V) → ℝ≥0∞) :
    uavg (fun y : α → V ↦ ∏ i, g i fun j ↦ y j.1) =
      ∏ i, uavg (fun y : α → V ↦ g i fun j ↦ y j.1) := by
  let e : (α → V) ≃ ∀ i, {j // x j = i} → V :=
    (Equiv.arrowCongr (Equiv.sigmaFiberEquiv x).symm (Equiv.refl V)).trans
      (Equiv.piCurry fun _ _ ↦ V)
  have he : ∀ y i, e y i = fun j ↦ y j.1 := fun _ _ ↦ rfl
  calc uavg (fun y : α → V ↦ ∏ i, g i fun j ↦ y j.1)
      = uavg (fun y ↦ (fun Z : ∀ i, {j // x j = i} → V ↦ ∏ i, g i (Z i)) (e y)) := by
        simp only [he]
    _ = ∏ i, uavg (g i) := (uavg_comp_equiv e _).trans (uavg_pi_prod g)
    _ = _ := Finset.prod_congr rfl fun i _ ↦
        (uavg_comp_restrict (fun j : {j // x j = i} ↦ j.1) Subtype.val_injective (g i)).symm

end average

/-! ## Products over the loads of a uniform index stream -/

section loads

variable (H : ℕ → ℝ≥0∞)

/-- `Σ_x Π_i H(load_i x)` over the maps `x : α → Fin K`, the load of bin `i` the size of its
fiber. -/
noncomputable def loadSum (α : Type*) [Fintype α] [DecidableEq α] (K : ℕ) : ℝ≥0∞ :=
  ∑ x : α → Fin K, ∏ i, H #(univ.filter fun j ↦ x j = i)

theorem loadSum_congr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (K : ℕ) : loadSum H α K = loadSum H β K := by
  unfold loadSum
  refine Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl _)) _ _ fun x ↦ ?_
  refine Finset.prod_congr rfl fun i _ ↦ congrArg H ?_
  exact card_equiv e fun j ↦ by simp [Equiv.arrowCongr_apply]

/-- The fiber of the bin `0` is `A`; the other bins are a map from the complement of `A`. -/
private theorem card_filter_succ {α : Type*} [Fintype α] [DecidableEq α] {K : ℕ}
    {A : Finset α} {x : α → Fin (K + 1)} (hx : (univ.filter fun j ↦ x j = 0) = A)
    (hne : ∀ j : {j // j ∉ A}, x j.1 ≠ 0) (i : Fin K) :
    #(univ.filter fun j ↦ x j = i.succ) =
      #(univ.filter fun j : {j // j ∉ A} ↦ (x j.1).pred (hne j) = i) := by
  have hA : ∀ j, x j = i.succ → j ∉ A := fun j hj hjA ↦ by
    rw [← hx, mem_filter] at hjA
    exact Fin.succ_ne_zero i (hj.symm.trans hjA.2)
  refine Finset.card_bij' (fun j hj ↦ ⟨j, hA j (mem_filter.1 hj).2⟩) (fun j _ ↦ j.1) ?_ ?_
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  · intro j hj
    rw [mem_filter] at hj ⊢
    exact ⟨mem_univ _, by rw [Fin.pred_eq_iff_eq_succ]; exact hj.2⟩
  · intro j hj
    rw [mem_filter] at hj ⊢
    exact ⟨mem_univ _, (Fin.pred_eq_iff_eq_succ _).1 hj.2⟩

/-- **The recursion over the bins**: split off the fiber `A` of bin `0`. -/
theorem loadSum_succ (α : Type*) [Fintype α] [DecidableEq α] (K : ℕ) :
    loadSum H α (K + 1) = ∑ A : Finset α, H #A * loadSum H {j // j ∉ A} K := by
  unfold loadSum
  rw [← Finset.sum_fiberwise univ fun x : α → Fin (K + 1) ↦ univ.filter fun j ↦ x j = 0]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [Finset.mul_sum]
  have hne : ∀ x ∈ univ.filter (fun x : α → Fin (K + 1) ↦ (univ.filter fun j ↦ x j = 0) = A),
      ∀ j : {j // j ∉ A}, x j.1 ≠ 0 := fun x hx j h ↦
    j.2 ((congrArg (fun s ↦ j.1 ∈ s) (mem_filter.1 hx).2).mp (mem_filter.2 ⟨mem_univ _, h⟩))
  refine Finset.sum_bij' (fun x hx j ↦ (x j.1).pred (hne x hx j))
    (fun z _ j ↦ if h : j ∈ A then 0 else (z ⟨j, h⟩).succ) (fun _ _ ↦ mem_univ _) ?_ ?_ ?_ ?_
  · intro z _
    rw [mem_filter]
    refine ⟨mem_univ _, Finset.ext fun j ↦ ?_⟩
    rw [mem_filter]
    by_cases h : j ∈ A
    · simp [h]
    · simp [h, Fin.succ_ne_zero]
  · intro x hx
    funext j
    by_cases h : j ∈ A
    · simp only [h, dite_true]
      rw [← (mem_filter.1 hx).2, mem_filter] at h
      exact h.2.symm
    · simp only [h, dite_false, Fin.succ_pred]
  · intro z _
    funext j
    simp only [j.2, dite_false, Fin.pred_succ]
  · intro x hx
    rw [Fin.prod_univ_succ, (mem_filter.1 hx).2]
    congr 1
    refine Finset.prod_congr rfl fun i _ ↦ congrArg H ?_
    exact card_filter_succ (mem_filter.1 hx).2 (hne x hx) i

theorem card_subtype_not_mem {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    Fintype.card {j // j ∉ A} = Fintype.card α - #A := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]

/-- The recursion over the bins for a stream of length `N`. -/
theorem loadSum_fin_succ (N K : ℕ) :
    loadSum H (Fin N) (K + 1) =
      ∑ m ∈ range (N + 1), (N.choose m : ℝ≥0∞) * (H m * loadSum H (Fin (N - m)) K) := by
  rw [loadSum_succ]
  have h : ∀ A : Finset (Fin N), H #A * loadSum H {j // j ∉ A} K =
      H #A * loadSum H (Fin (N - #A)) K := fun A ↦ by
    rw [loadSum_congr H (Fintype.equivFinOfCardEq ((card_subtype_not_mem A).trans
      (by rw [Fintype.card_fin])))]
  rw [Finset.sum_congr rfl fun A _ ↦ h A, ← Finset.powerset_univ]
  refine (Finset.sum_powerset_apply_card (fun m ↦ H m * loadSum H (Fin (N - m)) K)
    (x := (univ : Finset (Fin N)))).trans ?_
  rw [Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]

theorem loadSum_zero_bins (N : ℕ) : loadSum H (Fin N) 0 = if N = 0 then 1 else 0 := by
  unfold loadSum
  simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rcases N with _ | N
  · simp
  · simp

/-- `ρ^N / N! · C(N, m) = ρ^m / m! · ρ^(N-m) / (N-m)!`. -/
private theorem pow_div_factorial_mul_choose (ρ : ℝ) {m N : ℕ} (h : m ≤ N) :
    ρ ^ N / N ! * N.choose m = ρ ^ m / m ! * (ρ ^ (N - m) / (N - m)!) := by
  rw [Nat.cast_choose ℝ h, ← pow_mul_pow_sub ρ h]
  have h1 : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (factorial_ne_zero _)
  have h2 : ((N - m)! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (factorial_ne_zero _)
  have h3 : (N ! : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (factorial_ne_zero _)
  field_simp

/-- The Cauchy product in `ℝ≥0∞`. -/
theorem tsum_mul_tsum_antidiagonal (f g : ℕ → ℝ≥0∞) :
    ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 = (∑' n, f n) * ∑' n, g n := by
  calc ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2
      = ∑' c : (Σ n, antidiagonal n), f c.2.1.1 * g c.2.1.2 := by
        rw [ENNReal.tsum_sigma']
        refine tsum_congr fun n ↦ ?_
        rw [tsum_fintype]
        exact (Finset.sum_coe_sort (antidiagonal n) fun kl ↦ f kl.1 * g kl.2).symm
    _ = ∑' p : ℕ × ℕ, f p.1 * g p.2 :=
        (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq
          fun p : ℕ × ℕ ↦ f p.1 * g p.2
    _ = ∑' a, ∑' b, f a * g b := ENNReal.tsum_prod (f := fun a b ↦ f a * g b)
    _ = (∑' n, f n) * ∑' n, g n := by
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- **The exponential generating function of the loads**: Poissonizing the stream length makes
the bins independent. -/
theorem tsum_loadSum {ρ : ℝ} (hρ : 0 ≤ ρ) (K : ℕ) :
    ∑' N, ENNReal.ofReal (ρ ^ N / N !) * loadSum H (Fin N) K =
      (∑' m, H m * ENNReal.ofReal (ρ ^ m / m !)) ^ K := by
  induction K with
  | zero =>
    rw [pow_zero, tsum_eq_single 0 fun N hN ↦ by simp [loadSum_zero_bins, hN]]
    simp [loadSum_zero_bins]
  | succ K ih =>
    have hterm : ∀ N, ENNReal.ofReal (ρ ^ N / N !) * loadSum H (Fin N) (K + 1) =
        ∑ kl ∈ antidiagonal N, H kl.1 * ENNReal.ofReal (ρ ^ kl.1 / kl.1 !) *
          (ENNReal.ofReal (ρ ^ kl.2 / kl.2 !) * loadSum H (Fin kl.2) K) := fun N ↦ by
      rw [loadSum_fin_succ, Finset.mul_sum,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun k l ↦ H k *
          ENNReal.ofReal (ρ ^ k / k !) * (ENNReal.ofReal (ρ ^ l / l !) * loadSum H (Fin l) K))]
      refine Finset.sum_congr rfl fun m hm ↦ ?_
      have hmN : m ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hm)
      have e := pow_div_factorial_mul_choose ρ hmN
      have e' : ENNReal.ofReal (ρ ^ N / N !) * (N.choose m : ℝ≥0∞) =
          ENNReal.ofReal (ρ ^ m / m !) * ENNReal.ofReal (ρ ^ (N - m) / (N - m)!) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), e,
          ENNReal.ofReal_mul (by positivity)]
      calc ENNReal.ofReal (ρ ^ N / N !) * ((N.choose m : ℝ≥0∞) *
            (H m * loadSum H (Fin (N - m)) K))
          = (ENNReal.ofReal (ρ ^ N / N !) * (N.choose m : ℝ≥0∞)) *
            (H m * loadSum H (Fin (N - m)) K) := by rw [mul_assoc]
        _ = _ := by rw [e']; ring
    simp only [hterm]
    refine (tsum_mul_tsum_antidiagonal (fun k ↦ H k * ENNReal.ofReal (ρ ^ k / k !))
      fun l ↦ ENNReal.ofReal (ρ ^ l / l !) * loadSum H (Fin l) K).trans ?_
    rw [ih, _root_.pow_succ']

theorem sum_fin_cons {N K : ℕ} (F : (Fin (N + 1) → Fin K) → ℝ≥0∞) :
    ∑ x, F x = ∑ b : Fin K, ∑ x : Fin N → Fin K, F (Fin.cons b x) := by
  calc ∑ x, F x = ∑ p : Fin K × (Fin N → Fin K), F (Fin.cons p.1 p.2) :=
        (Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Fin K) _ _ fun _ ↦ rfl).symm
    _ = _ := Fintype.sum_prod_type' fun b x ↦ F (Fin.cons b x)

/-- **More balls, larger product**: for monotone `H`, adding a uniform ball to each stream
multiplies the sum by at least `K`. -/
theorem loadSum_mul_le_succ (hH : Monotone H) (N K : ℕ) :
    (K : ℝ≥0∞) * loadSum H (Fin N) K ≤ loadSum H (Fin (N + 1)) K := by
  unfold loadSum
  rw [sum_fin_cons fun x ↦ ∏ i, H #(univ.filter fun j ↦ x j = i)]
  calc (K : ℝ≥0∞) * ∑ x : Fin N → Fin K, ∏ i, H #(univ.filter fun j ↦ x j = i)
      = ∑ b : Fin K, ∑ x : Fin N → Fin K, ∏ i, H #(univ.filter fun j ↦ x j = i) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := by
        refine Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
        refine Finset.prod_le_prod fun i _ ↦ hH ?_
        refine Finset.card_le_card_of_injOn Fin.succ (fun j hj ↦ ?_) (Fin.succ_injective _).injOn
        rw [mem_coe, mem_filter] at hj ⊢
        exact ⟨mem_univ _, by rw [Fin.cons_succ]; exact hj.2⟩

theorem pow_mul_loadSum_le (hH : Monotone H) (N K d : ℕ) :
    (K : ℝ≥0∞) ^ d * loadSum H (Fin N) K ≤ loadSum H (Fin (N + d)) K := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc (K : ℝ≥0∞) ^ (d + 1) * loadSum H (Fin N) K
        = K * ((K : ℝ≥0∞) ^ d * loadSum H (Fin N) K) := by rw [_root_.pow_succ', mul_assoc]
      _ ≤ K * loadSum H (Fin (N + d)) K := by gcongr
      _ ≤ loadSum H (Fin (N + d + 1)) K := loadSum_mul_le_succ H hH _ K

theorem hasSum_pow_div_factorial (x : ℝ) : HasSum (fun n ↦ x ^ n / n !) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

theorem tsum_ofReal_pow_div_factorial {x : ℝ} (hx : 0 ≤ x) :
    ∑' n, ENNReal.ofReal (x ^ n / n !) = ENNReal.ofReal (Real.exp x) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)
    (hasSum_pow_div_factorial x).summable, (hasSum_pow_div_factorial x).tsum_eq]

/-- The Poisson upper part: `Σ'_{i} R^(N+i) / (N+i)! = e^R - Σ_{i<N} R^i / i!`. -/
theorem tsum_ofReal_pow_div_factorial_add {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    ∑' i, ENNReal.ofReal (R ^ (i + N) / (i + N)!) =
      ENNReal.ofReal (Real.exp R - ∑ i ∈ range N, R ^ i / i !) := by
  have hs := (hasSum_pow_div_factorial R).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity)
    ((summable_nat_add_iff N).2 hs), ← (hasSum_pow_div_factorial R).tsum_eq,
    ← hs.sum_add_tsum_nat_add N, add_sub_cancel_left]

/-- **The Poissonized bound**: with Poisson mean `K ρ`, `(1 - η) E_N ≤ (e^{-ρ} G)^K`, `E_N` the
mean product over uniform streams of length `N`, `G = Σ_m H(m) ρ^m / m!` and
`η = e^{-Kρ} Σ_{i<N} (Kρ)^i / i!` the Poisson mass below `N`. -/
theorem loadSum_poisson (hH : Monotone H) (N K : ℕ) (hK : 0 < K) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ENNReal.ofReal (1 - Real.exp (-(K * ρ)) * ∑ i ∈ range N, (K * ρ) ^ i / i !) *
        (loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N) ≤
      (ENNReal.ofReal (Real.exp (-ρ)) * ∑' m, H m * ENNReal.ofReal (ρ ^ m / m !)) ^ K := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hK.ne'
  have hKt : (K : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top K
  have hR : 0 ≤ (K : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg K) hρ
  set E := loadSum H (Fin N) K / (K : ℝ≥0∞) ^ N with hE
  -- each later stream length has mean at least `E`
  have hmono : ∀ i, ENNReal.ofReal (((K : ℝ) * ρ) ^ (i + N) / (i + N)!) * E ≤
      ENNReal.ofReal (ρ ^ (i + N) / (i + N)!) * loadSum H (Fin (i + N)) K := fun i ↦ by
    have h1 : ENNReal.ofReal (((K : ℝ) * ρ) ^ (i + N) / (i + N)!) =
        (K : ℝ≥0∞) ^ (i + N) * ENNReal.ofReal (ρ ^ (i + N) / (i + N)!) := by
      rw [mul_pow, mul_div_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow
        (Nat.cast_nonneg K), ENNReal.ofReal_natCast]
    have h2 : (K : ℝ≥0∞) ^ (i + N) * E ≤ loadSum H (Fin (i + N)) K := by
      calc (K : ℝ≥0∞) ^ (i + N) * E
          = (K : ℝ≥0∞) ^ i * ((K : ℝ≥0∞) ^ N * E) := by rw [pow_add, mul_assoc]
        _ = (K : ℝ≥0∞) ^ i * loadSum H (Fin N) K := by
            rw [ENNReal.mul_div_cancel (pow_ne_zero _ hK0) (ENNReal.pow_ne_top hKt)]
        _ ≤ loadSum H (Fin (N + i)) K := pow_mul_loadSum_le H hH N K i
        _ = loadSum H (Fin (i + N)) K := by rw [Nat.add_comm]
    calc ENNReal.ofReal (((K : ℝ) * ρ) ^ (i + N) / (i + N)!) * E
        = ENNReal.ofReal (ρ ^ (i + N) / (i + N)!) * ((K : ℝ≥0∞) ^ (i + N) * E) := by
          rw [h1]; ring
      _ ≤ _ := by gcongr
  have hsum : ENNReal.ofReal (Real.exp ((K : ℝ) * ρ) - ∑ i ∈ range N, ((K : ℝ) * ρ) ^ i / i !) *
      E ≤ (∑' m, H m * ENNReal.ofReal (ρ ^ m / m !)) ^ K := by
    rw [← tsum_ofReal_pow_div_factorial_add hR N, ← ENNReal.tsum_mul_right, ← tsum_loadSum H hρ K]
    calc ∑' i, ENNReal.ofReal (((K : ℝ) * ρ) ^ (i + N) / (i + N)!) * E
        ≤ ∑' i, ENNReal.ofReal (ρ ^ (i + N) / (i + N)!) * loadSum H (Fin (i + N)) K :=
          ENNReal.tsum_le_tsum hmono
      _ ≤ ∑' n, ENNReal.ofReal (ρ ^ n / n !) * loadSum H (Fin n) K :=
          ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective N)
            fun n ↦ ENNReal.ofReal (ρ ^ n / n !) * loadSum H (Fin n) K
  have hexp : ENNReal.ofReal (Real.exp (-((K : ℝ) * ρ))) =
      ENNReal.ofReal (Real.exp (-ρ)) ^ K := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, mul_neg]
  have hone : 1 - Real.exp (-((K : ℝ) * ρ)) * ∑ i ∈ range N, ((K : ℝ) * ρ) ^ i / i ! =
      Real.exp (-((K : ℝ) * ρ)) *
        (Real.exp ((K : ℝ) * ρ) - ∑ i ∈ range N, ((K : ℝ) * ρ) ^ i / i !) := by
    rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [hone, ENNReal.ofReal_mul (Real.exp_pos _).le, hexp, mul_assoc, mul_pow]
  gcongr

/-- **The Poisson lower tail**: for `N ≤ R`, `Σ_{i<N} R^i / i! ≤ (R/N)^N e^N`. -/
theorem sum_pow_div_factorial_le {R : ℝ} {N : ℕ} (hN : 0 < N) (hR : (N : ℝ) ≤ R) :
    ∑ i ∈ range N, R ^ i / i ! ≤ (R / N) ^ N * Real.exp N := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hq : 1 ≤ R / N := (one_le_div hN0).2 hR
  calc ∑ i ∈ range N, R ^ i / i !
      = ∑ i ∈ range N, (R / N) ^ i * ((N : ℝ) ^ i / i !) := Finset.sum_congr rfl fun i _ ↦ by
        have := pow_ne_zero i hN0.ne'
        rw [div_pow, div_mul_div_cancel₀ this]
    _ ≤ ∑ i ∈ range N, (R / N) ^ N * ((N : ℝ) ^ i / i !) := Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hq (mem_range.1 hi).le) (by positivity)
    _ = (R / N) ^ N * ∑ i ∈ range N, (N : ℝ) ^ i / i ! := (Finset.mul_sum _ _ _).symm
    _ ≤ (R / N) ^ N * Real.exp N :=
        mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg hN0.le N) (by positivity)

end loads

end Quantum.Qrom.Sphincs.Multi

end
