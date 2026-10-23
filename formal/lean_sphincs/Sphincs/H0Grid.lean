import Sphincs.H0Max

/-! **Abel summation on the grid `{0..4}^d`.** For a function `g` on the grid and the forward
difference `Δ g(m) = g(m) - g(m + e_i)` along every axis (no difference at the top), every value
telescopes: `g(x) = Σ_{m ≥ x} Δ* g(m)`. Hence `E[g(M)] = Σ_m P(M ≤ m) Δ* g(m)` for any random grid
point; for the maximum of `u` uniform codewords, `P(M ≤ m) = H(m)^u`. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### One axis -/

/-- The forward difference of a function on `{0..4}`, with no difference at `4`. -/
def D1 (h : FPos → ℝ) (y : FPos) : ℝ :=
  h y - if hy : y.val < chainTop then h ⟨y.val + 1, by simp only [chainTop] at hy ⊢; omega⟩ else 0

theorem telescope1 (h : FPos → ℝ) (x : FPos) :
    ∑ y : FPos, (if x ≤ y then (1 : ℝ) else 0) * D1 h y = h x := by
  have key : ∀ (h : Fin 5 → ℝ) (x : Fin 5), ∑ y : Fin 5, (if x ≤ y then (1 : ℝ) else 0) *
      (h y - if hy : y.val < 4 then h ⟨y.val + 1, by omega⟩ else 0) = h x := by
    intro h x
    fin_cases x <;> simp [Fin.sum_univ_five] <;> ring_nf <;> rfl
  unfold D1
  exact key h x

/-! ### The forward difference on the grid -/

/-- The forward difference along every axis. -/
noncomputable def deltaF : (d : ℕ) → ((Fin d → FPos) → ℝ) → (Fin d → FPos) → ℝ
  | 0, g => g
  | d + 1, g => fun m => D1 (fun y => deltaF d (fun m' => g (Fin.cons y m')) (Fin.tail m)) (m 0)

theorem sum_fin_succ_fun {d : ℕ} (F : (Fin (d + 1) → FPos) → ℝ) :
    ∑ m : Fin (d + 1) → FPos, F m = ∑ y : FPos, ∑ m' : Fin d → FPos, F (Fin.cons y m') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => FPos).symm F (fun p => F (Fin.cons p.1 p.2))
    fun m => by simp [Fin.consEquiv]).trans rfl

/-- **Telescoping.** -/
theorem telescope : ∀ (d : ℕ) (g : (Fin d → FPos) → ℝ) (x : Fin d → FPos),
    g x = ∑ m : Fin d → FPos, (if ∀ i, x i ≤ m i then (1 : ℝ) else 0) * deltaF d g m
  | 0, g, x => by
      rw [Fintype.sum_unique]
      simp only [deltaF]
      rw [ite_eq_left (fun i => i.elim0), one_mul]
      congr 1
      funext i
      exact i.elim0
  | d + 1, g, x => by
      rw [sum_fin_succ_fun]
      have hind : ∀ (y : FPos) (m' : Fin d → FPos),
          (if ∀ i, x i ≤ (Fin.cons y m' : Fin (d + 1) → FPos) i then (1 : ℝ) else 0) =
            (if x 0 ≤ y then (1 : ℝ) else 0) * (if ∀ i, Fin.tail x i ≤ m' i then (1 : ℝ) else 0) := by
        intro y m'
        by_cases h0 : x 0 ≤ y
        · rw [ite_eq_left h0, one_mul]
          congr 1
          apply propext
          constructor
          · intro h i
            have := h i.succ
            simpa [Fin.tail] using this
          · intro h i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa using h0
            · simpa [Fin.tail] using h j
        · rw [ite_eq_right h0, zero_mul, ite_eq_right]
          intro h
          exact h0 (by simpa using h 0)
      have hdel : ∀ (y : FPos) (m' : Fin d → FPos), deltaF (d + 1) g (Fin.cons y m') =
          D1 (fun y' => deltaF d (fun m'' => g (Fin.cons y' m'')) m') y := by
        intro y m'
        simp only [deltaF, Fin.tail_cons, Fin.cons_zero]
      simp only [hind, hdel]
      have hswap : (∑ y : FPos, ∑ m' : Fin d → FPos, (if x 0 ≤ y then (1 : ℝ) else 0) *
          (if ∀ i, Fin.tail x i ≤ m' i then (1 : ℝ) else 0) *
            D1 (fun y' => deltaF d (fun m'' => g (Fin.cons y' m'')) m') y) =
          ∑ m' : Fin d → FPos, (if ∀ i, Fin.tail x i ≤ m' i then (1 : ℝ) else 0) *
            ∑ y : FPos, (if x 0 ≤ y then (1 : ℝ) else 0) *
              D1 (fun y' => deltaF d (fun m'' => g (Fin.cons y' m'')) m') y := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
      rw [hswap]
      simp only [telescope1]
      rw [← telescope d (fun m'' => g (Fin.cons (x 0) m'')) (Fin.tail x)]
      simp

/-- **Abel summation.** For a random grid point, the expectation of `g` is the sum of the CDF
times the forward difference of `g`. -/
theorem avgR_abel {α : Type} [Fintype α] {d : ℕ} (M : α → Fin d → FPos) (g : (Fin d → FPos) → ℝ) :
    avgR (fun a => g (M a)) =
      ∑ m : Fin d → FPos, avgR (fun a => if ∀ i, M a i ≤ m i then (1 : ℝ) else 0) * deltaF d g m := by
  have h : ∀ a, g (M a) = ∑ m : Fin d → FPos, (if ∀ i, M a i ≤ m i then (1 : ℝ) else 0) * deltaF d g m :=
    fun a => telescope d g (M a)
  simp only [h]
  rw [avgR_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show (fun a => (if ∀ i, M a i ≤ m i then (1 : ℝ) else 0) * deltaF d g m) =
    fun a => deltaF d g m * (if ∀ i, M a i ≤ m i then (1 : ℝ) else 0) from funext fun a => mul_comm _ _,
    avgR_const_mul, mul_comm]

/-- The CDF of the componentwise maximum of `u` uniform codewords. -/
theorem avgR_maxCw_le {u : ℕ} (m : FChain → FPos) :
    avgR (fun c : Fin u → LutIdx => if ∀ i, maxCw c i ≤ m i then (1 : ℝ) else 0) = Hm m ^ u := by
  unfold Hm
  rw [← avgR_pow_prod]
  refine congrArg avgR (funext fun c => ?_)
  have hiff : (∀ i, maxCw c i ≤ m i) ↔ ∀ k, ∀ i, (lut (c k) i).val ≤ (m i).val := by
    constructor
    · intro h k i
      exact le_trans (Finset.le_sup (f := fun k => (lut (c k) i).val) (Finset.mem_univ k))
        (Fin.le_iff_val_le_val.1 (h i))
    · intro h i
      refine Fin.le_iff_val_le_val.2 ?_
      show (Finset.univ.sup fun k => (lut (c k) i).val) ≤ (m i).val
      exact Finset.sup_le fun k _ => h k i
  by_cases hall : ∀ i, maxCw c i ≤ m i
  · rw [ite_eq_left hall]
    exact (Finset.prod_eq_one fun k _ => ite_eq_left (hiff.1 hall k)).symm
  · rw [ite_eq_right hall]
    rw [hiff] at hall
    push Not at hall
    obtain ⟨k, hk⟩ := hall
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (ite_eq_right (by push Not; exact hk))).symm

/-- **`f(u)` on the grid.** -/
theorem fR_grid (u : ℕ) : fR u = ∑ m : FChain → FPos, Hm m ^ u * deltaF childChains Hm m := by
  rw [fR_eq_max, avgR_abel maxCw Hm]
  simp only [avgR_maxCw_le]

/-- **`f2(u)` on the grid.** -/
theorem f2R_grid (u : ℕ) : f2R u = ∑ m : FChain → FPos, Hm m ^ u * deltaF childChains (fun m => Hm m ^ 2) m := by
  rw [f2R_eq_max, avgR_abel maxCw (fun m => Hm m ^ 2)]
  simp only [avgR_maxCw_le]

end Sphincs.Security.H0
