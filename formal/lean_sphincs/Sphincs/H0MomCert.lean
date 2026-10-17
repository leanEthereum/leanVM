import Sphincs.H0FTab
import SphincsFors.H0SplitCert

/-! **Rational upper bounds of the per-tree moments.** From the kernel-checked codeword tables
(`f(u)` exactly for `u ≤ 40`, `f(u) ≤ 1` beyond) the closed forms of `Ψ1(n)` and `Ψ2(n)` give
rational upper bounds, rounded up to `2^-128` after each stage. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete SphincsFors.Security.H0

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

/-! ### The codeword-level sums are probabilities -/

theorem Hm_nonneg (m : FChain → FPos) : 0 ≤ Hm m := by
  unfold Hm avgR
  exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) (Finset.sum_nonneg fun w _ => by split_ifs <;> norm_num)

theorem Hm_le_one (m : FChain → FPos) : Hm m ≤ 1 := by
  unfold Hm
  calc (avgR fun w : LutIdx => if ∀ i, (lut w i).val ≤ (m i).val then (1 : ℝ) else 0)
      ≤ avgR fun _ : LutIdx => (1 : ℝ) := by
        unfold avgR
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => by split_ifs <;> norm_num)
          (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = 1 := avgR_const 1

theorem avgR_mem_unit {α : Type} [Fintype α] [Nonempty α] (g : α → ℝ) (h0 : ∀ a, 0 ≤ g a) (h1 : ∀ a, g a ≤ 1) :
    0 ≤ avgR g ∧ avgR g ≤ 1 := by
  unfold avgR
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  refine ⟨mul_nonneg (inv_nonneg.2 hc.le) (Finset.sum_nonneg fun a _ => h0 a), ?_⟩
  calc (Fintype.card α : ℝ)⁻¹ * ∑ a, g a ≤ (Fintype.card α : ℝ)⁻¹ * ∑ _a : α, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h1 a) (inv_nonneg.2 hc.le)
    _ = 1 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc.ne']

theorem fR_unit (u : ℕ) : 0 ≤ fR u ∧ fR u ≤ 1 := by
  rw [fR_eq_max]
  exact avgR_mem_unit _ (fun c => Hm_nonneg _) (fun c => Hm_le_one _)

theorem f2R_unit (u : ℕ) : 0 ≤ f2R u ∧ f2R u ≤ 1 := by
  rw [f2R_eq_max]
  exact avgR_mem_unit _ (fun c => sq_nonneg _) (fun c => pow_le_one₀ (Hm_nonneg _) (Hm_le_one _))

/-! ### The tables as upper bounds -/

/-- Upper bound of `f(u)`: exact for `u ≤ 40`, one beyond. -/
def fQ (u : ℕ) : ℚ := if u ≤ 40 then (fTab.getD u 0 : ℚ) / 256 ^ (u + 1) else 1

/-- Upper bound of `f2(u)`. -/
def f2Q (u : ℕ) : ℚ := if u ≤ 40 then (f2Tab.getD u 0 : ℚ) / 256 ^ (u + 2) else 1

theorem fR_le_fQ (u : ℕ) : fR u ≤ (fQ u : ℝ) := by
  unfold fQ
  split_ifs with hu
  · rw [fR_num, fNum, ← getD_sumTL 40 u hu, fTab_eq]
    push_cast
    rfl
  · exact_mod_cast (fR_unit u).2

theorem f2R_le_f2Q (u : ℕ) : f2R u ≤ (f2Q u : ℝ) := by
  unfold f2Q
  split_ifs with hu
  · rw [f2R_num, f2Num, ← getD_sumTL 40 u hu, f2Tab_eq]
    push_cast
    rfl
  · exact_mod_cast (f2R_unit u).2

/-! ### Binomial rows -/

/-- The rows of Pascal's triangle. -/
def pascal : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.zipWith (· + ·) (0 :: pascal n) (pascal n ++ [0])

theorem length_pascal : ∀ n, (pascal n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [pascal, List.length_zipWith, length_pascal n]

theorem pascal_getD : ∀ n k, (pascal n).getD k 0 = n.choose k
  | 0, k => by cases k <;> simp [pascal]
  | n + 1, k => by
      have hl := length_pascal n
      rcases lt_or_ge k (n + 2) with hk | hk
      · rw [List.getD_eq_getElem _ _ (by simp [pascal, List.length_zipWith, hl]; omega)]
        simp only [pascal, List.getElem_zipWith]
        cases k with
        | zero =>
            have h0 := pascal_getD n 0
            rw [List.getD_eq_getElem _ _ (by omega)] at h0
            rw [List.getElem_cons_zero, List.getElem_append_left (by omega), h0]
            simp
        | succ k =>
            rw [List.getElem_cons_succ, Nat.choose_succ_succ]
            have h1 := pascal_getD n k
            have h2 := pascal_getD n (k + 1)
            rw [List.getD_eq_getElem _ _ (by omega)] at h1
            rw [← h1]
            rcases lt_or_ge (k + 1) (n + 1) with hk' | hk'
            · rw [List.getElem_append_left (by omega)]
              rw [List.getD_eq_getElem _ _ (by omega)] at h2
              rw [h2]
            · rw [List.getElem_append_right (by omega)]
              have : k + 1 - (pascal n).length = 0 := by omega
              simp only [this, List.getElem_singleton, Nat.choose_eq_zero_of_lt (by omega : n < k + 1)]
      · rw [List.getD_eq_default _ _ (by simp [pascal, List.length_zipWith, hl]; omega),
          Nat.choose_eq_zero_of_lt (by omega)]

/-- A sum over `range` as a list sum. -/
theorem list_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]; simp


/-! ### The rational bounds -/

/-- A binomial weight `C(n,i) a^i b^(n-i)`. -/
def binQ (n i : ℕ) (a b : ℚ) : ℚ := ((pascal n).getD i 0 : ℚ) * a ^ i * b ^ (n - i)

/-- The bound of `μ_i`. -/
def μQ (i : ℕ) : ℚ := rup (((List.range (i + 1)).map fun u => binQ i u (1 / 8) (7 / 8) * fQ u).sum) 128

/-- The bounds of `μ_i`, `i ≤ 150`. -/
def μL : List ℚ := (List.range 151).map μQ

/-- The bound of `Σ_u C(s,u) f(u) f(s-u)`. -/
def hQ (s : ℕ) : ℚ :=
  rup (((List.range (s + 1)).map fun u => ((pascal s).getD u 0 : ℚ) * fQ u * fQ (s - u)).sum) 128

def hL : List ℚ := (List.range 151).map hQ

/-- The bound of `ν_i`. -/
def νQ (i : ℕ) : ℚ :=
  rup (1 / 8 * ((List.range (i + 1)).map fun u => binQ i u (1 / 8) (7 / 8) * f2Q u).sum +
    7 / 8 * ((List.range (i + 1)).map fun s => binQ i s (1 / 8) (6 / 8) * hL.getD s 0).sum) 128

def νL : List ℚ := (List.range 151).map νQ

/-- The bound of `Σ_i C(s,i) μ_i^2 μ_(s-i)^2`. -/
def gQ (s : ℕ) : ℚ :=
  rup (((List.range (s + 1)).map fun i => ((pascal s).getD i 0 : ℚ) * μL.getD i 0 ^ 2 * μL.getD (s - i) 0 ^ 2).sum) 128

def gL : List ℚ := (List.range 151).map gQ

/-- The bound of `Ψ1(n)`. -/
def P1Q (n : ℕ) : ℚ :=
  rup (((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * μL.getD i 0 ^ 2).sum) 128

/-- The bound of `Ψ2(n)`. -/
def P2Q (n : ℕ) : ℚ :=
  rup (1 / 16 * ((List.range (n + 1)).map fun i => binQ n i (1 / 16) (15 / 16) * νL.getD i 0 ^ 2).sum +
    15 / 16 * ((List.range (n + 1)).map fun s => binQ n s (1 / 16) (14 / 16) * gL.getD s 0).sum) 128

/-! ### Soundness -/

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) (N i : ℕ) (hi : i < N) :
    ((List.range N).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_range]

theorem binQ_cast (n i : ℕ) (a b : ℚ) :
    ((binQ n i a b : ℚ) : ℝ) = (a : ℝ) ^ i * (b : ℝ) ^ (n - i) * (n.choose i : ℝ) := by
  unfold binQ
  rw [pascal_getD]
  push_cast
  ring

theorem binQ_nonneg (n i : ℕ) {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ binQ n i a b := by
  unfold binQ; positivity

theorem rup_ge_real {x : ℚ} {y : ℝ} (h : y ≤ (x : ℝ)) (P : ℕ) : y ≤ ((rup x P : ℚ) : ℝ) :=
  le_trans h (by exact_mod_cast le_rup x P)

theorem fQ_nonneg (u : ℕ) : (0 : ℝ) ≤ (fQ u : ℝ) := le_trans (fR_unit u).1 (fR_le_fQ u)

theorem μR_bounds (i : ℕ) : 0 ≤ μR i ∧ μR i ≤ (μQ i : ℝ) := by
  rw [μR_eq]
  refine ⟨Finset.sum_nonneg fun u _ => mul_nonneg (by positivity) (fR_unit u).1, ?_⟩
  unfold μQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun u _ => ?_
  rw [binQ_cast]
  push_cast
  exact mul_le_mul_of_nonneg_left (fR_le_fQ u) (by positivity)

theorem μL_getD (i : ℕ) (hi : i ≤ 150) : μL.getD i 0 = μQ i := getD_map_range μQ 0 151 i (by omega)


theorem hL_getD (s : ℕ) (hs : s ≤ 150) : hL.getD s 0 = hQ s := getD_map_range hQ 0 151 s (by omega)
theorem νL_getD (i : ℕ) (hi : i ≤ 150) : νL.getD i 0 = νQ i := getD_map_range νQ 0 151 i (by omega)
theorem gL_getD (s : ℕ) (hs : s ≤ 150) : gL.getD s 0 = gQ s := getD_map_range gQ 0 151 s (by omega)

theorem hR_le (s : ℕ) :
    ∑ u ∈ Finset.range (s + 1), (s.choose u : ℝ) * fR u * fR (s - u) ≤ (hQ s : ℝ) := by
  unfold hQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun u _ => ?_
  rw [pascal_getD]
  push_cast
  have h1 := fR_unit u
  have h2 := fR_unit (s - u)
  have h3 := fR_le_fQ u
  have h4 := fR_le_fQ (s - u)
  have hc : (0 : ℝ) ≤ s.choose u := Nat.cast_nonneg _
  calc (s.choose u : ℝ) * fR u * fR (s - u) ≤ (s.choose u : ℝ) * (fQ u : ℝ) * fR (s - u) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc) h2.1
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (mul_nonneg hc (fQ_nonneg u))

theorem νR_bounds (i : ℕ) (hi : i ≤ 150) : 0 ≤ νR i ∧ νR i ≤ (νQ i : ℝ) := by
  unfold νR
  rw [νeqR_eq, νneR_eq]
  constructor
  · refine add_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg fun u _ => mul_nonneg (by positivity)
      (f2R_unit u).1)) (mul_nonneg (by norm_num) (Finset.sum_nonneg fun s _ => mul_nonneg (by positivity)
        (Finset.sum_nonneg fun u _ => mul_nonneg (mul_nonneg (by positivity) (fR_unit u).1) (fR_unit _).1)))
  unfold νQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range, list_sum_range]
  push_cast
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) (by norm_num))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s hs => ?_) (by norm_num))
  · rw [binQ_cast]
    push_cast
    exact mul_le_mul_of_nonneg_left (f2R_le_f2Q u) (by positivity)
  · rw [binQ_cast, hL_getD s (by have := Finset.mem_range.1 hs; omega)]
    push_cast
    exact mul_le_mul_of_nonneg_left (hR_le s) (by positivity)

theorem gR_le (s : ℕ) (hs : s ≤ 150) :
    ∑ i ∈ Finset.range (s + 1), (s.choose i : ℝ) * μR i ^ 2 * μR (s - i) ^ 2 ≤ (gQ s : ℝ) := by
  unfold gQ
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [pascal_getD, μL_getD i (by omega), μL_getD (s - i) (by omega)]
  push_cast
  have h1 := μR_bounds i
  have h2 := μR_bounds (s - i)
  gcongr
  · exact h1.1
  · exact h1.2
  · exact h2.1
  · exact h2.2

/-- **The first moment bound.** -/
theorem Ψ1R_le (n : ℕ) (hn : n ≤ 150) : Ψ1R n ≤ (P1Q n : ℝ) := by
  rw [Ψ1R_eq]
  unfold P1Q
  refine rup_ge_real ?_ 128
  rw [list_sum_range]
  push_cast
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  rw [binQ_cast, μL_getD i (by omega)]
  push_cast
  have h1 := μR_bounds i
  gcongr
  · exact h1.1
  · exact h1.2

/-- **The second moment bound.** -/
theorem Ψ2R_le (n : ℕ) (hn : n ≤ 150) : Ψ2R n ≤ (P2Q n : ℝ) := by
  rw [Ψ2R_eq]
  unfold P2Q
  refine rup_ge_real ?_ 128
  rw [list_sum_range, list_sum_range]
  push_cast
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (by norm_num))
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s hs => ?_) (by norm_num))
  · have hi' := Finset.mem_range.1 hi
    rw [binQ_cast, νL_getD i (by omega)]
    push_cast
    have h1 := νR_bounds i (by omega)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1.1 h1.2 2) (by positivity)
  · have hs' := Finset.mem_range.1 hs
    rw [binQ_cast, gL_getD s (by omega)]
    push_cast
    exact mul_le_mul_of_nonneg_left (gR_le s (by omega)) (by positivity)

end Sphincs.Security.H0
