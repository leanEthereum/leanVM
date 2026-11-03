import FORS.CoverBound.PerIndex

/-! **The near moment.** A target is *near covered* at the free tree `κ` when every other tree is
covered. The near value of the marks at an index, summed over the free tree, has per-index mean
`Σ_κ Ψ1(n)^(k-1)`: the free tree contributes a factor one. -/

open ENNReal

namespace FORS.Security.H0

variable [Params]

open Concrete H0Avg FORS.Base.Domination

set_option linter.unusedSectionVars false

/-! ### The near value of an index -/

open Classical in
/-- The per-tree factor of the near value: one at the free tree `κ`, the cover fraction elsewhere. -/
noncomputable def nearFactor (κ κ' : FTree) (Xs : Multiset FLeaf) : ℝ≥0∞ :=
  freshAvg Finset.univ fun t : FLeaf => if κ' = κ ∨ CoverF t Xs then 1 else 0

theorem nearFactor_self (κ : FTree) (Xs : Multiset FLeaf) : nearFactor κ κ Xs = 1 := by
  unfold nearFactor
  simp only [true_or, if_true]
  exact freshAvg_const _ Finset.univ_nonempty 1

theorem nearFactor_of_ne {κ κ' : FTree} (h : κ' ≠ κ) (Xs : Multiset FLeaf) : nearFactor κ κ' Xs = φF Xs := by
  unfold nearFactor φF
  congr 1
  funext t
  by_cases hc : CoverF t Xs
  · rw [if_pos (Or.inr hc), if_pos hc]
  · rw [if_neg (fun h' => h'.elim h hc), if_neg hc]

/-- **The near value of a multiset of disclosed marks at one index.** -/
noncomputable def yN (Ms : Multiset (FTree → FLeaf)) : ℝ≥0∞ :=
  ∑ κ, ∏ κ', nearFactor κ κ' (Ms.map fun m => m κ')

theorem avgN_sum_fin {U : Type} [Fintype U] [Nonempty U] {β : Type} [DecidableEq β] (s : Finset β)
    (φ : β → Multiset U → ℝ≥0∞) (n : ℕ) (X : Multiset U) :
    avgN (fun Y => ∑ b ∈ s, φ b Y) n X = ∑ b ∈ s, avgN (φ b) n X := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact avgN_const 0 n X
  | insert b s hb ih =>
      have h1 : (fun Y => ∑ b' ∈ insert b s, φ b' Y) = fun Y => φ b Y + ∑ b' ∈ s, φ b' Y :=
        funext fun Y => Finset.sum_insert hb
      rw [h1, avgN_add, ih, Finset.sum_insert hb]

/-- **`E[near | n] = Σ_κ Ψ1(n)^(k-1)`.** -/
theorem avgN_yN (n : ℕ) :
    avgN yN n 0 = ∑ _κ : FTree, ENNReal.ofReal (Ψ1R n) ^ (forsTrees - 1) := by
  unfold yN
  rw [avgN_sum_fin]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [avgN_prod_coords (nearFactor κ) n 0]
  simp only [Multiset.map_zero]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ κ)]
  have h1 : avgN (nearFactor κ κ) n 0 = 1 := by
    rw [show nearFactor κ κ = fun _ => 1 from funext (nearFactor_self κ)]
    exact avgN_const 1 n 0
  have h2 : ∀ κ' ∈ Finset.univ.erase κ, avgN (nearFactor κ κ') n 0 = ENNReal.ofReal (Ψ1R n) := by
    intro κ' hκ'
    rw [show nearFactor κ κ' = φF from funext (nearFactor_of_ne (Finset.ne_of_mem_erase hκ'))]
    exact avgN_φF n
  rw [h1, one_mul, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, card_ftree]

theorem nearFactor_le_one (κ κ' : FTree) (Xs : Multiset FLeaf) : nearFactor κ κ' Xs ≤ 1 := by
  classical
  unfold nearFactor
  calc freshAvg Finset.univ (fun t : FLeaf => if κ' = κ ∨ CoverF t Xs then (1 : ℝ≥0∞) else 0)
      ≤ freshAvg Finset.univ (fun _ : FLeaf => (1 : ℝ≥0∞)) :=
        freshAvg_mono _ fun t _ => by split_ifs <;> simp
    _ = 1 := by rw [freshAvg_const _ Finset.univ_nonempty]

theorem yN_le (Ms : Multiset (FTree → FLeaf)) : yN Ms ≤ forsTrees := by
  unfold yN
  calc ∑ κ, ∏ κ', nearFactor κ κ' (Ms.map fun m => m κ') ≤ ∑ _κ : FTree, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun κ _ => Finset.prod_le_one' fun κ' _ => nearFactor_le_one κ κ' _
    _ = forsTrees := by
        simp only [Finset.sum_const, Finset.card_univ, card_ftree, nsmul_eq_mul, mul_one]

end FORS.Security.H0
