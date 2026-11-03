import FORS.CoverBound.IndexFactor
import FORS.Scheme

/-! **One FORS tree.** A target leaf of a tree is covered by a multiset `X` of disclosed leaves of
the same tree (at the same index) when it is one of them. The cover indicator is
`1 - Π_{x ∈ X} [x ≠ t]`, a product over the disclosed leaves, so its average over `n` independent
uniform leaves is a power of the one-leaf miss probability. -/

open ENNReal

namespace FORS.Security.H0

variable [Params]

open Concrete

set_option linter.unusedSectionVars false

/-! ### Real averages -/

section Real

variable {α : Type} [Fintype α]

/-- The average of a real function over a finite type. -/
noncomputable def avgR (g : α → ℝ) : ℝ := (Fintype.card α : ℝ)⁻¹ * ∑ x, g x

/-- The average of `φ` over `n` independent uniform elements added to `X`. -/
noncomputable def avgNR (φ : Multiset α → ℝ) : ℕ → Multiset α → ℝ
  | 0, X => φ X
  | n + 1, X => avgR fun x : α => avgNR φ n (X + {x})

theorem avgR_add (g h : α → ℝ) : avgR (fun x => g x + h x) = avgR g + avgR h := by
  simp only [avgR, Finset.sum_add_distrib, mul_add]

theorem avgR_const_mul (c : ℝ) (g : α → ℝ) : avgR (fun x => c * g x) = c * avgR g := by
  simp only [avgR, ← Finset.mul_sum]
  ring

theorem avgR_sum {β : Type} (s : Finset β) (g : β → α → ℝ) :
    avgR (fun x => ∑ b ∈ s, g b x) = ∑ b ∈ s, avgR (g b) := by
  simp only [avgR, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem avgNR_sum {β : Type} (s : Finset β) (φ : β → Multiset α → ℝ) :
    ∀ n X, avgNR (fun Y => ∑ b ∈ s, φ b Y) n X = ∑ b ∈ s, avgNR (φ b) n X
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgNR, avgNR_sum s φ n]
      exact avgR_sum s _

theorem avgNR_const_mul (c : ℝ) (φ : Multiset α → ℝ) :
    ∀ n X, avgNR (fun Y => c * φ Y) n X = c * avgNR φ n X
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgNR, avgNR_const_mul c φ n]
      exact avgR_const_mul c _

/-- The average of a product over the elements is a power of the one-element average. -/
theorem avgNR_prod_map (g : α → ℝ) : ∀ n X,
    avgNR (fun Y => (Y.map g).prod) n X = (X.map g).prod * (avgR g) ^ n
  | 0, X => by simp [avgNR]
  | n + 1, X => by
      simp only [avgNR, avgNR_prod_map g n, Multiset.map_add, Multiset.map_singleton, Multiset.prod_add,
        Multiset.prod_singleton]
      rw [show (fun x => (X.map g).prod * g x * avgR g ^ n) = fun x => ((X.map g).prod * avgR g ^ n) * g x from
        funext fun x => by ring, avgR_const_mul, pow_succ]
      ring

theorem avgR_prod_pi {κ β : Type} [Fintype κ] [DecidableEq κ] [Fintype β] (G : κ → β → ℝ) :
    avgR (fun x : κ → β => ∏ c, G c (x c)) = ∏ c, avgR (G c) := by
  unfold avgR
  rw [Finset.prod_mul_distrib, Fintype.prod_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Nat.cast_pow, inv_pow]

theorem avgR_prod_type {β γ : Type} [Fintype β] [Fintype γ] (g : β × γ → ℝ) :
    avgR g = avgR fun b : β => avgR fun c : γ => g (b, c) := by
  unfold avgR
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type, mul_assoc, Finset.mul_sum]

theorem avgR_equiv {β : Type} [Fintype β] (e : α ≃ β) (g : α → ℝ) :
    avgR g = avgR fun b : β => g (e.symm b) := by
  unfold avgR
  rw [Fintype.card_congr e, Equiv.sum_comp e.symm g]

theorem avgR_const [Nonempty α] (c : ℝ) : avgR (fun _ : α => c) = c := by
  unfold avgR
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

theorem avgNR_add (φ ψ : Multiset α → ℝ) :
    ∀ n X, avgNR (fun Y => φ Y + ψ Y) n X = avgNR φ n X + avgNR ψ n X
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgNR, avgNR_add φ ψ n]
      exact avgR_add _ _

theorem avgNR_const [Nonempty α] (c : ℝ) : ∀ n X, avgNR (fun _ : Multiset α => c) n X = c
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgNR, avgNR_const c n]
      exact avgR_const c

/-- Averages over the elements commute with an average over another finite type. -/
theorem avgNR_avgR {β : Type} [Fintype β] (f : β → Multiset α → ℝ) (n : ℕ) (X : Multiset α) :
    avgNR (fun Y => avgR fun b => f b Y) n X = avgR fun b => avgNR (f b) n X := by
  unfold avgR
  rw [avgNR_const_mul, avgNR_sum]

end Real


/-! ### One tree -/

/-- The cover indicator of a target leaf by the disclosed leaves `X`. -/
noncomputable def coverR (t : FLeaf) (X : Multiset FLeaf) : ℝ := if t ∈ X then 1 else 0

/-- One disclosed leaf misses the target. -/
noncomputable def missR (t x : FLeaf) : ℝ := if x = t then 0 else 1

theorem coverR_nonneg (t : FLeaf) (X : Multiset FLeaf) : 0 ≤ coverR t X := by
  unfold coverR; split_ifs <;> norm_num

theorem coverR_le_one (t : FLeaf) (X : Multiset FLeaf) : coverR t X ≤ 1 := by
  unfold coverR; split_ifs <;> norm_num

/-- **The cover indicator as a product over the disclosed leaves.** -/
theorem coverR_eq (t : FLeaf) (X : Multiset FLeaf) : coverR t X = 1 - (X.map (missR t)).prod := by
  induction X using Multiset.induction_on with
  | empty => simp [coverR]
  | cons x X ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      by_cases hx : x = t
      · subst hx
        simp [coverR, missR]
      · rw [show missR t x = 1 from if_neg hx, one_mul, ← ih]
        unfold coverR
        by_cases h : t ∈ X
        · rw [if_pos h, if_pos (Multiset.mem_cons_of_mem h)]
        · rw [if_neg h, if_neg (fun h' => (Multiset.mem_cons.1 h').elim (fun e => hx e.symm) h)]

/-- The number of leaves of a tree, as a real number. -/
noncomputable def leavesR : ℝ := 2 ^ forsHeight

theorem leavesR_pos : 0 < leavesR := by unfold leavesR; positivity

theorem card_fleaf : (Fintype.card FLeaf : ℝ) = leavesR := by
  rw [Fintype.card_fin, leavesR]; push_cast; rfl

theorem sum_ind (t : FLeaf) : ∑ x : FLeaf, (if x = t then (1 : ℝ) else 0) = 1 := by
  rw [Finset.sum_ite_eq' Finset.univ t, if_pos (Finset.mem_univ t)]

/-- A uniform leaf misses a given leaf with probability `1 - 1/A`. -/
theorem avgR_missR (t : FLeaf) : avgR (missR t) = 1 - 1 / leavesR := by
  unfold avgR
  have h : ∀ x, missR t x = 1 - if x = t then 1 else 0 := fun x => by unfold missR; split_ifs <;> norm_num
  simp only [h, Finset.sum_sub_distrib, sum_ind, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    card_fleaf]
  have := leavesR_pos
  field_simp

/-- A uniform leaf misses two distinct leaves with probability `1 - 2/A`. -/
theorem avgR_missR_mul (t t' : FLeaf) :
    avgR (fun x => missR t x * missR t' x) = if t' = t then 1 - 1 / leavesR else 1 - 2 / leavesR := by
  by_cases htt : t' = t
  · subst htt
    rw [if_pos rfl, ← avgR_missR t']
    congr 1
    funext x
    unfold missR; split_ifs <;> norm_num
  · rw [if_neg htt]
    unfold avgR
    have h : ∀ x, missR t x * missR t' x = 1 - (if x = t then 1 else 0) - if x = t' then 1 else 0 := by
      intro x
      unfold missR
      by_cases h1 : x = t
      · subst h1; simp [Ne.symm htt]
      · by_cases h2 : x = t' <;> simp [h1, h2, htt]
    simp only [h, Finset.sum_sub_distrib, sum_ind, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_fleaf]
    have := leavesR_pos
    field_simp
    ring

end FORS.Security.H0
