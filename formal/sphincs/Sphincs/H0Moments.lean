import Sphincs.H0Mark

/-! **Per-tree cover moments by inclusion-exclusion.** A tree's mark is a tree leaf and, per
subtree, a WOTS key and a codeword. A target mark is covered by a multiset `X` of disclosed marks
when every chain it needs is opened deep enough by a disclosed mark with the same tree leaf and the
same WOTS key. Writing the cover indicator as `Π (1 - a Π_x (1 - κ_x))` and expanding by
inclusion-exclusion turns the average over `n` independent uniform marks into a signed sum of `n`-th
powers of one-mark avoidance probabilities `Q`, which decode into the codeword-level quantities. -/

open ENNReal

namespace Sphincs.Security.H0

open Concrete

set_option linter.unusedSectionVars false
attribute [local irreducible] lut codewordCodes

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

end Real

/-! ### Inclusion-exclusion -/

/-- `Π (1 - a b) = Σ_T (-1)^|T| Π_T a Π_T b` over all subsets. -/
theorem prod_one_sub_mul {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℝ) :
    ∏ i, (1 - a i * b i) = ∑ T : Finset ι, (-1) ^ T.card * (∏ i ∈ T, a i) * ∏ i ∈ T, b i := by
  have h := Finset.prod_add (fun i => -(a i * b i)) (fun _ => (1 : ℝ)) Finset.univ
  simp only [Finset.prod_const_one, mul_one, Finset.powerset_univ] at h
  rw [show (∏ i, (1 - a i * b i)) = ∏ i, (-(a i * b i) + 1) from
    Finset.prod_congr rfl fun i _ => by ring, h]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg, Finset.prod_mul_distrib]
  ring

/-! ### Marks as tuples -/

/-- A mark: the tree leaf and, per subtree, the WOTS key and the codeword index. -/
abbrev MT := SuperIdx × (SubIdx → ChildIdx × LutIdx)

def toMT (m : CoordMark) : MT := (m.super, fun j => (m.child j, m.word j))

def ofMT (x : MT) : CoordMark := ⟨x.1, fun j => (x.2 j).1, fun j => (x.2 j).2⟩

/-- Fields are uniform tuples. -/
def fieldMT : FieldVal ≃ MT where
  toFun v := toMT (markEquiv v)
  invFun x := markEquiv.symm (ofMT x)
  left_inv v := by
    simp only [toMT, ofMT]
    rw [show (⟨(markEquiv v).super, fun j => (markEquiv v).child j, fun j => (markEquiv v).word j⟩ : CoordMark) =
      markEquiv v from rfl, Equiv.symm_apply_apply]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, toMT, ofMT]

/-- The deficit of chain `i` of subtree `j`. -/
def need (x : MT) (j : SubIdx) (i : FChain) : ℕ := (lut (x.2 j).2 i).val

/-- `x` opens chain `i` of the WOTS key that `t` needs in subtree `j`, deep enough. -/
def KC (x t : MT) (j : SubIdx) (i : FChain) : Prop :=
  x.1 = t.1 ∧ (x.2 j).1 = (t.2 j).1 ∧ need t j i ≤ need x j i

instance (x t : MT) (j : SubIdx) (i : FChain) : Decidable (KC x t j i) := by unfold KC; infer_instance

/-- Every chain the target needs is opened deep enough. -/
def CoverT (t : MT) (X : Multiset MT) : Prop := ∀ j i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i

/-- The cover indicator as a real number. -/
noncomputable def coverR (t : MT) (X : Multiset MT) : ℝ := by
  classical
  exact if CoverT t X then 1 else 0

/-! ### The expansion of the cover indicator -/

/-- The sign of a choice of chains per subtree. -/
def sgnS (S : SubIdx → Finset FChain) : ℝ := ∏ j, (-1) ^ (S j).card

/-- The chosen chains are all needed. -/
noncomputable def needA (t : MT) (S : SubIdx → Finset FChain) : ℝ :=
  ∏ j, ∏ i ∈ S j, if need t j i = 0 then 0 else 1

/-- A mark avoids every chosen chain. -/
noncomputable def avoidB (t : MT) (S : SubIdx → Finset FChain) (x : MT) : ℝ := by
  classical
  exact ∏ j, ∏ i ∈ S j, (1 - if KC x t j i then 1 else 0)

theorem coverR_eq_prod (t : MT) (X : Multiset MT) :
    coverR t X = ∏ j, ∏ i, (1 - (if need t j i = 0 then 0 else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) := by
  classical
  have hpt : ∀ j i, (1 - (if need t j i = 0 then (0 : ℝ) else 1) *
      (X.map fun x => (1 - if KC x t j i then (1 : ℝ) else 0)).prod) =
      if need t j i = 0 ∨ ∃ x ∈ X, KC x t j i then 1 else 0 := by
    intro j i
    by_cases h0 : need t j i = 0
    · rw [if_pos h0, zero_mul, sub_zero, if_pos (Or.inl h0)]
    · rw [if_neg h0, one_mul]
      by_cases hx : ∃ x ∈ X, KC x t j i
      · obtain ⟨x, hx, hk⟩ := hx
        rw [if_pos (Or.inr ⟨x, hx, hk⟩), Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨x, hx, by simp [hk]⟩),
          sub_zero]
      · push Not at hx
        rw [if_neg (by rintro (h | ⟨x, hx', hk⟩); exact h0 h; exact hx x hx' hk)]
        rw [Multiset.prod_eq_one (fun y hy => by
          obtain ⟨x, hx', rfl⟩ := Multiset.mem_map.1 hy
          simp [hx x hx'])]
        ring
  simp only [hpt]
  unfold coverR CoverT
  by_cases hc : ∀ j i, need t j i = 0 ∨ ∃ x ∈ X, KC x t j i
  · rw [if_pos hc]
    symm
    refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun i _ => ?_
    rw [if_pos (hc j i)]
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨j, i, hji⟩ := hc
    symm
    refine Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    rw [if_neg]
    rintro (h | ⟨x, hx, hk⟩)
    · exact hji.1 h
    · exact hji.2 x hx hk

theorem multiset_prod_finset_prod {β γ : Type} (X : Multiset β) (s : Finset γ) (g : γ → β → ℝ) :
    (X.map fun x => ∏ i ∈ s, g i x).prod = ∏ i ∈ s, (X.map (g i)).prod := by
  induction X using Multiset.induction_on with
  | empty => simp
  | cons x X ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, ih, Finset.prod_mul_distrib]

/-- **Inclusion-exclusion of the cover indicator.** -/
theorem coverR_expand (t : MT) (X : Multiset MT) :
    coverR t X = ∑ S : SubIdx → Finset FChain, sgnS S * needA t S * (X.map (avoidB t S)).prod := by
  classical
  rw [coverR_eq_prod]
  simp only [prod_one_sub_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  unfold sgnS needA avoidB
  rw [multiset_prod_finset_prod]
  simp only [multiset_prod_finset_prod, Finset.prod_mul_distrib]

end Sphincs.Security.H0
