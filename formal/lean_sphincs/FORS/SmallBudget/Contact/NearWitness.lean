import FORS.CoverPotential.GenericWitness
import FORS.CoverBound.NearMoment

/-! **The near witness.** A target is near covered at tree `κ` when the leaf it selects in every
other tree is disclosed by a disclosed view at its index; the witness counts the trees at which the
target is near covered. It is monotone and finite, at least one on a target covered at every tree
but one, and its fresh-digest price is a sum over the indices of `κ E` times the near value `yN` of
the index's marks. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner FORS.Base.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable


/-- Every tree of the target but `κ` is covered. -/
def NearSub (target : View) (κ : FTree) (D : Multiset View) : Prop :=
  ∀ κ', κ' ≠ κ → TreeCovered target κ' D

/-- **The near witness.** -/
noncomputable def witnessNear (target : View) (D : Multiset View) : ℝ≥0∞ :=
  ∑ κ, if NearSub target κ D then 1 else 0

theorem nearSub_mono {target : View} {κ : FTree} {small large : Multiset View} (hle : small ≤ large)
    (h : NearSub target κ small) : NearSub target κ large :=
  fun κ' hκ => treeCovered_mono hle (h κ' hκ)

theorem witnessNear_le (target : View) (D : Multiset View) : witnessNear target D ≤ forsTrees := by
  unfold witnessNear
  calc ∑ κ, (if NearSub target κ D then (1 : ℝ≥0∞) else 0) ≤ ∑ _κ : FTree, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun κ _ => by split_ifs <;> simp
    _ = forsTrees := by simp

theorem witnessNear_props : WitnessProps witnessNear := by
  intro v
  refine ⟨fun small large hle => ?_, fun D => ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (witnessNear_le v D)⟩
  unfold witnessNear
  refine Finset.sum_le_sum fun κ _ => ?_
  by_cases h : NearSub v κ small
  · rw [if_pos h, if_pos (nearSub_mono hle h)]
  · rw [if_neg h]; exact zero_le

/-- A tree covered by the reveals is covered by disclosed views accounting for the reveals. -/
theorem treeCovered_of_treeCov {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (κ : FTree) (hcov : TreeCov (HiddenBridge.revealedSet R) (fullDigestView digest) κ) :
    TreeCovered (Lifetime.localDigestView digest) κ d := by
  unfold TreeCov at hcov
  simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hcov
  obtain ⟨v, hv, h1, h2⟩ := hD _ _ _ _ hcov
  exact ⟨v, hv, by rw [localDigestView_fst]; exact h1, by rw [localDigestView_snd]; exact h2⟩

/-- **A near-covered digest has a positive near witness.** -/
theorem nearWitness_pos {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (κ : FTree) (hnear : ∀ κ', κ' ≠ κ → TreeCov (HiddenBridge.revealedSet R) (fullDigestView digest) κ') :
    1 ≤ witnessNear (Lifetime.localDigestView digest) d := by
  have hsub : NearSub (Lifetime.localDigestView digest) κ d :=
    fun κ' hκ => treeCovered_of_treeCov hD digest κ' (hnear κ' hκ)
  unfold witnessNear
  refine le_trans ?_ (Finset.single_le_sum (f := fun κ => if NearSub (Lifetime.localDigestView digest) κ d
    then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ κ))
  rw [if_pos hsub]

end FORS.Security.ForsPotential

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.Domination H0Avg ForsPotential


theorem freshAvg_sum' {V β : Type} (U : Finset V) (s : Finset β) (g : β → V → ℝ≥0∞) :
    freshAvg U (fun u => ∑ b ∈ s, g b u) = ∑ b ∈ s, freshAvg U (g b) := by
  unfold freshAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem nearSub_iff (l : Fin (2 ^ subtreeHeight)) (τ : FTree → FLeaf) (κ : FTree) (d : Multiset View) :
    NearSub (l, τ) κ d ↔ ∀ κ', κ' = κ ∨ CoverF (τ κ') ((marksAt l d).map fun m => m κ') := by
  unfold NearSub TreeCovered CoverF
  simp only [mem_marks_map]
  constructor
  · intro h κ'
    by_cases hκ : κ' = κ
    · exact Or.inl hκ
    · exact Or.inr (h κ' hκ)
  · intro h κ' hκ
    rcases h κ' with h0 | h1
    · exact absurd h0 hκ
    · exact h1

/-- **The near price is a sum over the indices.** -/
theorem priceNear_decomp (d : Multiset View) :
    priceW witnessNear d = ∑ l : Fin (2 ^ subtreeHeight), κE * yN (marksAt l d) := by
  classical
  unfold priceW
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (FTree → FLeaf)))
    from rfl, freshAvg_prod]
  have hw : ∀ (l : Fin (2 ^ subtreeHeight)) (τ : FTree → FLeaf), witnessNear (l, τ) d =
      ∑ κ, ∏ κ', (fun κ' (t : FLeaf) => if κ' = κ ∨ CoverF t ((marksAt l d).map fun m => m κ')
        then (1 : ℝ≥0∞) else 0) κ' (τ κ') := by
    intro l τ
    unfold witnessNear
    refine Finset.sum_congr rfl fun κ _ => ?_
    by_cases h : NearSub (l, τ) κ d
    · rw [if_pos h]
      exact (Finset.prod_eq_one fun κ' _ => if_pos ((nearSub_iff l τ κ d).1 h κ')).symm
    · rw [if_neg h]
      rw [nearSub_iff] at h
      push Not at h
      obtain ⟨κ', hκ'⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ κ') (if_neg (by
        rintro (h1 | h1)
        · exact hκ'.1 h1
        · exact hκ'.2 h1))).symm
  simp only [hw]
  have hy : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg Finset.univ fun τ : FTree → FLeaf =>
      ∑ κ, ∏ κ', (fun κ' (t : FLeaf) => if κ' = κ ∨ CoverF t ((marksAt l d).map fun m => m κ')
        then (1 : ℝ≥0∞) else 0) κ' (τ κ')) = yN (marksAt l d) := by
    intro l
    unfold yN
    rw [freshAvg_sum']
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [freshAvg_pi_prod (fun κ' (t : FLeaf) => if κ' = κ ∨ CoverF t ((marksAt l d).map fun m => m κ')
        then (1 : ℝ≥0∞) else 0)]
    refine Finset.prod_congr rfl fun κ' _ => ?_
    unfold nearFactor
    rfl
  simp only [hy]
  unfold freshAvg κE
  rw [Finset.mul_sum, Finset.mul_sum, Finset.card_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end FORS.Security.H0
