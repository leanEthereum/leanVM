import Sphincs.BridgeForsGeneric
import Sphincs.H0NearMom

/-! **The near witness.** A target is near covered at the free subtree `(c, j')` when every chain
outside that subtree is opened deep enough by disclosed views at its index; the witness counts the
free subtrees, indexing them by the covered subtree `j` of tree `c`. It is monotone and finite, at
least one on a target covered at every chain but one, and its fresh-digest price is a sum over the
indices of `κ E` times the near value `yN` of the index's marks. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open SphincsFors.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- Every chain of the target outside subtree `1 - j` of tree `c` is covered: the other trees, and
subtree `j` of tree `c`. -/
def NearSub (target : View) (c : Coord) (j : SubIdx) (D : Multiset View) : Prop :=
  (∀ c', c' ≠ c → ∀ j' i', ChainCovered target c' j' i' D) ∧ ∀ i', ChainCovered target c j i' D

/-- **The near witness.** -/
noncomputable def witnessNear (target : View) (D : Multiset View) : ℝ≥0∞ :=
  ∑ c, ∑ j, if NearSub target c j D then 1 else 0

theorem nearSub_mono {target : View} {c : Coord} {j : SubIdx} {small large : Multiset View} (hle : small ≤ large)
    (h : NearSub target c j small) : NearSub target c j large :=
  ⟨fun c' hc j' i' => chainCovered_mono hle (h.1 c' hc j' i'), fun i' => chainCovered_mono hle (h.2 i')⟩

theorem witnessNear_le (target : View) (D : Multiset View) : witnessNear target D ≤ 16 := by
  unfold witnessNear
  calc ∑ c, ∑ j, (if NearSub target c j D then (1 : ℝ≥0∞) else 0) ≤ ∑ _c : Coord, ∑ _j : SubIdx, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => by split_ifs <;> simp
    _ = 16 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        rw [show Fintype.card Coord = 8 from H0.card_coord]
        norm_num

theorem witnessNear_props : WitnessProps witnessNear := by
  intro v
  refine ⟨fun small large hle => ?_, fun D => ne_top_of_le_ne_top (by norm_num) (witnessNear_le v D)⟩
  unfold witnessNear
  refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun j _ => ?_
  by_cases h : NearSub v c j small
  · rw [if_pos h, if_pos (nearSub_mono hle h)]
  · rw [if_neg h]; exact zero_le

/-- A chain covered by the reveals is covered by disclosed views accounting for the reveals. -/
theorem chainCovered_of_chainCov {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (c : Coord) (j : SubIdx) (i : FChain)
    (hcov : ChainCov (HiddenBridge.revealedSet R) (fullDigestView digest) c j i) :
    ChainCovered (Lifetime.localDigestView digest) c j i d := by
  rcases hcov with hz | ⟨p, hp, hle⟩
  · exact Or.inl hz
  · simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨v, hv, h1, h2, h3, h4⟩ := hD _ _ _ _ _ _ _ hp
    refine Or.inr ⟨v, hv, by rw [localDigestView_fst]; exact h1, ?_⟩
    refine ⟨by rw [h2]; rfl, by rw [h3]; rfl, ?_⟩
    have hneed : chainNeed (coordField digest c) j i ≤ chainTop := by
      have := (lut ((decodeMark (coordField digest c)).word j) i).isLt
      simp only [chainNeed, chainTop] at this ⊢
      omega
    have hneedv : chainNeed (v.2 c) j i ≤ chainTop := by
      have := (lut ((decodeMark (v.2 c)).word j) i).isLt
      simp only [chainNeed, chainTop] at this ⊢
      omega
    simp only [fullDigestView] at hle
    change chainNeed (coordField digest c) j i ≤ chainNeed (v.2 c) j i
    omega

/-- The other subtree. -/
def otherSub (j : SubIdx) : SubIdx := if j = 0 then 1 else 0

omit [Params] in
theorem otherSub_ne (j : SubIdx) : otherSub j ≠ j := by
  fin_cases j <;> decide

/-- **A near-covered digest has a positive near witness.** -/
theorem nearWitness_pos {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (c : Coord) (j : SubIdx) (i : FChain)
    (hnear : ∀ c' j' i', (c', j', i') ≠ (c, j, i) →
      ChainCov (HiddenBridge.revealedSet R) (fullDigestView digest) c' j' i') :
    1 ≤ witnessNear (Lifetime.localDigestView digest) d := by
  have hsub : NearSub (Lifetime.localDigestView digest) c (otherSub j) d := by
    refine ⟨fun c' hc j' i' => chainCovered_of_chainCov hD digest c' j' i' (hnear c' j' i' ?_),
      fun i' => chainCovered_of_chainCov hD digest c _ i' (hnear c _ i' ?_)⟩
    · intro h
      exact hc (congrArg Prod.fst h)
    · intro h
      exact otherSub_ne j (congrArg (fun x => x.2.1) h)
  unfold witnessNear
  refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ j, if NearSub (Lifetime.localDigestView digest) c j d
    then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ c))
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => if NearSub (Lifetime.localDigestView digest) c j d
    then (1 : ℝ≥0∞) else 0) (fun _ _ => zero_le) (Finset.mem_univ (otherSub j)))
  rw [if_pos hsub]

end Sphincs.Security.ForsPotential

namespace Sphincs.Security.H0

open Concrete ForestPrice SphincsFors.Security.Domination H0Avg ForsPotential

variable [Params]

omit [Params] in
theorem freshAvg_sum' {V β : Type} (U : Finset V) (s : Finset β) (g : β → V → ℝ≥0∞) :
    freshAvg U (fun u => ∑ b ∈ s, g b u) = ∑ b ∈ s, freshAvg U (g b) := by
  unfold freshAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem nearSub_iff (l : Fin (2 ^ subtreeHeight)) (τ : Coord → FieldVal) (c : Coord) (j : SubIdx) (d : Multiset View) :
    NearSub (l, τ) c j d ↔ ∀ c', if c' = c then CoverHF (τ c') j ((marksAt l d).map fun m => m c')
      else CoverF (τ c') ((marksAt l d).map fun m => m c') := by
  unfold NearSub ChainCovered CoverHF CoverF
  simp only [mem_marks_map]
  constructor
  · rintro ⟨h1, h2⟩ c'
    split_ifs with hc
    · subst hc
      intro i
      rcases h2 i with h0 | ⟨v, hv, hl, hk⟩
      · exact Or.inl h0
      · exact Or.inr ⟨v.2 c', ⟨v, hv, hl, rfl⟩, hk⟩
    · intro j' i
      rcases h1 c' hc j' i with h0 | ⟨v, hv, hl, hk⟩
      · exact Or.inl h0
      · exact Or.inr ⟨v.2 c', ⟨v, hv, hl, rfl⟩, hk⟩
  · intro h
    refine ⟨fun c' hc j' i => ?_, fun i => ?_⟩
    · have h' := h c'
      rw [if_neg hc] at h'
      rcases h' j' i with h0 | ⟨_, ⟨v, hv, hl, rfl⟩, hk⟩
      · exact Or.inl h0
      · exact Or.inr ⟨v, hv, hl, hk⟩
    · have h' := h c
      rw [if_pos rfl] at h'
      rcases h' i with h0 | ⟨_, ⟨v, hv, hl, rfl⟩, hk⟩
      · exact Or.inl h0
      · exact Or.inr ⟨v, hv, hl, hk⟩

/-- **The near price is a sum over the indices.** -/
theorem priceNear_decomp (d : Multiset View) :
    priceW witnessNear d = ∑ l : Fin (2 ^ subtreeHeight), κE * yN (marksAt l d) := by
  classical
  unfold priceW
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (Coord → FieldVal)))
    from rfl, freshAvg_prod]
  have hw : ∀ (l : Fin (2 ^ subtreeHeight)) (τ : Coord → FieldVal), witnessNear (l, τ) d =
      ∑ c, ∑ j, ∏ c', (fun c' (t : FieldVal) => if (if c' = c then CoverHF t j ((marksAt l d).map fun m => m c')
        else CoverF t ((marksAt l d).map fun m => m c')) then (1 : ℝ≥0∞) else 0) c' (τ c') := by
    intro l τ
    unfold witnessNear
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : NearSub (l, τ) c j d
    · rw [if_pos h]
      exact (Finset.prod_eq_one fun c' _ => if_pos ((nearSub_iff l τ c j d).1 h c')).symm
    · rw [if_neg h]
      rw [nearSub_iff] at h
      push Not at h
      obtain ⟨c', hc'⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ c') (if_neg hc')).symm
  simp only [hw]
  have hy : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg Finset.univ fun τ : Coord → FieldVal =>
      ∑ c, ∑ j, ∏ c', (fun c' (t : FieldVal) => if (if c' = c then CoverHF t j ((marksAt l d).map fun m => m c')
        else CoverF t ((marksAt l d).map fun m => m c')) then (1 : ℝ≥0∞) else 0) c' (τ c')) =
      yN (marksAt l d) := by
    intro l
    unfold yN
    rw [freshAvg_sum']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [freshAvg_sum']
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [freshAvg_pi_prod (fun c' (t : FieldVal) => if (if c' = c then CoverHF t j ((marksAt l d).map fun m => m c')
        else CoverF t ((marksAt l d).map fun m => m c')) then (1 : ℝ≥0∞) else 0)]
    refine Finset.prod_congr rfl fun c' _ => ?_
    unfold nearFactor
    split_ifs with hc
    · rfl
    · rfl
  simp only [hy]
  unfold freshAvg κE
  rw [Finset.mul_sum, Finset.mul_sum, Finset.card_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end Sphincs.Security.H0
