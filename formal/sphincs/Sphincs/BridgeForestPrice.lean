import SphincsFors.BridgeVirtual
import Sphincs.LifetimeLanding

/-! The forest price over multisets of disclosed kept views. A target view is covered when, in every
tree and both subtrees, each chain of the WOTS key it selects is disclosed at or below the position
it needs by a disclosed view at the same index. The cover indicator is monotone (it is not
supermodular: a second cover adds nothing). The fresh-digest price averages it over a uniform landed
digest. -/

open ENNReal

namespace Sphincs.Security.ForestPrice

open Concrete SphincsFors.Security.Domination

variable [Params]

abbrev View := Lifetime.KeptDigestView

/-- Chain `i` of the WOTS key that the target selects in tree `c`, subtree `j`, needs only the
public top, or some disclosed view at the target's index opens it deep enough. -/
def ChainCovered (target : View) (c : Coord) (j : SubIdx) (i : FChain) (disclosed : Multiset View) : Prop :=
  chainNeed (target.2 c) j i = 0 ∨ ∃ v ∈ disclosed, v.1 = target.1 ∧ KeyCovers (v.2 c) (target.2 c) j i

/-- Every chain the target needs is covered. -/
def CoverAll (target : View) (disclosed : Multiset View) : Prop :=
  ∀ c j i, ChainCovered target c j i disclosed

theorem chainCovered_mono {target : View} {c : Coord} {j : SubIdx} {i : FChain} {small large : Multiset View}
    (hle : small ≤ large) (h : ChainCovered target c j i small) : ChainCovered target c j i large := by
  rcases h with h | ⟨v, hv, h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨v, Multiset.mem_of_le hle hv, h1, h2⟩

open Classical in
/-- **The witness**: the cover indicator of a target. -/
noncomputable def witness (target : View) (disclosed : Multiset View) : ℝ≥0∞ :=
  if CoverAll target disclosed then 1 else 0

theorem witness_le_one (target : View) (disclosed : Multiset View) : witness target disclosed ≤ 1 := by
  unfold witness; split_ifs <;> simp

theorem witness_ne_top (target : View) (disclosed : Multiset View) : witness target disclosed ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (witness_le_one target disclosed)

theorem witness_mono (target : View) : Monotone' (witness target) := by
  intro small large hle
  unfold witness
  by_cases hs : CoverAll target small
  · have hl : CoverAll target large := fun c j i => chainCovered_mono hle (hs c j i)
    rw [if_pos hs, if_pos hl]
  · rw [if_neg hs]; exact zero_le

/-! ### The fresh-digest price and its excess over a baseline -/

omit [Params] in
theorem mono_const_mul {V : Type} {g : Multiset V → ℝ≥0∞} (hg : Monotone' g) (c : ℝ≥0∞) :
    Monotone' fun d => c * g d := fun _ _ hle => mul_le_mul_right (hg _ _ hle) c

omit [Params] in
theorem mono_freshAvg' {V W : Type} (U : Finset W) {h : W → Multiset V → ℝ≥0∞} (hh : ∀ u, Monotone' (h u)) :
    Monotone' fun d => freshAvg U fun u => h u d :=
  fun _ _ hle => freshAvg_mono U fun u _ => hh u _ _ hle

/-- Probability that a uniform digest lands in the kept subtree. -/
noncomputable def landing : ℝ≥0∞ := ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞)⁻¹

theorem landing_le_one : landing ≤ 1 := by
  unfold landing
  exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)

/-- The cover price of a fresh digest: landing times the probability that a uniform view is covered. -/
noncomputable def price (disclosed : Multiset View) : ℝ≥0∞ :=
  landing * freshAvg Finset.univ fun target => witness target disclosed

theorem price_mono : Monotone' price :=
  mono_const_mul (mono_freshAvg' _ fun target => witness_mono target) _

theorem price_le_landing (disclosed : Multiset View) : price disclosed ≤ landing := by
  unfold price
  calc landing * freshAvg Finset.univ (fun target => witness target disclosed)
      ≤ landing * freshAvg Finset.univ (fun _ => (1 : ℝ≥0∞)) :=
        mul_le_mul_right (freshAvg_mono _ fun t _ => witness_le_one t disclosed) _
    _ = landing := by rw [freshAvg_const _ Finset.univ_nonempty, mul_one]

theorem price_ne_top (disclosed : Multiset View) : price disclosed ≠ ⊤ :=
  ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one) (price_le_landing disclosed)

omit [Params] in
theorem excess_mono {V : Type} {g : Multiset V → ℝ≥0∞} (hmono : Monotone' g) (b : ℝ≥0∞) :
    Monotone' fun d => g d - b := fun _ _ hle => tsub_le_tsub_right (hmono _ _ hle) b

end Sphincs.Security.ForestPrice
