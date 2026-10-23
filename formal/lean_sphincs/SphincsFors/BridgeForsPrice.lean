import SphincsFors.BridgeVirtual
import SphincsFors.LifetimeLanding

/-! Count-based FORS prices over multisets of disclosed kept views. The witness count of a target
view is the product over the 24 trees of the number of disclosed views at its index that match
it on that tree; it bounds the coverage indicator and is monotone with increasing differences.
The fresh-digest price averages it over a uniform landed digest. -/

open ENNReal

namespace SphincsFors.Security.ForsPrice

open Concrete Domination

variable [Params]

abbrev View := Lifetime.KeptDigestView

/-- Disclosed views matching a target on one tree. -/
def matchCount (target : View) (tree : FtsTree) (disclosed : Multiset View) : ℕ :=
  (disclosed.filter fun view => view.1 = target.1 ∧ view.2 tree = target.2 tree).card

/-- The witness count of a target. -/
def witness (target : View) (disclosed : Multiset View) : ℕ :=
  ∏ tree, matchCount target tree disclosed

theorem matchCount_add (target : View) (tree : FtsTree) (first second : Multiset View) :
    matchCount target tree (first + second) = matchCount target tree first + matchCount target tree second := by
  simp [matchCount, Multiset.filter_add]

theorem matchCount_mono (target : View) (tree : FtsTree) {small large : Multiset View} (hle : small ≤ large) :
    matchCount target tree small ≤ matchCount target tree large :=
  Multiset.card_le_card (Multiset.filter_le_filter _ hle)

omit [Params] in
/-- Products of affine increasing functions have increasing differences. -/
theorem prod_increasing_differences {κ : Type} [DecidableEq κ] (trees : Finset κ) (small large extra : κ → ℕ)
    (hle : ∀ t, small t ≤ large t) :
    ∏ t ∈ trees, (small t + extra t) + ∏ t ∈ trees, large t ≤
      ∏ t ∈ trees, (large t + extra t) + ∏ t ∈ trees, small t := by
  induction trees using Finset.induction_on with
  | empty => simp
  | insert j trees hj ih =>
      simp only [Finset.prod_insert hj]
      set A := ∏ t ∈ trees, small t
      set A' := ∏ t ∈ trees, large t
      set B := ∏ t ∈ trees, (small t + extra t)
      set B' := ∏ t ∈ trees, (large t + extra t)
      have hBB : B ≤ B' := Finset.prod_le_prod fun t _ => Nat.add_le_add_right (hle t) _
      have hAB : A ≤ B := Finset.prod_le_prod fun t _ => Nat.le_add_right _ _
      have hj' := hle j
      -- (a + s) B + a' A' ≤ (a' + s) B' + a A
      nlinarith [Nat.mul_le_mul_right (extra j) hBB, Nat.mul_le_mul hj' (le_refl (B - A)),
        Nat.sub_add_cancel hAB, Nat.mul_le_mul_left (large j) ih,
        Nat.mul_le_mul_left (small j) hAB, Nat.zero_le (small j), Nat.zero_le A]

theorem witness_mono (target : View) : Monotone' fun disclosed : Multiset View =>
    (witness target disclosed : ℝ≥0∞) := by
  intro small large hle
  have h : witness target small ≤ witness target large :=
    Finset.prod_le_prod fun tree _ => matchCount_mono target tree hle
  show (witness target small : ℝ≥0∞) ≤ (witness target large : ℝ≥0∞)
  exact Nat.cast_le.mpr h

theorem witness_super (target : View) : Supermodular fun disclosed : Multiset View =>
    (witness target disclosed : ℝ≥0∞) := by
  intro small large extra hle
  have h := prod_increasing_differences Finset.univ (fun t => matchCount target t small)
    (fun t => matchCount target t large) (fun t => matchCount target t extra)
    (fun t => matchCount_mono target t hle)
  have h' : witness target (small + extra) + witness target large ≤
      witness target (large + extra) + witness target small := by
    simp only [witness, matchCount_add]
    exact h
  show (witness target (small + extra) : ℝ≥0∞) + (witness target large : ℝ≥0∞) ≤
    (witness target (large + extra) : ℝ≥0∞) + (witness target small : ℝ≥0∞)
  rw [← Nat.cast_add, ← Nat.cast_add]
  exact Nat.cast_le.mpr h'

/-! ### The fresh-digest price and its excess over a baseline -/

omit [Params] in
theorem super_const_mul {V : Type} {g : Multiset V → ℝ≥0∞} (hg : Supermodular g) (c : ℝ≥0∞) :
    Supermodular fun d => c * g d := by
  intro small large extra hle
  simp only [← mul_add]
  exact mul_le_mul_right (hg small large extra hle) c

omit [Params] in
theorem mono_const_mul {V : Type} {g : Multiset V → ℝ≥0∞} (hg : Monotone' g) (c : ℝ≥0∞) :
    Monotone' fun d => c * g d := fun _ _ hle => mul_le_mul_right (hg _ _ hle) c

/-- Probability that a uniform digest lands in the kept subtree. -/
noncomputable def landing : ℝ≥0∞ := ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞)⁻¹

/-- The count price of a fresh digest: landing times the average witness count. -/
noncomputable def price (disclosed : Multiset View) : ℝ≥0∞ :=
  landing * freshAvg Finset.univ fun target => (witness target disclosed : ℝ≥0∞)

theorem price_mono : Monotone' price :=
  mono_const_mul (mono_freshAvg _ fun target => witness_mono target) _

theorem price_super : Supermodular price :=
  super_const_mul (super_freshAvg _ fun target => witness_super target) _

theorem price_ne_top (disclosed : Multiset View) : price disclosed ≠ ⊤ := by
  refine ENNReal.mul_ne_top ?_ (freshAvg_ne_top Finset.univ_nonempty fun _ => ENNReal.natCast_ne_top _)
  simp [landing]

omit [Params] in
theorem real_excess (A A' B B' b : ℝ) (hAA : A ≤ A') (hAB : A ≤ B) (hsuper : B + A' ≤ B' + A) :
    max (B - b) 0 + max (A' - b) 0 ≤ max (B' - b) 0 + max (A - b) 0 := by
  rcases le_total B b with h1 | h1 <;> rcases le_total A' b with h2 | h2 <;>
    rcases le_total A b with h3 | h3 <;> rcases le_total B' b with h4 | h4 <;>
    simp only [max_eq_right (sub_nonpos.2 h1), max_eq_left (sub_nonneg.2 h1),
      max_eq_right (sub_nonpos.2 h2), max_eq_left (sub_nonneg.2 h2),
      max_eq_right (sub_nonpos.2 h3), max_eq_left (sub_nonneg.2 h3),
      max_eq_right (sub_nonpos.2 h4), max_eq_left (sub_nonneg.2 h4)] <;> linarith

omit [Params] in
theorem toReal_tsub (x b : ℝ≥0∞) (hx : x ≠ ⊤) (hb : b ≠ ⊤) : (x - b).toReal = max (x.toReal - b.toReal) 0 := by
  rcases le_total b x with h | h
  · rw [ENNReal.toReal_sub_of_le h hx, max_eq_left]
    exact sub_nonneg.2 (ENNReal.toReal_mono hx h)
  · rw [tsub_eq_zero_of_le h, ENNReal.toReal_zero, max_eq_right]
    exact sub_nonpos.2 (ENNReal.toReal_mono hb h)

omit [Params] in
/-- Excess over a baseline keeps increasing differences. -/
theorem excess_super {V : Type} {g : Multiset V → ℝ≥0∞} (hmono : Monotone' g) (hsuper : Supermodular g)
    (hfin : ∀ d, g d ≠ ⊤) (b : ℝ≥0∞) (hb : b ≠ ⊤) : Supermodular fun d => g d - b := by
  intro small large extra hle
  have hAA := hmono small large hle
  have hAB := hmono small (small + extra) (Multiset.le_add_right _ _)
  have hs := hsuper small large extra hle
  have hsub : ∀ d, g d - b ≠ ⊤ := fun d => ne_top_of_le_ne_top (hfin d) tsub_le_self
  rw [← ENNReal.toReal_le_toReal (hfin _) (hfin _)] at hAA
  rw [← ENNReal.toReal_le_toReal (hfin _) (hfin _)] at hAB
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩)
    (ENNReal.add_ne_top.2 ⟨hfin _, hfin _⟩), ENNReal.toReal_add (hfin _) (hfin _),
    ENNReal.toReal_add (hfin _) (hfin _)] at hs
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨hsub _, hsub _⟩)
    (ENNReal.add_ne_top.2 ⟨hsub _, hsub _⟩), ENNReal.toReal_add (hsub _) (hsub _),
    ENNReal.toReal_add (hsub _) (hsub _),
    toReal_tsub _ _ (hfin _) hb, toReal_tsub _ _ (hfin _) hb, toReal_tsub _ _ (hfin _) hb,
    toReal_tsub _ _ (hfin _) hb]
  exact real_excess _ _ _ _ _ hAA hAB hs

omit [Params] in
theorem excess_mono {V : Type} {g : Multiset V → ℝ≥0∞} (hmono : Monotone' g) (b : ℝ≥0∞) :
    Monotone' fun d => g d - b := fun _ _ hle => tsub_le_tsub_right (hmono _ _ hle) b

end SphincsFors.Security.ForsPrice
