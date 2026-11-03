import Mathlib
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbComp

/-! Potentials of independent virtual disclosures. A potential is a function of the multiset of
disclosed views that is monotone and has increasing differences (supermodular). Independent coins,
each disclosing a multiset with some probability, raise it by at least each coin's probability
times its gain; the gain of one more view grows with the base; and averages over a finite set of
fresh views are linear and monotone. -/

open ENNReal OracleComp

namespace FORS.Base.Domination

variable {V : Type}

/-- Monotone in the disclosed multiset. -/
def Monotone' (f : Multiset V → ℝ≥0∞) : Prop := ∀ small large, small ≤ large → f small ≤ f large

/-- Expected potential after independent coins: `(p, S)` adds `S` with probability `p`. -/
noncomputable def slotValue (f : Multiset V → ℝ≥0∞) : Multiset V → List (ℝ≥0∞ × Multiset V) → ℝ≥0∞
  | current, [] => f current
  | current, (p, extra) :: rest =>
      p * slotValue f (current + extra) rest + (1 - p) * slotValue f current rest

theorem slotValue_ne_top (f : Multiset V → ℝ≥0∞) (hfin : ∀ m, f m ≠ ⊤) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) (current : Multiset V), (∀ c ∈ coins, c.1 ≤ 1) →
      slotValue f current coins ≠ ⊤
  | [], current, _ => hfin current
  | (p, extra) :: rest, current, hp => by
      have hp1 : p ≤ 1 := hp _ (List.mem_cons_self ..)
      have hrest : ∀ c ∈ rest, c.1 ≤ 1 := fun c hc => hp c (List.mem_cons_of_mem _ hc)
      have h1 := slotValue_ne_top f hfin rest (current + extra) hrest
      have h2 := slotValue_ne_top f hfin rest current hrest
      simp only [slotValue]
      refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ?_ h1, ENNReal.mul_ne_top ?_ h2⟩
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top hp1
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

theorem list_sum_ne_top (values : List ℝ≥0∞) (h : ∀ v ∈ values, v ≠ ⊤) : values.sum ≠ ⊤ := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      rw [List.sum_cons]
      exact ENNReal.add_ne_top.2 ⟨h _ (List.mem_cons_self ..), ih fun v hv => h v (List.mem_cons_of_mem _ hv)⟩

/-! ### Averages over fresh views -/

section Slot

variable (U : Finset V)

/-- The average over a finite set of fresh views. -/
noncomputable def freshAvg (g : V → ℝ≥0∞) : ℝ≥0∞ := (U.card : ℝ≥0∞)⁻¹ * ∑ u ∈ U, g u

theorem freshAvg_const (hU : U.Nonempty) (c : ℝ≥0∞) : freshAvg U (fun _ => c) = c := by
  rw [freshAvg, Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hU.card_pos.ne') (ENNReal.natCast_ne_top _), one_mul]

theorem freshAvg_add (g h : V → ℝ≥0∞) : freshAvg U (fun u => g u + h u) = freshAvg U g + freshAvg U h := by
  simp only [freshAvg, Finset.sum_add_distrib, mul_add]

theorem freshAvg_mono {g h : V → ℝ≥0∞} (hle : ∀ u ∈ U, g u ≤ h u) : freshAvg U g ≤ freshAvg U h := by
  unfold freshAvg
  gcongr with u hu
  exact hle u hu

theorem freshAvg_mul (c : ℝ≥0∞) (g : V → ℝ≥0∞) : freshAvg U (fun u => c * g u) = c * freshAvg U g := by
  simp only [freshAvg, ← Finset.mul_sum]
  ring

end Slot

end FORS.Base.Domination
