import Mathlib
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbComp

/-! Potentials of independent virtual disclosures. A potential is a function of the multiset of
disclosed views that is monotone and has increasing differences (supermodular). Independent coins,
each disclosing a multiset with some probability, raise it by at least each coin's probability
times its gain; the gain of one more view grows with the base; and averages over a finite set of
fresh views are linear and monotone. -/

open ENNReal OracleComp

namespace SphincsFors.Security.Domination

variable {V : Type}

/-- Monotone in the disclosed multiset. -/
def Monotone' (f : Multiset V → ℝ≥0∞) : Prop := ∀ small large, small ≤ large → f small ≤ f large

/-- Increasing differences, in additive form. -/
def Supermodular (f : Multiset V → ℝ≥0∞) : Prop :=
  ∀ small large extra, small ≤ large → f (small + extra) + f large ≤ f (large + extra) + f small

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

/-- Summed increasing differences over a list of coins. -/
theorem supermodular_sum (f : Multiset V → ℝ≥0∞) (hsuper : Supermodular f) (current extra : Multiset V)
    (coins : List (ℝ≥0∞ × Multiset V)) :
    (coins.map fun c => c.1 * f (current + c.2)).sum + (coins.map (·.1)).sum * f (current + extra) ≤
      (coins.map fun c => c.1 * f (current + extra + c.2)).sum + (coins.map (·.1)).sum * f current := by
  induction coins with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      have hstep : head.1 * f (current + head.2) + head.1 * f (current + extra) ≤
          head.1 * f (current + extra + head.2) + head.1 * f current := by
        rw [← mul_add, ← mul_add]
        exact mul_le_mul_right (hsuper current (current + extra) head.2 (Multiset.le_add_right _ _)) _
      calc head.1 * f (current + head.2) + (tail.map fun c => c.1 * f (current + c.2)).sum +
            (head.1 * f (current + extra) + (tail.map (·.1)).sum * f (current + extra))
          = (head.1 * f (current + head.2) + head.1 * f (current + extra)) +
            ((tail.map fun c => c.1 * f (current + c.2)).sum +
              (tail.map (·.1)).sum * f (current + extra)) := by ring
        _ ≤ (head.1 * f (current + extra + head.2) + head.1 * f current) +
            ((tail.map fun c => c.1 * f (current + extra + c.2)).sum +
              (tail.map (·.1)).sum * f current) := add_le_add hstep ih
        _ = _ := by ring

/-- **Independent coins.** Each coin contributes at least its probability times its gain. -/
theorem slot_lower (f : Multiset V → ℝ≥0∞) (hsuper : Supermodular f) (hfin : ∀ m, f m ≠ ⊤) :
    ∀ (coins : List (ℝ≥0∞ × Multiset V)) (current : Multiset V), (∀ c ∈ coins, c.1 ≤ 1) →
      f current + (coins.map fun c => c.1 * f (current + c.2)).sum ≤
        slotValue f current coins + (coins.map (·.1)).sum * f current
  | [], current, _ => by simp [slotValue]
  | (p, extra) :: rest, current, hp => by
      have hp1 : p ≤ 1 := hp _ (List.mem_cons_self ..)
      have hrest : ∀ c ∈ rest, c.1 ≤ 1 := fun c hc => hp c (List.mem_cons_of_mem _ hc)
      have ih1 := slot_lower f hsuper hfin rest (current + extra) hrest
      have ih2 := slot_lower f hsuper hfin rest current hrest
      have hsum := supermodular_sum f hsuper current extra rest
      simp only [slotValue, List.map_cons, List.sum_cons]
      -- finiteness of everything involved
      have hptop : p ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hp1
      have hP : (rest.map (·.1)).sum ≠ ⊤ := list_sum_ne_top _ (by
        intro v hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
        exact ne_top_of_le_ne_top ENNReal.one_ne_top (hrest c hc))
      have hS1 : (rest.map fun c => c.1 * f (current + extra + c.2)).sum ≠ ⊤ := list_sum_ne_top _ (by
        intro v hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hrest c hc)) (hfin _))
      have hS2 : (rest.map fun c => c.1 * f (current + c.2)).sum ≠ ⊤ := list_sum_ne_top _ (by
        intro v hv
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (hrest c hc)) (hfin _))
      have hsv1 := slotValue_ne_top f hfin rest (current + extra) hrest
      have hsv2 := slotValue_ne_top f hfin rest current hrest
      have ha := hfin current
      have hc := hfin (current + extra)
      -- move to real numbers
      set P := (rest.map (·.1)).sum
      set S1 := (rest.map fun c => c.1 * f (current + extra + c.2)).sum
      set S2 := (rest.map fun c => c.1 * f (current + c.2)).sum
      set sv1 := slotValue f (current + extra) rest
      set sv2 := slotValue f current rest
      have hPc : P * f (current + extra) ≠ ⊤ := ENNReal.mul_ne_top hP hc
      have hPa : P * f current ≠ ⊤ := ENNReal.mul_ne_top hP ha
      have hq1 : (1 - p) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
      rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)] at ih1 ih2 hsum
      rw [ENNReal.toReal_add hc hS1, ENNReal.toReal_add hsv1 hPc, ENNReal.toReal_mul] at ih1
      rw [ENNReal.toReal_add ha hS2, ENNReal.toReal_add hsv2 hPa, ENNReal.toReal_mul] at ih2
      rw [ENNReal.toReal_add hS2 hPc, ENNReal.toReal_add hS1 hPa, ENNReal.toReal_mul,
        ENNReal.toReal_mul] at hsum
      have hpc : p * f (current + extra) ≠ ⊤ := ENNReal.mul_ne_top hptop hc
      have hps1 : p * sv1 ≠ ⊤ := ENNReal.mul_ne_top hptop hsv1
      have hps2 : (1 - p) * sv2 ≠ ⊤ := ENNReal.mul_ne_top hq1 hsv2
      have hpPa : (p + P) * f current ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨hptop, hP⟩) ha
      rw [← ENNReal.toReal_le_toReal (ENNReal.add_ne_top.2 ⟨ha, ENNReal.add_ne_top.2 ⟨hpc, hS2⟩⟩)
          (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hps1, hps2⟩, hpPa⟩),
        ENNReal.toReal_add ha (ENNReal.add_ne_top.2 ⟨hpc, hS2⟩), ENNReal.toReal_add hpc hS2,
        ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨hps1, hps2⟩) hpPa, ENNReal.toReal_add hps1 hps2,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_add hptop hP]
      have hq : (1 - p).toReal = 1 - p.toReal := by
        rw [ENNReal.toReal_sub_of_le hp1 ENNReal.one_ne_top, ENNReal.toReal_one]
      have hpr : p.toReal ≤ 1 := by
        have := ENNReal.toReal_mono ENNReal.one_ne_top hp1
        simpa using this
      rw [hq]
      have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
      have h1 := mul_le_mul_of_nonneg_left ih1 hp0
      have h2 := mul_le_mul_of_nonneg_left ih2 (sub_nonneg.2 hpr)
      have h3 := mul_le_mul_of_nonneg_left hsum hp0
      nlinarith [h1, h2, h3]

/-! ### Gains -/

/-- The gain of disclosing one more view. -/
noncomputable def gain (f : Multiset V → ℝ≥0∞) (base : Multiset V) (view : V) : ℝ≥0∞ :=
  f (base + {view}) - f base

theorem add_gain (f : Multiset V → ℝ≥0∞) (hmono : Monotone' f) (base : Multiset V) (view : V) :
    f (base + {view}) = f base + gain f base view :=
  (add_tsub_cancel_of_le (hmono _ _ (Multiset.le_add_right _ _))).symm

/-- Gains grow with the base. -/
theorem gain_le_of_le (f : Multiset V → ℝ≥0∞) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (small large : Multiset V) (hle : small ≤ large) (view : V) :
    f large + gain f small view ≤ f (large + {view}) := by
  have h := hsuper small large {view} hle
  rw [add_gain f hmono small view] at h
  refine (ENNReal.add_le_add_iff_right (hfin small)).1 ?_
  calc f large + gain f small view + f small = f small + gain f small view + f large := by ring
    _ ≤ f (large + {view}) + f small := h

/-- Coins attached to items. -/
def coinsOf (items : List (ℝ≥0∞ × V)) : List (ℝ≥0∞ × Multiset V) := items.map fun i => (i.1, {i.2})

theorem coins_gain (f : Multiset V → ℝ≥0∞) (hmono : Monotone' f) (hsuper : Supermodular f)
    (hfin : ∀ m, f m ≠ ⊤) (items : List (ℝ≥0∞ × V)) (hw : ∀ i ∈ items, i.1 ≤ 1)
    (small large : Multiset V) (hle : small ≤ large) :
    f large + (items.map fun i => i.1 * gain f small i.2).sum ≤ slotValue f large (coinsOf items) := by
  have hcoins : ∀ c ∈ coinsOf items, c.1 ≤ 1 := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc
    exact hw i hi
  have hslot := slot_lower f hsuper hfin (coinsOf items) large hcoins
  simp only [coinsOf, List.map_map, Function.comp_def] at hslot
  have hW : (items.map fun i => i.1).sum ≠ ⊤ := list_sum_ne_top _ (by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hv
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (hw i hi))
  have hstep : (items.map fun i => i.1 * f large).sum + (items.map fun i => i.1 * gain f small i.2).sum ≤
      (items.map fun i => i.1 * f (large + {i.2})).sum := by
    rw [← List.sum_map_add]
    refine List.sum_le_sum fun i _ => ?_
    rw [← mul_add]
    exact mul_le_mul_right (gain_le_of_le f hmono hsuper hfin small large hle i.2) _
  have hWf : (items.map fun i => i.1 * f large).sum = (items.map fun i => i.1).sum * f large := by
    rw [List.sum_map_mul_right]
  rw [hWf] at hstep
  have hWtop : (items.map fun i => i.1).sum * f large ≠ ⊤ := ENNReal.mul_ne_top hW (hfin _)
  refine (ENNReal.add_le_add_iff_right hWtop).1 ?_
  calc f large + (items.map fun i => i.1 * gain f small i.2).sum + (items.map fun i => i.1).sum * f large
      = f large + ((items.map fun i => i.1).sum * f large +
          (items.map fun i => i.1 * gain f small i.2).sum) := by ring
    _ ≤ f large + (items.map fun i => i.1 * f (large + {i.2})).sum := add_le_add le_rfl hstep
    _ ≤ _ := hslot

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

end SphincsFors.Security.Domination
