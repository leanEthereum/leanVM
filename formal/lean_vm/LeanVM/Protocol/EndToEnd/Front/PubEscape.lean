/-
  LeanVM.Protocol.EndToEnd.Front.PubEscape

  The probability that one uniform challenge escapes the doom of a front phase, in the form the
  calculus of verifier programs states it: an average over `E`, bounded by a worst-case
  round-by-round error of an ArkLib phase and a union bound over the candidates.
-/

module

public import LeanVM.Protocol.Compile.Prog
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Escape averages of front phases

The calculus of verifier programs (`LeanVM.Protocol.Compile.Spec`) states the probability of an
event over one challenge as an average, `|E|⁻¹ · Σ_c [p c]` (`avgE`, `indE`). A front phase's
security on ArkLib's typed framework states it as `Pr{let c ← $ᵗ E}[p c] ≤ ε` for one statement
and one stack, at every verifier prefix (`IsLocallyBounded`). The front phases' doom
quantifies over the candidates of the level-0 commitment, a finite set of stacks, so a challenge
escapes it when it escapes for one candidate:

* `avgE_indE_le_of_prEvent`: the probability bounds the average;
* `avgE_indE_exists_le`: the union bound, `L₀` times the per-candidate bound for at most `L₀`
  candidates;
* `avgE_le_one`, `avgE_indE_le_one`: an average of probabilities is one.
-/

namespace LeanVM.Protocol.EndToEnd.Front

open LeanVM.Parameters OracleComp
open scoped ENNReal NNReal

@[expose] public section

/-- Stacks of a given height are finitely many: the candidates of a commitment are a finite set. -/
instance instFiniteColumn (n : ℕ) : Finite (Column n) :=
  Finite.of_injective (fun c : Column n ↦ c.values) fun a b h ↦ by
    cases a
    cases b
    simp_all

/-- Stacks of a given height are finitely many. -/
theorem finite_column (n : ℕ) : Finite (Column n) := instFiniteColumn n

/-- The indicator of a proposition, `1` if it holds and `0` otherwise. -/
noncomputable def indE (p : Prop) : ℝ≥0∞ := by classical exact if p then 1 else 0

/-- The average of a function over one uniform challenge, as the calculus writes it. -/
noncomputable def avgE (f : E → ℝ≥0∞) : ℝ≥0∞ := (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ c : E, f c

/-- An indicator is at most one. -/
theorem indE_le_one (p : Prop) : indE p ≤ 1 := by
  unfold indE
  split_ifs <;> simp

/-- The indicator of a false proposition is zero. -/
theorem indE_of_not {p : Prop} (h : ¬ p) : indE p = 0 := by
  simp [indE, h]

/-- The indicator of a true proposition is one. -/
theorem indE_of {p : Prop} (h : p) : indE p = 1 := by
  simp [indE, h]

/-- The indicator grows with the proposition. -/
theorem indE_mono {p q : Prop} (h : p → q) : indE p ≤ indE q := by
  by_cases hp : p
  · rw [indE_of hp, indE_of (h hp)]
  · rw [indE_of_not hp]
    exact zero_le

private theorem card_E_ne_zero : (Fintype.card E : ℝ≥0∞) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/-- An average of values at most `c` is at most `c`. -/
theorem avgE_le_of_le {f : E → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ x, f x ≤ c) : avgE f ≤ c := by
  unfold avgE
  calc (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ x : E, f x
      ≤ (Fintype.card E : ℝ≥0∞)⁻¹ * ∑ _x : E, c := by gcongr with x; exact h x
    _ = c := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel card_E_ne_zero (ENNReal.natCast_ne_top _), one_mul]

/-- An average of values at most one is at most one. -/
theorem avgE_le_one {f : E → ℝ≥0∞} (h : ∀ x, f x ≤ 1) : avgE f ≤ 1 := avgE_le_of_le h

/-- An average of indicators is at most one. -/
theorem avgE_indE_le_one (p : E → Prop) : avgE (fun x ↦ indE (p x)) ≤ 1 :=
  avgE_le_one fun x ↦ indE_le_one (p x)

/-- The average grows with the function. -/
theorem avgE_mono {f g : E → ℝ≥0∞} (h : ∀ x, f x ≤ g x) : avgE f ≤ avgE g := by
  unfold avgE
  gcongr with x
  exact h x

/-- The average of the indicator of an event is its uniform probability. -/
theorem avgE_indE_eq_prEvent (p : E → Prop) :
    avgE (fun x ↦ indE (p x)) = Pr{let c ← $ᵗ E}[p c] := by
  classical
  rw [SampleableType.prEvent_uniformSample, avgE, div_eq_mul_inv, mul_comm]
  congr 1
  unfold indE
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A bound on the uniform probability of an event bounds the average of its indicator. -/
theorem avgE_indE_le_of_prEvent {p : E → Prop} {ε : ℝ≥0∞}
    (h : Pr{let c ← $ᵗ E}[p c] ≤ ε) : avgE (fun x ↦ indE (p x)) ≤ ε := by
  rw [avgE_indE_eq_prEvent]
  exact h

/-- The average is additive over a finite sum. -/
private theorem avgE_finset_sum {β : Type} (s : Finset β) (f : β → E → ℝ≥0∞) :
    avgE (fun x ↦ ∑ b ∈ s, f b x) = ∑ b ∈ s, avgE (f b) := by
  unfold avgE
  rw [Finset.sum_comm, Finset.mul_sum]

/-- **The union bound over candidates.** If each of at most `L₀` candidates satisfies an event
with average at most `ε`, some candidate satisfies it with average at most `L₀ · ε`. -/
theorem avgE_indE_exists_le {β : Type} {C : Set β} (hfin : C.Finite) {L₀ : ℕ}
    (hcard : C.ncard ≤ L₀) {P : β → E → Prop} {ε : ℝ≥0∞}
    (h : ∀ q ∈ C, avgE (fun x ↦ indE (P q x)) ≤ ε) :
    avgE (fun x ↦ indE (∃ q ∈ C, P q x)) ≤ L₀ * ε := by
  classical
  let s := hfin.toFinset
  have hpt : ∀ x, indE (∃ q ∈ C, P q x) ≤ ∑ q ∈ s, indE (P q x) := fun x ↦ by
    by_cases hx : ∃ q ∈ C, P q x
    · obtain ⟨q, hq, hP⟩ := hx
      rw [indE_of ⟨q, hq, hP⟩]
      calc (1 : ℝ≥0∞) = indE (P q x) := (indE_of hP).symm
        _ ≤ ∑ q ∈ s, indE (P q x) :=
          Finset.single_le_sum (f := fun q ↦ indE (P q x)) (fun _ _ ↦ zero_le)
            (hfin.mem_toFinset.mpr hq)
    · rw [indE_of_not hx]
      exact zero_le
  calc avgE (fun x ↦ indE (∃ q ∈ C, P q x))
      ≤ avgE (fun x ↦ ∑ q ∈ s, indE (P q x)) := avgE_mono hpt
    _ = ∑ q ∈ s, avgE (fun x ↦ indE (P q x)) := avgE_finset_sum s _
    _ ≤ ∑ _q ∈ s, ε := Finset.sum_le_sum fun q hq ↦ h q (hfin.mem_toFinset.mp hq)
    _ = s.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ L₀ * ε := by
      gcongr
      rw [← Set.ncard_eq_toFinset_card C hfin]
      exact_mod_cast hcard

end
end LeanVM.Protocol.EndToEnd.Front
