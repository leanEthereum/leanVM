import SphincsSecurity.Proof.Chains.AdaptiveChainCheckpoint
namespace SphincsSecurity.Concrete.PartialChainEndpoint

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem scaled_expectation_le {Result : Type} (law : PMF Result) (factor : ENNReal)
    (left right : Result → ENNReal) (h : ∀ result ∈ law.support, factor * left result ≤ right result) :
    factor * (∑' result, law result * left result) ≤ ∑' result, law result * right result := by
  rw [← expectation_scale]
  apply ENNReal.tsum_le_tsum
  intro result
  by_cases hr : result ∈ law.support
  · exact mul_le_mul' le_rfl (h result hr)
  · have hz : law result = 0 := not_not.mp hr
    simp only [hz, zero_mul, le_refl]

variable {State : Type} [Fintype State] [DecidableEq State] [Nonempty State]
  {AuxIndex : Type} {auxSpec : OracleSpec AuxIndex} {n : Nat} {Checkpoint Result : Type}
  (auxiliary : State → QueryImpl auxSpec PMF)
  (before : State → OracleComp (auxSpec + PrefixSpec n State) Checkpoint)
  (after : State → Checkpoint × (Fin n → State → Option State) → OracleComp (auxSpec + PrefixSpec n State) Result)
  (observed : Fin n → State → Option State)
  (marked : State → Checkpoint × (Fin n → State → Option State) → Prop)

theorem realCheckpointRun_mark_probability :
    Pr[fun result => marked result.1 result.2.1 | realCheckpointRun auxiliary before after observed] =
      Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  have h := congrArg (fun law : PMF (State × (Checkpoint × (Fin n → State → Option State))) =>
    Pr[fun result => marked result.1 result.2 | law]) (realCheckpointRun_before auxiliary before after observed)
  simpa only [← PMF.monad_map_eq_map, probEvent_map, Function.comp_def] using h

theorem realCheckpointRun_contact_charge (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      ∑' result, realCheckpointRun auxiliary before after observed result *
        (((queryCount result.2.1.2 + 2 * result.2.2.1.2 : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
  rw [show Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
      realCheckpointRun auxiliary before after observed] =
      (∑' result, realCheckpointRun auxiliary before after observed result *
        if marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 then 1 else 0) by
          simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]]
  rw [realCheckpointRun_density, realCheckpointRun_expectation, ← mul_assoc]
  apply scaled_expectation_le
  intro endpoint _
  apply scaled_expectation_le
  intro middle hmiddle
  by_cases hm : marked endpoint middle
  · simp only [hm, true_and, if_true, mul_one]
    simpa only [mul_assoc] using run_contact_charge_transfer (auxiliary endpoint) (after endpoint middle) middle.2 endpoint
      (hmarked endpoint middle hm) budget (hbudget endpoint middle hmiddle hm)
  · simp only [hm, false_and, if_false, mul_zero, tsum_zero, le_refl]

theorem realCheckpointRun_contact_le_mark (budget : Nat)
    (hmarked : ∀ endpoint middle, marked endpoint middle → ¬Contact middle.2 endpoint)
    (hbudget : ∀ endpoint, ∀ middle ∈ (lazyRun (auxiliary endpoint) (before endpoint) observed).support,
      marked endpoint middle → ∀ result ∈ (lazyRun (auxiliary endpoint)
        (QueryCap.counted IsPrefixQuery (after endpoint middle)) middle.2).support, queryCount result.2 ≤ budget)
    (hcost : ∀ result ∈ (realCheckpointRun auxiliary before after observed).support,
      marked result.1 result.2.1 → queryCount result.2.1.2 + result.2.2.1.2 ≤ budget) :
    (1 - (budget : ENNReal) / Fintype.card State) * ((Fintype.card State : ENNReal) *
      Pr[fun result => marked result.1 result.2.1 ∧ Contact result.2.2.2 result.1 |
        realCheckpointRun auxiliary before after observed]) ≤
      (2 * budget : Nat) * Pr[fun result => marked result.1 result.2 | realRun auxiliary before observed] := by
  apply (realCheckpointRun_contact_charge auxiliary before after observed marked budget hmarked hbudget).trans
  calc
    _ ≤ ∑' result, realCheckpointRun auxiliary before after observed result *
        (((2 * budget : Nat) : ENNReal) * if marked result.1 result.2.1 then 1 else 0) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ (realCheckpointRun auxiliary before after observed).support
      · apply mul_le_mul' le_rfl
        by_cases hm : marked result.1 result.2.1
        · simp only [if_pos hm, mul_one]
          have hc := hcost result hr hm
          exact_mod_cast (show queryCount result.2.1.2 + 2 * result.2.2.1.2 ≤ 2 * budget by omega)
        · simp only [if_neg hm, mul_zero, le_refl]
      · have hz : realCheckpointRun auxiliary before after observed result = 0 := not_not.mp hr
        simp only [hz, zero_mul, le_refl]
    _ = _ := by
      rw [expectation_scale, ← realCheckpointRun_mark_probability auxiliary before after observed marked]
      simp only [probEvent_eq_tsum_ite, PMF.probOutput_eq_apply, mul_ite, mul_one, mul_zero]

end SphincsSecurity.Concrete.PartialChainEndpoint
