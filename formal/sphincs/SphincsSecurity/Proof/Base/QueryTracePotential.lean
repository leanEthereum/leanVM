import SphincsSecurity.Proof.Base.QueryTraceInvariant
import SphincsSecurity.Proof.Residual.RetainedObservation
namespace SphincsSecurity.QueryPause

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable {Index Trace Result State : Type} {spec : OracleSpec Index} [Monoid Trace]
  (observation : (input : spec.Domain) → spec.Range input → Trace) (impl : QueryImpl spec (StateT State SPMF))

theorem traced_spmf_query_bind (input : spec.Domain) (next : spec.Range input → OracleComp spec Result) (state : State) :
    (simulateQ impl (traced observation (liftM (spec.query input) >>= next))).run state =
      ((impl input).run state >>= fun middle =>
        (fun result => ((result.1.1, observation input middle.1 * result.1.2), result.2)) <$>
          (simulateQ impl (traced observation (next middle.1))).run middle.2) := by
  simp only [traced_query_bind, simulateQ_bind, simulateQ_map, simulateQ_spec_query, StateT.run_bind, StateT.run_map]

theorem traced_spmf_history_potential_le (invariant : Trace → State → Prop)
    (hpreserve : ∀ history state, invariant history state → ∀ input result,
      (impl input).run state result ≠ 0 → invariant (history * observation input result.1) result.2)
    (hmass : ∀ (computation : OracleComp spec Result) history state, invariant history state →
      Pr[⊥ | (simulateQ impl (traced observation computation)).run state] = 0)
    (potential : Trace → State → ENNReal) (rate : ENNReal) (cost : Trace → Trace → Nat) (charge : Trace → spec.Domain → Nat)
    (hzero : ∀ history, cost history 1 = 0)
    (hcost : ∀ history input answer tail, cost history (observation input answer * tail) =
      charge history input + cost (history * observation input answer) tail)
    (hstep : ∀ history state, invariant history state → ∀ input,
      (∑' result, Pr[= result | (impl input).run state] * potential (history * observation input result.1) result.2) ≤
        potential history state + rate * (charge history input : ENNReal))
    (computation : OracleComp spec Result) (history : Trace) (state : State) (hi : invariant history state) :
    (∑' result, Pr[= result | (simulateQ impl (traced observation computation)).run state] *
      potential (history * result.1.2) result.2) ≤ potential history state + rate *
        ∑' result, Pr[= result | (simulateQ impl (traced observation computation)).run state] * (cost history result.1.2 : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing history state with
  | pure value =>
      simp only [traced_pure, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul,
        mul_one, hzero, Nat.cast_zero, mul_zero, add_zero, le_refl]
  | query_bind input next ih =>
      simp only [traced_spmf_query_bind, tsum_probOutput_bind_mul, tsum_probOutput_map_mul, ← mul_assoc, hcost, Nat.cast_add]
      have hconstant : (∑' middle, Pr[= middle | (impl input).run state] *
          ∑' result, Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] *
            ((charge history input : ENNReal) + (cost (history * observation input middle.1) result.1.2 : ENNReal))) =
          (charge history input : ENNReal) * (∑' middle, Pr[= middle | (impl input).run state]) +
            ∑' middle, Pr[= middle | (impl input).run state] *
              ∑' result, Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] * (cost (history * observation input middle.1) result.1.2 : ENNReal) := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        apply tsum_congr
        intro middle
        by_cases hm : (impl input).run state middle = 0
        · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, mul_zero, zero_add]
        · have hi' := hpreserve history state hi input middle hm
          rw [show (∑' result, Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] *
              ((charge history input : ENNReal) + (cost (history * observation input middle.1) result.1.2 : ENNReal))) =
              (charge history input : ENNReal) + ∑' result,
                Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] * (cost (history * observation input middle.1) result.1.2 : ENNReal) by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
              tsum_probOutput_eq_one' (hmass (next middle.1) _ _ hi'), one_mul]]
          rw [mul_add, mul_comm _ (charge history input : ENNReal)]
      calc
        _ ≤ ∑' middle, Pr[= middle | (impl input).run state] *
            (potential (history * observation input middle.1) middle.2 + rate *
              ∑' result, Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] * (cost (history * observation input middle.1) result.1.2 : ENNReal)) := by
          apply ENNReal.tsum_le_tsum
          intro middle
          by_cases hm : (impl input).run state middle = 0
          · simp only [SPMF.probOutput_eq_apply, hm, zero_mul, le_refl]
          · exact mul_le_mul' le_rfl (ih middle.1 _ _ (hpreserve history state hi input middle hm))
        _ = (∑' middle, Pr[= middle | (impl input).run state] *
            potential (history * observation input middle.1) middle.2) + rate *
            ∑' middle, Pr[= middle | (impl input).run state] *
              ∑' result, Pr[= result | (simulateQ impl (traced observation (next middle.1))).run middle.2] * (cost (history * observation input middle.1) result.1.2 : ENNReal) := by
          simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ rate, ENNReal.tsum_mul_left]
        _ ≤ _ := by
          have hqueryMass : (∑' middle, Pr[= middle | (impl input).run state]) = 1 := by
            have hfull : (∑' result, Pr[= result |
                (simulateQ impl (traced observation (liftM (spec.query input) >>= next))).run state] * (1 : ENNReal)) = 1 := by
              simpa only [mul_one] using tsum_probOutput_eq_one' (hmass (liftM (spec.query input) >>= next) history state hi)
            rw [traced_spmf_query_bind, tsum_probOutput_bind_mul] at hfull
            simp only [mul_one] at hfull
            exact le_antisymm tsum_probOutput_le_one (by
              rw [← hfull]
              apply ENNReal.tsum_le_tsum
              intro middle
              exact mul_le_of_le_one_right zero_le tsum_probOutput_le_one)
          rw [hconstant, hqueryMass, mul_one, mul_add, ← add_assoc]
          exact add_le_add (hstep history state hi input) le_rfl

theorem traced_spmf_potential_le (invariant : Trace → State → Prop)
    (hpreserve : ∀ history state, invariant history state → ∀ input result,
      (impl input).run state result ≠ 0 → invariant (history * observation input result.1) result.2)
    (hmass : ∀ (computation : OracleComp spec Result) history state, invariant history state →
      Pr[⊥ | (simulateQ impl (traced observation computation)).run state] = 0)
    (potential : Trace → State → ENNReal) (rate : ENNReal) (cost : Trace → Nat) (charge : spec.Domain → Nat)
    (hzero : cost 1 = 0) (hcost : ∀ input answer tail, cost (observation input answer * tail) = charge input + cost tail)
    (hstep : ∀ history state, invariant history state → ∀ input,
      (∑' result, Pr[= result | (impl input).run state] * potential (history * observation input result.1) result.2) ≤
        potential history state + rate * (charge input : ENNReal))
    (computation : OracleComp spec Result) (history : Trace) (state : State) (hi : invariant history state) :
    (∑' result, Pr[= result | (simulateQ impl (traced observation computation)).run state] *
      potential (history * result.1.2) result.2) ≤ potential history state + rate *
        ∑' result, Pr[= result | (simulateQ impl (traced observation computation)).run state] * (cost result.1.2 : ENNReal) := by
  exact traced_spmf_history_potential_le observation impl invariant hpreserve hmass potential rate
    (fun _ => cost) (fun _ => charge) (fun _ => hzero) (fun _ => hcost) hstep computation history state hi

end SphincsSecurity.QueryPause
