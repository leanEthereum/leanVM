import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Fts.ExactTargetShapeSigning
import SphincsSecurity.Proof.Fts.TargetShapeContinuation
import SphincsSecurity.Proof.Fts.TargetShapeExpectation

/-! ## SigningExecutionBudget -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

/-- Debit from the syntactic continuation bound, including repeatable digest rejection. -/
def signingExecutionHashCost : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => digestAttemptLimit

end SphincsSecurity.Concrete

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

noncomputable def reuseTargetEnvelope (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) : TargetShapeVector :=
  targetShapeEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse
    (((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ * (Fintype.card Index : ENNReal)⁻¹) budget signatures
    (observedTargetShapeVector key payload target state)

theorem reuseTargetEnvelope_budget_mono (key : SecretKey) (reuse : ENNReal) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) {smaller larger : Nat} (hbudget : smaller ≤ larger)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    reuseTargetEnvelope key reuse smaller payload target signatures state groups remaining ≤
      reuseTargetEnvelope key reuse larger payload target signatures state groups remaining :=
  targetShapeEnvelope_queries_mono _ _ _ signatures _ hbudget groups remaining hvalid

theorem expected_randomOracle_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : HashInput) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (randomOracle input).run state.1] *
      reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + 1) payload target signatures state groups remaining := by
  by_cases hfresh : state.1 input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    unfold reuseTargetEnvelope
    rw [targetShapeEnvelope_expected, ← targetShapeEnvelope_query]
    exact targetShapeEnvelope_mono _ _ _ budget signatures
      (fun G R hv => expected_fresh_targetShape_le key payload target state.1 state.2 input hfresh hsigned G R hv)
      groups remaining hvalid
  · obtain ⟨output, ho⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ ho, tsum_probOutput_pure_mul]
    exact reuseTargetEnvelope_budget_mono key reuse payload target signatures state (Nat.le_succ _) groups remaining hvalid

theorem expected_logTraced_world_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState) (input : OracleWorld.Domain) (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inl input)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse (budget + signingExecutionHashCost (.inl input)) payload target signatures state groups remaining := by
  rw [logTracedMappedAdversaryImpl_run_map, tsum_probOutput_map_mul]
  simp only [signingLogFragment, List.append_nil]
  cases input with
  | inr input => exact expected_randomOracle_reuseTarget_le key reuse budget payload target signatures state input hsigned groups remaining hvalid
  | inl sample =>
      have hrun : (unifFwdImpl HashSpec sample).run state.1 =
          (fun output => (output, state.1)) <$> (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) := by
        simpa [simulateQ_query] using (unifFwdImpl.simulateQ_run
          (hashSpec := HashSpec) (liftM (unifSpec.query sample) : ProbComp (unifSpec.Range sample)) state.1)
      change (∑' result, Pr[= result | (unifFwdImpl HashSpec sample).run state.1] *
        reuseTargetEnvelope key reuse budget payload target signatures (result.2, state.2) groups remaining) ≤ _
      rw [hrun, tsum_probOutput_map_mul]
      dsimp only
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem expected_logTraced_sign_reuseTarget_le (key : SecretKey) (reuse : ENNReal) (budget : Nat) (payload : HashInput) (target : FewTimeView)
    (signatures : Nat) (state : CoverLogState)
    (hsigned : SigningDigestsCached key.parameter state.1 key.root state.2) (message : Message)
    (hreuse : exactDigestReuseWeight key message state.1 ≤ reuse)
    (groups : Finset (Finset FtsTree)) (remaining : Finset FtsTree) (hvalid : TargetShapeValid groups remaining) :
    (∑' result, Pr[= result | (logTracedMappedAdversaryImpl key (.inr message)).run state] *
      reuseTargetEnvelope key reuse budget payload target signatures result.2 groups remaining) ≤
      reuseTargetEnvelope key reuse budget payload target (signatures + 1) state groups remaining := by
  unfold reuseTargetEnvelope
  rw [targetShapeEnvelope_expected]
  exact (targetShapeEnvelope_mono _ _ _ budget signatures
    (fun G R hv => expected_logTraced_sign_targetShape_le_of_exactReuse key reuse payload target state hsigned message hreuse G R hv)
      groups remaining hvalid).trans
    (targetShapeEnvelope_signing_le _ _ _ budget signatures _ groups remaining hvalid)

end SphincsSecurity.Concrete
