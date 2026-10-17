import XmssSecurity.Proof.FirstLaneEagerBound
import XmssSecurity.Proof.FirstLaneHazardEnforcement
import XmssSecurity.Proof.MarginalCoupling
import XmssSecurity.Proof.CacheAgreement
import VCVio.ProgramLogic.Relational.FromUnary

open OracleComp OracleSpec
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity

set_option maxHeartbeats 2000000

theorem relTriple_enforcedHit_append
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest) (limit : Nat)
    (history fragment : FirstLaneOracleSimulation.ActionTrace Index)
    (hhit : FirstLaneOracleSimulation.CombinedHit table
      (FirstLaneOracleSimulation.enforceHazardTrace limit
        (history ++ fragment)))
    (left : ProbComp α)
    (right : ProbComp
      (β × FirstLaneOracleSimulation.ActionTrace Index)) :
    RelTriple left
      (Prod.map id (fun suffix => fragment ++ suffix) <$> right)
      (fun _ result => FirstLaneOracleSimulation.CombinedHit table
        (FirstLaneOracleSimulation.enforceHazardTrace limit
          (history ++ result.2))) := by
  have hmapped : RelTriple
      (id <$> left)
      (Prod.map id (fun suffix => fragment ++ suffix) <$> right)
      (fun _ result => FirstLaneOracleSimulation.CombinedHit table
        (FirstLaneOracleSimulation.enforceHazardTrace limit
          (history ++ result.2))) := by
    apply relTriple_map
    apply relTriple_post_mono
      (relTriple_prod (fun _ _ => True.intro) (fun _ _ => True.intro))
    intro _ result _hresults
    simpa [Prod.map, List.append_assoc] using
      FirstLaneOracleSimulation.CombinedHit.enforce_append_of_prefix
        table limit (history ++ fragment) result.2 hhit
  simpa only [id_map] using hmapped

theorem relTriple_simulateQ_bind_bounded_firstLane
    {spec : OracleSpec ι}
    [Fintype Index] [DecidableEq Index]
    (table : Index → Digest)
    (leftImpl : QueryImpl spec (StateT σ₁ ProbComp))
    (rightImpl : QueryImpl spec
      (StateT σ₂ (OracleComp (FirstLaneOracleSimulation.World Index))))
    (leftFinish : α → σ₁ → ProbComp (β × σ₁))
    (rightFinish : α → σ₂ →
      OracleComp (FirstLaneOracleSimulation.World Index) (β × σ₂))
    (cost : spec.Domain → Nat)
    (stateRel : σ₁ → σ₂ →
      FirstLaneOracleSimulation.ActionTrace Index → Prop)
    (accounted : σ₁ → Nat → Prop)
    (Budget : OracleComp spec α → Nat → σ₁ → Prop)
    (stepBudget : ∀ (input : spec.Domain)
      (next : spec.Range input → OracleComp spec α) (fuel : Nat)
      (leftState : σ₁) (result : spec.Range input × σ₁),
      Budget (liftM (spec.query input) >>= next) fuel leftState →
      result ∈ support ((leftImpl input).run leftState) →
      cost input ≤ fuel ∧ Budget (next result.1) (fuel - cost input) result.2)
    (stepCoupling : ∀ (used : Nat) (input : spec.Domain)
      (leftState : σ₁) (rightState : σ₂)
      (trace : FirstLaneOracleSimulation.ActionTrace Index),
      stateRel leftState rightState trace →
      FirstLaneOracleSimulation.hazardCount trace ≤ used →
      accounted leftState used →
      RelTriple ((leftImpl input).run leftState)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          ((rightImpl input).run rightState)).run)
        (fun leftResult rightResult =>
          (leftResult.1 = rightResult.1.1 ∧
            stateRel leftResult.2 rightResult.1.2
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input ∧
            accounted leftResult.2 (used + cost input)) ∨
          (FirstLaneOracleSimulation.CombinedHit table
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ used + cost input)))
    (countLimit hitLimit : Nat)
    (terminalCoupling : ∀ (value : α) (used fuel : Nat)
      (leftState : σ₁) (rightState : σ₂)
      (trace : FirstLaneOracleSimulation.ActionTrace Index),
      Budget (pure value) fuel leftState →
      stateRel leftState rightState trace →
      FirstLaneOracleSimulation.hazardCount trace ≤ used →
      accounted leftState used →
      used + fuel ≤ countLimit →
      RelTriple (leftFinish value leftState)
        ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
          (rightFinish value rightState)).run)
        (fun leftResult rightResult =>
          (leftResult.1 = rightResult.1.1 ∧
            stateRel leftResult.2 rightResult.1.2
              (trace ++ rightResult.2) ∧
            FirstLaneOracleSimulation.hazardCount
                (trace ++ rightResult.2) ≤ countLimit) ∨
          FirstLaneOracleSimulation.CombinedHit table
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ rightResult.2))))
    (used fuel : Nat)
    (computation : OracleComp spec α)
    (leftState : σ₁) (rightState : σ₂)
    (hbudget : Budget computation fuel leftState)
    (trace : FirstLaneOracleSimulation.ActionTrace Index)
    (hstate : stateRel leftState rightState trace)
    (hcount : FirstLaneOracleSimulation.hazardCount trace ≤ used)
    (haccounted : accounted leftState used)
    (htotal : used + fuel ≤ countLimit)
    (hlimits : countLimit ≤ hitLimit) :
    RelTriple
      ((simulateQ leftImpl computation).run leftState >>= fun result =>
        leftFinish result.1 result.2)
      ((simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table) (do
        let result ← (simulateQ rightImpl computation).run rightState
        rightFinish result.1 result.2)).run)
      (fun leftResult rightResult =>
        (leftResult.1 = rightResult.1.1 ∧
          stateRel leftResult.2 rightResult.1.2
            (trace ++ rightResult.2) ∧
          FirstLaneOracleSimulation.hazardCount
              (trace ++ rightResult.2) ≤ countLimit) ∨
        FirstLaneOracleSimulation.CombinedHit table
          (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
            (trace ++ rightResult.2))) := by
  induction computation using OracleComp.inductionOn generalizing leftState
      rightState trace used fuel with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact terminalCoupling value used fuel leftState rightState trace hbudget
        hstate hcount haccounted htotal
  | query_bind input next ih =>
      simp only [StateT.run_bind, simulateQ_bind, WriterT.run_bind',
        simulateQ_spec_query, bind_assoc]
      apply relTriple_bind (relTriple_with_support
        (stepCoupling used input leftState rightState trace hstate hcount
          haccounted))
      intro headLeft headRight hhead
      have hnextBudget := stepBudget input next fuel leftState headLeft hbudget
        hhead.2.1
      rcases hhead.1 with hgood | hhit
      · obtain ⟨hvalue, hnextState, hnextCount, hnextAccounted⟩ := hgood
        have hnextBudget' : Budget (next headRight.1.1)
            (fuel - cost input) headLeft.2 := by
          rw [← hvalue]
          exact hnextBudget.2
        let appendTrace := fun result :
            ((β × σ₂) × FirstLaneOracleSimulation.ActionTrace Index) =>
          Prod.map id (fun tail => headRight.2 ++ tail) result
        have hrec := ih headRight.1.1 (used + cost input)
          (fuel - cost input) headLeft.2 headRight.1.2 hnextBudget'
            (trace ++ headRight.2) hnextState hnextCount hnextAccounted
              (by omega)
        rw [simulateQ_bind, WriterT.run_bind'] at hrec
        change RelTriple _ _ _ at hrec
        have hlifted : RelTriple
            (id <$> ((simulateQ leftImpl (next headRight.1.1)).run headLeft.2 >>=
              fun result => leftFinish result.1 result.2))
            (appendTrace <$>
              (do
                let handled ←
                  (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                    ((simulateQ rightImpl
                      (next headRight.1.1)).run headRight.1.2)).run
                Prod.map id (fun tail => handled.2 ++ tail) <$>
                  (simulateQ
                    (FirstLaneOracleSimulation.eagerTraceImpl table)
                    (rightFinish handled.1.1 handled.1.2)).run))
            (fun leftResult rightResult =>
              (leftResult.1 = rightResult.1.1 ∧
                stateRel leftResult.2 rightResult.1.2
                  (trace ++ rightResult.2) ∧
                FirstLaneOracleSimulation.hazardCount
                    (trace ++ rightResult.2) ≤ countLimit) ∨
              FirstLaneOracleSimulation.CombinedHit table
                (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
                  (trace ++ rightResult.2))) := by
          apply relTriple_map
          apply relTriple_post_mono hrec
          intro leftResult rightResult hresult
          simpa [appendTrace, Prod.map, List.append_assoc] using hresult
        rw [hvalue]
        change RelTriple _ (appendTrace <$> _) _
        simpa only [id_map] using hlifted
      · obtain ⟨hhit, hnextCount⟩ := hhit
        have hnextLimit : FirstLaneOracleSimulation.hazardCount
            (trace ++ headRight.2) ≤ hitLimit := hnextCount.trans (by omega)
        have henforced : FirstLaneOracleSimulation.CombinedHit table
            (FirstLaneOracleSimulation.enforceHazardTrace hitLimit
              (trace ++ headRight.2)) := by
          rw [FirstLaneOracleSimulation.enforceHazardTrace_eq_self_of_count_le
            (trace ++ headRight.2) hitLimit hnextLimit]
          exact hhit
        apply relTriple_post_mono
          (relTriple_enforcedHit_append table hitLimit trace headRight.2
            henforced
            ((simulateQ leftImpl (next headLeft.1)).run headLeft.2 >>=
              fun result => leftFinish result.1 result.2)
            (do
              let handled ←
                (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                  ((simulateQ rightImpl
                    (next headRight.1.1)).run headRight.1.2)).run
              Prod.map id (fun tail => handled.2 ++ tail) <$>
                (simulateQ (FirstLaneOracleSimulation.eagerTraceImpl table)
                  (rightFinish handled.1.1 handled.1.2)).run))
        intro _leftResult _rightResult hresult
        exact Or.inr (by simpa [List.append_assoc] using hresult)

end XmssSecurity
