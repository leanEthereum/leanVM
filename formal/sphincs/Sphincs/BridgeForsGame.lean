import Sphincs.BridgeForsPotential

/-! The rest of the game of an arbitrary adaptive adversary as a cost program (`advProg`): every
adversary step is a draw, an ordinary hash query or a signing call, and verification is a lifted
hash computation (`finishGame`). -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner SphincsFors.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Program

variable (parameter : PublicParameter) (data : PublicData)

/-- Verification of the forgery, with the log so far. -/
noncomputable def finishGame (L : QueryLog SigningSpec) (forgery : Forgery) : OracleComp CostSpec HiddenBridge.Outcome := do
  let verified ← liftM (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) forgery.message forgery.signature :
    OracleComp HashSpec Bool)
  return (forgery, L, verified)

/-- The rest of the game from an adversary computation and a log prefix. -/
noncomputable def advProg (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec) :
    OracleComp CostSpec HiddenBridge.Outcome :=
  (simulateQ (costInteraction parameter data) M).run >>= fun r => finishGame parameter data (L ++ r.2) r.1

theorem costRestX_eq (adversary : Adversary) :
    HiddenBridge.costRestX parameter data adversary =
      advProg parameter data (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold HiddenBridge.costRestX advProg finishGame
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem advProg_pure (forgery : Forgery) (L : QueryLog SigningSpec) :
    advProg parameter data (pure forgery) L = finishGame parameter data L forgery := by
  unfold advProg
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advProg_draw (draw : ℕ) (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next) L =
      liftM (CostSpec.query (.inl (.inl draw))) >>= fun v => advProg parameter data (next v) L := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpec.query (.inl (.inl draw))) :
      OracleComp CostSpec _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProg_hash (bytes : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inr bytes))) >>= next) L =
      liftM (CostSpec.query (.inl (.inr (.inl bytes)))) >>= fun v => advProg parameter data (next v) L := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) :
      OracleComp CostSpec _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProg_sign (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) L =
      signCostSource parameter data message >>= fun r => advProg parameter data (next r) (L ++ [⟨message, r⟩]) := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => GraphView.signCostSource parameter data message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

end Program

end Sphincs.Security.ForsPotential
