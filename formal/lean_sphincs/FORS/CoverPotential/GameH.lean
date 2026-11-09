module

public import FORS.CoverPotential.Game
public import FORS.GraphView.HonestGame

@[expose] public section

/-! The rest of the game over the honest-reading cost interface (`advProgH`): the adversary's
draws and hash queries are charged as before, a signing call runs the honest signer
`signCostSourceH` (its reads honest, no ticks), and verification is a lifted hash computation,
charged (`finishGameH`, raw queries, not `liftM`). The honest analogue of `advProg`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView

set_option backward.isDefEq.respectTransparency false

section Program

variable (parameter : PublicParameter) (data : PublicData)

/-- Verification of the forgery over the honest interface, with the log. Its reads are raw (charged):
`liftM` from `HashSpec` would land on the honest summand, so the hash oracle is simulated by raw
queries explicitly. -/
noncomputable def finishGameH (L : QueryLog SigningSpec) (forgery : Forgery) :
    OracleComp CostSpecH HiddenBridge.Outcome := do
  let verified ← simulateQ (fun q => liftM (CostSpecH.query (.inl (.inr (.inl q)))) :
    QueryImpl HashSpec (OracleComp CostSpecH))
    (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) forgery.message forgery.signature : OracleComp HashSpec Bool)
  return (forgery, L, verified)

/-- The rest of the game from an adversary computation and a log prefix, the signer honest. -/
noncomputable def advProgH (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec) :
    OracleComp CostSpecH HiddenBridge.Outcome :=
  (simulateQ (costInteractionH parameter data) M).run >>= fun r => finishGameH parameter data (L ++ r.2) r.1

/-- The honest-reading game with its outcome: key generation's cost as a tick, then `advProgH`
(the adversary's and the verifier's queries charged, the signer's honest). -/
noncomputable def costGameXH (adversary : Adversary) : OracleComp CostSpecH HiddenBridge.Outcome := do
  HiddenCost.tick (H := HashInput) Prefix.keygenHashCost
  advProgH parameter data (adversary.main ⟨data.root, parameter⟩) []

theorem advProgH_pure (forgery : Forgery) (L : QueryLog SigningSpec) :
    advProgH parameter data (pure forgery) L = finishGameH parameter data L forgery := by
  unfold advProgH
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advProgH_draw (draw : ℕ) (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProgH parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next) L =
      liftM (CostSpecH.query (.inl (.inl draw))) >>= fun v => advProgH parameter data (next v) L := by
  unfold advProgH
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpecH.query (.inl (.inl draw))) :
      OracleComp CostSpecH _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProgH_hash (bytes : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProgH parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inr bytes))) >>= next) L =
      liftM (CostSpecH.query (.inl (.inr (.inl bytes)))) >>= fun v => advProgH parameter data (next v) L := by
  unfold advProgH
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpecH.query (.inl (.inr (.inl bytes)))) :
      OracleComp CostSpecH _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProgH_sign (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProgH parameter data (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) L =
      signCostSourceH parameter data message >>= fun r =>
        advProgH parameter data (next r) (L ++ [⟨message, r⟩]) := by
  unfold advProgH
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpecH)
      (fun message => GraphView.signCostSourceH parameter data message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

end Program

end FORS.Security.ForsPotential
