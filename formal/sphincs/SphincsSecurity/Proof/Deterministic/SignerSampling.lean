import SphincsSecurity.Proof.Deterministic.TrialSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] Concrete.ftsOpen Concrete.signLayer Concrete.treeRoot tableDigestLoop Concrete.signDigestLoop

def signatureAfterTrial (secretKey : SphincsSecurity.SecretKey) (attempt : TrialResult) : OracleComp HashSpec (Option Signature) :=
  match attempt with
  | none => pure none
  | some (randomness, index, leaves) => do
      let ftsPath ← Concrete.ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index)
      match ← Concrete.sequenceLayers (fun lay => Concrete.signLayer secretKey index lay) with
      | none => return none
      | some parts => do
          let _ ← Concrete.treeRoot secretKey.parameter topLayer Concrete.rootTree (secretKey.otsSecret topLayer Concrete.rootTree)
          return some
            { randomness := randomness
              ftsSecret := fun tree => secretKey.ftsSecret index tree (leaves (Concrete.ftsIndexOf tree))
              ftsPath := ftsPath
              counter := fun lay => (parts lay).1
              chainValue := fun lay => (parts lay).2.1
              authPath := Concrete.flattenPaths fun lay => (parts lay).2.2 }

theorem tableSign_eq_finish (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey) (message : Message) :
    (tableSign randomizers secretKey message : OracleComp HashSpec (Option Signature)) =
      (tableDigestLoop randomizers secretKey message digestAttemptLimit 0 >>= signatureAfterTrial secretKey) := by
  unfold tableSign
  rfl

theorem sign_eq_finish (secretKey : SphincsSecurity.SecretKey) (message : Message) :
    Concrete.sign secretKey message = (Concrete.signDigestLoop digestAttemptLimit secretKey message >>= fun attempt =>
      (liftM (signatureAfterTrial secretKey attempt) : OracleComp OracleWorld (Option Signature))) := by
  unfold Concrete.sign
  apply bind_congr
  intro attempt
  cases attempt with
  | none => rfl
  | some attempt =>
      rcases attempt with ⟨randomness, index, leaves⟩
      simp only [signatureAfterTrial, liftM_bind]
      apply bind_congr
      intro path
      apply bind_congr
      intro layers
      cases layers <;> simp only [liftM_bind, liftM_pure]

attribute [local irreducible] signatureAfterTrial

theorem evalDist_tableSign (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (state : State) :
    𝒟[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableSign (fun position => tape position.2)
        secretKey message : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature))).run state] =
      𝒟[(simulateQ (worldHandler hash) (Concrete.sign secretKey message)).run state] := by
  simp_rw [tableSign_eq_finish, sign_eq_finish, liftM_bind, simulateQ_bind, StateT.run_bind]
  have h := evalDist_tableDigestLoop hash secretKey message digestAttemptLimit 0 (by decide) state
  have heq := congrArg (fun distribution => distribution >>= fun result : TrialResult × State =>
    𝒟[(simulateQ (worldHandler hash) (liftM (signatureAfterTrial secretKey result.1) :
      OracleComp OracleWorld (Option Signature))).run result.2]) h
  simpa only [evalDist_bind, bind_assoc] using heq

end SphincsSecurity.Seeded
