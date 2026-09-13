import SphincsSecurity.Proof.Deterministic.DerivationTable
import SphincsSecurity.Proof.Seeded.AlgorithmErasure

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def tableDigestLoop (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : Nat → Nat → m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := truncateHash (randomizers (message, BitVec.ofNat 32 trial))
      match ← Concrete.signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => tableDigestLoop randomizers secretKey message attempts (trial + 1)

def tableSign (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : m (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) => do
      let ftsPath ← Concrete.ftsOpen secretKey.parameter index leaves (secretKey.ftsSecret index)
      match ← sequenceLayers (fun lay => Concrete.signLayer secretKey index lay) with
      | none => return none
      | some parts => do
          let _ ← Concrete.treeRoot secretKey.parameter topLayer rootTree (secretKey.otsSecret topLayer rootTree)
          return some
            { randomness := randomness
              ftsSecret := fun tree => secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
              ftsPath := ftsPath
              layers := fun lay => LayerSignature.ofPadded lay (parts lay) }

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme SphincsSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk message => liftM (tableSign randomizers sk message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

theorem erases_deterministicDigestLoop (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) (attempts trial : Nat) :
    Erases known (signDigestLoop ⟨seed, parameter, root⟩ message attempts trial : OracleComp HashSpec _)
      (tableDigestLoop randomizers (tableKey parameter root outputs) message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signDigestLoop tableDigestLoop deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (message, BitVec.ofNat 32 trial))
      change Erases known (Concrete.signAttempt (tableKey parameter root outputs) message
        (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
          (Concrete.signAttempt (tableKey parameter root outputs) message
            (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _

theorem erases_deterministicSign (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) :
    Erases known (sign ⟨seed, parameter, root⟩ message : OracleComp HashSpec _)
      (tableSign randomizers (tableKey parameter root outputs) message) := by
  unfold sign tableSign
  apply (erases_deterministicDigestLoop known parameter seed root outputs randomizers hrandomizers message _ _).bind
  intro attempt
  cases attempt with
  | none => exact .pure _
  | some attempt =>
      rcases attempt with ⟨randomness, index, leaves⟩
      apply (erases_selectedSecrets known parameter seed outputs hsecrets index leaves).bind_known
      apply (erases_ftsOpen known parameter seed outputs hsecrets index leaves).bind
      intro path
      have hlayers := Erases.sequenceLayers known _ _
        (fun lay => erases_signLayer known parameter seed outputs hsecrets root index lay)
      rw [sequenceLayers_map] at hlayers
      apply hlayers.bind_map_right
      intro layers
      cases layers with
      | none => exact .pure _
      | some parts =>
          apply (erases_treeRoot known parameter seed outputs hsecrets topLayer Concrete.rootTree).bind
          intro rootValue
          exact .pure _

end SphincsSecurity.Seeded
