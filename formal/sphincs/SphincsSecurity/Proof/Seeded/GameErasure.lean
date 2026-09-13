import SphincsSecurity.Proof.Seeded.AlgorithmErasure
import SphincsSecurity.Proof.Scheme.Secrets

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem Erases.simulateQ_writer {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {α : Type} (known : QueryCache target)
    (left right : QueryImpl source (WriterT (QueryLog SigningSpec) (OracleComp target)))
    (h : ∀ input, Erases known (left input).run (right input).run)
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind]
      apply (h input).bind
      intro result
      exact (ih result.1).map _

noncomputable def gameRest {Key : Type} (scheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def gameAfterParameter (adversary : Adversary) (parameter : PublicParameter)
    (seed : MasterSeed) : OracleComp OracleWorld Bool := do
  let root ← liftM (treeRoot parameter topLayer Concrete.rootTree seed : OracleComp HashSpec Digest)
  gameRest scheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩

theorem gameCore_seeded_eq (adversary : Adversary) :
    gameCore scheme adversary = (do
      let seed ← liftM sampleMasterSeed
      let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
      gameAfterParameter adversary parameter seed) := by
  simp only [gameCore, scheme, keygen, gameAfterParameter, gameRest,
    bind_assoc, pure_bind]

section Game

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))

include hknown

theorem erases_gameRest (adversary : Adversary) (root : Digest) :
    Erases (worldKnown known)
      (gameRest scheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩)
      (SphincsSecurity.gameRest Concrete.scheme adversary ⟨root, parameter⟩ (tableKey parameter root outputs)) := by
  unfold gameRest SphincsSecurity.gameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (erases_sign known parameter seed outputs hknown root request).map _

theorem erases_gameAfterParameter (adversary : Adversary) :
    Erases (worldKnown known) (gameAfterParameter adversary parameter seed)
      (Concrete.gameAfterSecrets adversary parameter (tableOts outputs) (tableFts outputs)) := by
  unfold gameAfterParameter Concrete.gameAfterSecrets
  apply (erases_treeRoot known parameter seed outputs hknown topLayer Concrete.rootTree).lift_hash.bind
  intro root
  exact erases_gameRest known parameter seed outputs hknown adversary root

end Game
end SphincsSecurity.Seeded
