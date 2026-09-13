import XmssSecurity.Proof.Deterministic.TableSigner
import XmssSecurity.Proof.Seeded.Presampling

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

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

noncomputable def deterministicGameAfterSecrets (adversary : Adversary) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  gameRest scheme adversary ⟨result.1, parameter⟩ ⟨seed, sk⟩

noncomputable def tableGameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : ChainSecrets) (randomizers : RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  gameRest (tableScheme randomizers) adversary ⟨result.1, parameter⟩ sk

theorem gameCore_deterministic_eq (adversary : Adversary) :
    gameCore scheme adversary = (do
      let seed ← liftM sampleMasterSeed
      let (parameter, secret) ← liftM (deriveParametersAndSecrets seed)
      deterministicGameAfterSecrets adversary seed parameter secret) := by
  simp only [gameCore, scheme, keygen, keygenFromSeed, deterministicGameAfterSecrets, gameRest,
    deriveParametersAndSecrets, deriveChainSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

theorem erases_deterministicGameRest (known : QueryCache HashSpec) (seed : MasterSeed)
    (pk : PublicKey) (sk : XmssSecurity.SecretKey) (randomizers : RandomizerOutputs)
    (hrandomizers : ∀ position, known (randomizerInputs sk.parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known)
      (gameRest scheme adversary pk ⟨seed, sk⟩)
      (gameRest (tableScheme randomizers) adversary pk sk) := by
  unfold gameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (erases_sign known seed sk randomizers
        hrandomizers request.epoch request.message).lift_hash.map _

theorem erases_deterministicGameAfterSecrets (known : QueryCache HashSpec) (seed : MasterSeed)
    (parameter : PublicParameter) (secret : ChainSecrets) (randomizers : RandomizerOutputs)
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known) (deterministicGameAfterSecrets adversary seed parameter secret)
      (tableGameAfterSecrets adversary parameter secret randomizers) := by
  unfold deterministicGameAfterSecrets tableGameAfterSecrets
  apply (Erases.refl (worldKnown known) _).bind
  intro result
  exact erases_deterministicGameRest known seed ⟨result.1, parameter⟩
    (Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)) randomizers hrandomizers adversary

attribute [local irreducible] deterministicGameAfterSecrets tableGameAfterSecrets signingDerivationCache

theorem evalDist_deterministicGameAfterSecrets_prepared (adversary : Adversary) (seed : MasterSeed)
    (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    𝒟[(simulateQ romImpl (deterministicGameAfterSecrets adversary seed (truncateHash parameterOutput)
        (outputSecrets outputs))).run' (derivationCache seed parameterOutput outputs)] =
      𝒟[do
        let randomizers ← sampleRandomizerOutputs
        (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash parameterOutput)
            (outputSecrets outputs) randomizers)).run'
          (signingDerivationCache seed parameterOutput outputs randomizers)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs)]
  rw [show simulateQ romImpl (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs) =
      simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareRandomizers, ← evalDist_bind, bind_map_left]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  exact congrArg _ ((erases_deterministicGameAfterSecrets _ seed _ _ randomizers
    (signingDerivationCache_randomizer seed parameterOutput outputs randomizers) adversary).evalDist_run _ le_rfl)

noncomputable def programmedDeterministicGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ ChainOutputs
  let randomizers ← sampleRandomizerOutputs
  (simulateQ romImpl (tableGameAfterSecrets adversary (truncateHash parameterOutput)
      (outputSecrets outputs) randomizers)).run'
    (signingDerivationCache seed parameterOutput outputs randomizers)

theorem evalDist_gameCore_deterministic_programmed (adversary : Adversary) :
    𝒟[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒟[programmedDeterministicGame adversary] := by
  rw [gameCore_deterministic_eq, run'_lift_sample_bind]
  unfold programmedDeterministicGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  rw [run'_lift_hash_bind, evalDist_bind, evalDist_deriveParametersAndSecrets, ← evalDist_bind]
  simp only [bind_assoc, pure_bind]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro outputs
  exact evalDist_deterministicGameAfterSecrets_prepared adversary seed parameterOutput outputs

end XmssSecurity.Seeded
