import SphincsSecurity.Proof.Deterministic.TableSigner
import SphincsSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable def deterministicGameAfterParameter (adversary : Adversary) (parameter : PublicParameter)
    (seed : MasterSeed) : OracleComp OracleWorld Bool := do
  let root ← liftM (treeRoot parameter topLayer Concrete.rootTree seed : OracleComp HashSpec Digest)
  gameRest scheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩

noncomputable def tableGameAfterParameter (adversary : Adversary) (parameter : PublicParameter)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let root ← liftM
    (Concrete.treeRoot parameter topLayer Concrete.rootTree (tableOts outputs topLayer Concrete.rootTree) :
      OracleComp HashSpec Digest)
  gameRest (tableScheme randomizers) adversary ⟨root, parameter⟩ (tableKey parameter root outputs)

theorem gameCore_deterministic_eq (adversary : Adversary) :
    gameCore scheme adversary = (do
      let seed ← liftM sampleMasterSeed
      let parameter ← liftM (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)
      deterministicGameAfterParameter adversary parameter seed) := by
  simp only [gameCore, scheme, keygen, keygenFromSeed, deterministicGameAfterParameter, gameRest,
    bind_assoc, pure_bind, liftM_bind, liftM_pure]

theorem erases_deterministicGameRest (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known)
      (gameRest scheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩)
      (gameRest (tableScheme randomizers) adversary ⟨root, parameter⟩ (tableKey parameter root outputs)) := by
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
      exact (erases_deterministicSign known parameter seed root outputs randomizers
        hsecrets hrandomizers request).lift_hash.map _

theorem erases_deterministicGameAfterParameter (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known) (deterministicGameAfterParameter adversary parameter seed)
      (tableGameAfterParameter adversary parameter outputs randomizers) := by
  unfold deterministicGameAfterParameter tableGameAfterParameter
  apply (erases_treeRoot known parameter seed outputs hsecrets topLayer Concrete.rootTree).lift_hash.bind
  intro root
  exact erases_deterministicGameRest known parameter seed root outputs randomizers hsecrets hrandomizers adversary

attribute [local irreducible] deterministicGameAfterParameter tableGameAfterParameter signingDerivationCache

theorem evalDist_deterministicGameAfterParameter_prepared (adversary : Adversary) (seed : MasterSeed)
    (parameterOutput : HashOutput) :
    𝒟[(simulateQ romImpl (deterministicGameAfterParameter adversary (truncateHash parameterOutput) seed)).run'
      (parameterCache seed parameterOutput)] =
      𝒟[do
        let outputs ← sampleSecretOutputs
        let randomizers ← sampleRandomizerOutputs
        (simulateQ romImpl (tableGameAfterParameter adversary (truncateHash parameterOutput) outputs randomizers)).run'
          (signingDerivationCache seed parameterOutput outputs randomizers)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareSecrets (truncateHash parameterOutput) seed) : OracleComp OracleWorld SecretOutputs)]
  rw [show simulateQ romImpl (liftM (prepareSecrets (truncateHash parameterOutput) seed) : OracleComp OracleWorld SecretOutputs) =
      simulateQ randomOracle (prepareSecrets (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareSecrets, ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr'
  intro outputs
  rw [evalDist_presample_computation _
    (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs)]
  rw [show simulateQ romImpl (liftM (prepareRandomizers (truncateHash parameterOutput) seed) : OracleComp OracleWorld RandomizerOutputs) =
      simulateQ randomOracle (prepareRandomizers (truncateHash parameterOutput) seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalDist_bind, evalDist_prepareRandomizers, ← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr'
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  exact congrArg _ ((erases_deterministicGameAfterParameter _ _ seed outputs randomizers
    (signingDerivationCache_secret seed parameterOutput outputs randomizers)
    (signingDerivationCache_randomizer seed parameterOutput outputs randomizers) adversary).evalDist_run _ le_rfl)

noncomputable def programmedDeterministicGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← sampleSecretOutputs
  let randomizers ← sampleRandomizerOutputs
  (simulateQ romImpl (tableGameAfterParameter adversary (truncateHash parameterOutput) outputs randomizers)).run'
    (signingDerivationCache seed parameterOutput outputs randomizers)

theorem evalDist_gameCore_deterministic_programmed (adversary : Adversary) :
    𝒟[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒟[programmedDeterministicGame adversary] := by
  rw [gameCore_deterministic_eq, run'_lift_sample_bind]
  unfold programmedDeterministicGame
  apply evalDist_bind_congr'
  intro seed
  rw [run'_lift_hash_bind, run_deriveParameter, bind_map_left]
  exact evalDist_bind_congr' _ (evalDist_deterministicGameAfterParameter_prepared adversary seed)

end SphincsSecurity.Seeded
