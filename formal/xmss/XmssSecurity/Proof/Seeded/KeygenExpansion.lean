import XmssSecurity.Proof.Seeded.FreshTable
import XmssSecurity.Proof.Seeded.SeedGuessing
import XmssSecurity.Proof.RandomOracle

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

abbrev ChainOutputs := Epoch → ChainIndex → HashOutput

def chainInputs (parameter : PublicParameter) (seed : MasterSeed) (epoch : Epoch) (chain : ChainIndex) :
    HashInput := keygenHashInput parameter (.chain epoch chain) seed

theorem chainInputs_injective (parameter : PublicParameter) (seed : MasterSeed)
    (epoch epoch' : Epoch) (chain chain' : ChainIndex)
    (h : chainInputs parameter seed epoch chain = chainInputs parameter seed epoch' chain') :
    epoch = epoch' ∧ chain = chain' :=
  KeygenDomain.chain.inj (keygenHashInput_injective h).2.1

def parameterCache (seed : MasterSeed) (output : HashOutput) : QueryCache HashSpec :=
  (∅ : QueryCache HashSpec).cacheQuery (keygenHashInput 0 .parameter seed) output

theorem parameterCache_chain_fresh (seed : MasterSeed) (output : HashOutput)
    (parameter : PublicParameter) (epoch : Epoch) (chain : ChainIndex) :
    parameterCache seed output (chainInputs parameter seed epoch chain) = none := by
  apply QueryCache.cacheQuery_of_ne
  intro h
  have hdomain := (keygenHashInput_injective h).2.1
  cases hdomain

def derivationCache (seed : MasterSeed) (parameterOutput : HashOutput) (outputs : ChainOutputs) :
    QueryCache HashSpec :=
  cacheRows (parameterCache seed parameterOutput) (chainInputs (truncateHash parameterOutput) seed) outputs

/-- The initial cache can differ from an empty oracle only at inputs naming this seed. -/
theorem derivationCache_of_not_seedHit (seed : MasterSeed) (parameterOutput : HashOutput)
    (outputs : ChainOutputs) (input : HashInput) (hinput : ¬ SeedHit input seed) :
    derivationCache seed parameterOutput outputs input = none := by
  unfold derivationCache
  rw [cacheRows_apply_of_not_mem]
  · apply QueryCache.cacheQuery_of_ne
    intro h
    exact hinput ⟨0, .parameter, h.symm⟩
  · intro epoch chain h
    exact hinput ⟨truncateHash parameterOutput, .chain epoch chain, h.symm⟩

def deriveChainSecrets (parameter : PublicParameter) (seed : MasterSeed) :
    OracleComp HashSpec (Epoch → ChainIndex → Digest) :=
  Concrete.sequenceFin fun epoch => Concrete.sequenceFin fun chain =>
    deriveKey parameter (.chain epoch chain) seed

noncomputable def drawChainOutputs : ProbComp ChainOutputs :=
  Concrete.sequenceFin fun _ : Epoch => Concrete.sequenceFin fun _ : ChainIndex => $ᵗ HashOutput

def outputSecrets (outputs : ChainOutputs) : Epoch → ChainIndex → Digest :=
  fun epoch chain => truncateHash (outputs epoch chain)

theorem deriveChainSecrets_eq_map (parameter : PublicParameter) (seed : MasterSeed) :
    deriveChainSecrets parameter seed =
      outputSecrets <$> Concrete.sequenceFin (fun epoch => Concrete.sequenceFin fun chain =>
        (liftM (HashSpec.query (chainInputs parameter seed epoch chain)) : OracleComp HashSpec HashOutput)) := by
  simp only [deriveChainSecrets, deriveKey, Concrete.oracleHash, bind_pure_comp,
    sequenceFin_map, chainInputs]
  rfl

/-- The actual WOTS derivation loop, including its final cache, equals fresh full-output sampling. -/
theorem run_deriveChainSecrets (seed : MasterSeed) (parameterOutput : HashOutput) :
    (simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput) =
        (fun outputs => (outputSecrets outputs, derivationCache seed parameterOutput outputs)) <$>
          drawChainOutputs := by
  rw [deriveChainSecrets_eq_map, simulateQ_map, StateT.run_map,
    run_sequenceFin_rows_fresh _
      (fun epoch chain epoch' chain' => chainInputs_injective _ seed epoch epoch' chain chain')
      _ (parameterCache_chain_fresh seed parameterOutput _)]
  simp only [bind_pure_comp, Functor.map_map, drawChainOutputs, derivationCache]

theorem evalDist_drawChainOutputs : 𝒟[drawChainOutputs] = 𝒟[$ᵗ ChainOutputs] := by
  calc
    _ = 𝒟[Concrete.sequenceFin fun _ : Epoch => ($ᵗ (ChainIndex → HashOutput))] :=
      evalDist_sequenceFin_congr _ _ (fun _ => evalDist_sequenceFin_uniform _)
    _ = _ := evalDist_sequenceFin_uniform _

theorem evalDist_deriveChainSecrets (seed : MasterSeed) (parameterOutput : HashOutput) :
    𝒟[(simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] =
        𝒟[(fun outputs => (outputSecrets outputs, derivationCache seed parameterOutput outputs)) <$>
          ($ᵗ ChainOutputs)] := by
  rw [run_deriveChainSecrets, evalDist_map, evalDist_map, evalDist_drawChainOutputs]

def deriveParametersAndSecrets (seed : MasterSeed) :
    OracleComp HashSpec (PublicParameter × (Epoch → ChainIndex → Digest)) := do
  let parameter ← deriveKey 0 .parameter seed
  let secrets ← deriveChainSecrets parameter seed
  return (parameter, secrets)

theorem run_deriveParameter (seed : MasterSeed) :
    (simulateQ randomOracle (deriveKey 0 .parameter seed : OracleComp HashSpec Digest)).run ∅ =
      (fun output => (truncateHash output, parameterCache seed output)) <$> ($ᵗ HashOutput) := by
  have hquery : (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) =
      truncateHash <$> (liftM (HashSpec.query (keygenHashInput 0 .parameter seed)) :
        OracleComp HashSpec HashOutput) := by
    simp only [deriveKey, Concrete.oracleHash, bind_pure_comp]
    rfl
  rw [hquery, simulateQ_map, StateT.run_map, simulateQ_spec_query,
    QueryImpl.withCaching_run_none _ (QueryCache.empty_apply _)]
  simp only [Functor.map_map]
  rfl

/-- Exact joint distribution of the derived values and every full answer retained by the oracle. -/
theorem evalDist_deriveParametersAndSecrets (seed : MasterSeed) :
    𝒟[(simulateQ randomOracle (deriveParametersAndSecrets seed)).run ∅] =
      𝒟[do
        let parameterOutput ← $ᵗ HashOutput
        let outputs ← $ᵗ ChainOutputs
        pure ((truncateHash parameterOutput, outputSecrets outputs),
          derivationCache seed parameterOutput outputs)] := by
  simp only [deriveParametersAndSecrets, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure]
  rw [run_deriveParameter]
  simp only [bind_map_left, bind_pure_comp]
  change 𝒟[($ᵗ HashOutput) >>= _] = 𝒟[($ᵗ HashOutput) >>= _]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro parameterOutput
  change 𝒟[(fun result => ((truncateHash parameterOutput, result.1), result.2)) <$>
    (simulateQ randomOracle (deriveChainSecrets (truncateHash parameterOutput) seed)).run
      (parameterCache seed parameterOutput)] = _
  rw [evalDist_map, evalDist_deriveChainSecrets, ← evalDist_map]
  simp only [Functor.map_map]

end XmssSecurity.Seeded
