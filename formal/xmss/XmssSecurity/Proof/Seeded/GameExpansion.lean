import XmssSecurity.Proof.Seeded.KeygenSampling

open OracleComp OracleSpec

namespace XmssSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

noncomputable def gameRest {Key : Type} (scheme : Scheme Key) (adversary : Adversary)
    (pk : PublicKey) (sk : Key) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.epoch forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (secret : ChainSecrets) : OracleComp OracleWorld Bool := do
  let result ← liftM
    (Concrete.treeNode parameter secret treeHeight Concrete.rootNode : OracleComp HashSpec Digest).withQueryLog
  let sk := Concrete.precomputedSecretKey parameter secret (hashCacheOfLog result.2)
  gameRest Concrete.scheme adversary ⟨result.1, parameter⟩ sk

theorem gameCore_seeded_eq (adversary : Adversary) :
    gameCore scheme adversary = (do
      let seed ← liftM sampleMasterSeed
      let (parameter, secret) ← liftM (deriveParametersAndSecrets seed)
      gameAfterSecrets adversary parameter secret) := by
  simp only [gameCore, scheme, keygen, gameAfterSecrets, gameRest, Concrete.scheme,
    deriveParametersAndSecrets, deriveChainSecrets, liftM_bind, liftM_pure,
    bind_assoc, pure_bind, signingOracle]

theorem gameCore_independent_eq (adversary : Adversary) :
    gameCore Concrete.scheme adversary = (do
      let parameter ← liftM Concrete.samplePublicParameter
      let secret ← liftM Concrete.sampleSecret
      gameAfterSecrets adversary parameter secret) := by
  simp only [gameCore, Concrete.scheme, Concrete.precomputedKeygen, gameAfterSecrets,
    gameRest, bind_assoc, pure_bind]

theorem run'_lift_hash_bind {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

noncomputable def programmedGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let parameter ← Concrete.samplePublicParameter
  let secret ← Concrete.sampleSecret
  let parameterHigh ← $ᵗ Digest
  let secretHigh ← Concrete.sampleSecret
  (simulateQ romImpl (gameAfterSecrets adversary parameter secret)).run'
    (programmedCache seed parameter secret parameterHigh secretHigh)

/-- The seeded forgery game is exactly the independent-secret game with its derivation answers installed. -/
theorem evalDist_gameCore_eq_programmed (adversary : Adversary) :
    𝒟[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒟[programmedGame adversary] := by
  rw [gameCore_seeded_eq, run'_lift_sample_bind]
  unfold programmedGame
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro seed
  rw [run'_lift_hash_bind, evalDist_bind, evalDist_deriveParametersAndSecrets_eq_independent,
    ← evalDist_bind]
  simp only [bind_assoc, pure_bind]

end XmssSecurity.Seeded
