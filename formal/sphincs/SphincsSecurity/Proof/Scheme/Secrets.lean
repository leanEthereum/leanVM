import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Reference.QueryBound
/-!
# Splitting the game at the secrets

Key generation runs first and fixes every honest value, so the reduction reasons about what follows it against a cache it can treat as given: `gameRest` is everything the game does after key generation. The honest structure is a function of the sampled secrets and of the oracle's answers, so a bound that mentions it has to be stated after the secrets are fixed and before any hash query is made. Key generation samples them and then builds layer `0`'s tree, so the useful split is inside key generation: `gameAfterSecrets` makes every hash query the experiment makes, and the accounting therefore starts from the empty cache, at potential `0`, and with nothing to prove about what key generation leaves behind.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

/-- Everything the game does after key generation: run the adversary against the signing oracle,
verify what it returns, and decide whether that counts as a forgery. -/
noncomputable def gameRest (scheme : Scheme SecretKey) (adversary : Adversary) (pk : PublicKey)
    (sk : SecretKey) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog SigningSpec) ←
    (simulateQ (forwardOracles + signingOracle scheme sk) (adversary.main pk)).run
  let verified ← scheme.verify pk forgery.message forgery.signature
  return decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && verified

theorem gameCore_eq (scheme : Scheme SecretKey) (adversary : Adversary) :
    gameCore scheme adversary
      = scheme.keygen >>= fun keys => gameRest scheme adversary keys.1 keys.2 := rfl

namespace Concrete

/-- The game from the sampled secrets on: build the root, then run the adversary against the signer
and verify what it returns. -/
noncomputable def gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) : OracleComp OracleWorld Bool := do
  let root ← liftM
    (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree) : OracleComp HashSpec Digest)
  gameRest scheme adversary ⟨root, parameter⟩ ⟨parameter, root, otsSecret, ftsSecret⟩

attribute [local semireducible] keygen

theorem gameCore_eq_secrets (adversary : Adversary) :
    gameCore scheme adversary = (do
      let parameter ← liftM sampleParameter
      let otsSecret ← liftM sampleOtsSecrets
      let ftsSecret ← liftM sampleFtsSecrets
      gameAfterSecrets adversary parameter otsSecret ftsSecret) := by
  rw [gameCore_eq]
  simp only [scheme, keygen, gameAfterSecrets, bind_assoc, pure_bind]

/-- Lifting a sampling into the game's oracles changes nothing about where it lands. -/
theorem mem_support_liftM_of_mem_support {α : Type} {oa : ProbComp α} {x : α}
    (hmem : x ∈ support oa) : x ∈ support (liftM oa : OracleComp OracleWorld α) := by
  rwa [← liftComp_eq_liftM, support_liftComp]

/-- A lifted sampling passes through the semantics untouched: it samples, and the cache it hands on
is the one it was given. -/
theorem simulateQ_romImpl_liftM_bind_run' {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM oa : OracleComp OracleWorld α) >>= k)).run' cache
      = oa >>= fun x => (simulateQ romImpl (k x)).run' cache := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    show simulateQ romImpl (liftM oa : OracleComp OracleWorld α)
      = simulateQ (unifFwdImpl HashSpec) oa from QueryImpl.simulateQ_add_liftM_left _ _ oa,
    unifFwdImpl.simulateQ_run]
  simp [map_eq_bind_pure_comp, bind_assoc, StateT.run'_eq]

/-- The query bound survives the split: what bounds the whole experiment bounds what follows the
secrets. -/
theorem hashQueryBound_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) {parameter : PublicParameter}
    (hparameter : parameter ∈ support sampleParameter)
    {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
    (hots : otsSecret ∈ support sampleOtsSecrets)
    {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
    (hfts : ftsSecret ∈ support sampleFtsSecrets) :
    HashQueryBound (gameAfterSecrets adversary parameter otsSecret ftsSecret) ∅ q := by
  rw [hasHashQueryBound_iff, gameCore_eq_secrets] at hq
  exact hashQueryBound_of_sampling_bind _ _ ∅ q
    (hashQueryBound_of_sampling_bind _ _ ∅ q
      (hashQueryBound_of_sampling_bind _ _ ∅ q hq parameter hparameter) otsSecret hots)
    ftsSecret hfts

end Concrete

end SphincsSecurity
