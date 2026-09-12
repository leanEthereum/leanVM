import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Scheme.NoMessage
import SphincsSecurity.Proof.Scheme.Replay
/-!
# Cached message inputs

A uniformly sampled signer randomizer addresses an input already in a fixed cache with probability
at most the number of matching cache entries divided by the randomizer space. This is used only
while retaining the few-time coverage event that the cached answer must also satisfy.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

noncomputable local instance instSampleableTypeRandomness : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

def cachedMessageInputSet (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (root : Digest) (message : Message) :
    Set ((t : HashSpec.Domain) × HashSpec.Range t) :=
  {entry ∈ cache.toSet | ∃ randomness,
    entry.1 = tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness)}

noncomputable def cachedMessageEntryCount (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (root : Digest) (message : Message) : ℝ≥0∞ :=
  (((cachedMessageInputSet cache parameter root message).encard : ENat) : ℝ≥0∞)

theorem card_randomness : Fintype.card Randomness = 2 ^ randomnessBits := by
  simp

noncomputable def Concrete.signDigestLoopContinuation
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (randomness : Randomness)
    (result : Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec) :
    ProbComp (Option (Randomness × Index × (IndexGroup → FtsLeaf)) ×
      QueryCache HashSpec) :=
  match result.1 with
  | some (index, leaves) => pure (some (randomness, index, leaves), result.2)
  | none => (simulateQ romImpl
      (Concrete.signDigestLoop attempts secretKey message)).run result.2

attribute [irreducible] Concrete.signDigestLoopContinuation

theorem Concrete.signDigestLoop_run_succ_eq
    (attempts : Nat) (secretKey : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl
      (Concrete.signDigestLoop (attempts + 1) secretKey message)).run cache =
      (($ᵗ Randomness) >>= fun randomness =>
        (simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).run cache >>=
          Concrete.signDigestLoopContinuation attempts secretKey message randomness) := by
  rw [Concrete.signDigestLoop, simulateQ_bind, StateT.run_bind]
  have hsampleRun :
      (simulateQ romImpl (liftM Concrete.sampleRandomness)).run cache =
        (fun randomness => (randomness, cache)) <$> Concrete.sampleRandomness := by
    change (simulateQ (unifFwdImpl HashSpec +
        (randomOracle : QueryImpl HashSpec
          (StateT (QueryCache HashSpec) ProbComp)))
      (liftM Concrete.sampleRandomness)).run cache = _
    exact roSim.run_liftM
      (hashSpec := HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      Concrete.sampleRandomness cache
  rw [hsampleRun, Concrete.sampleRandomness_eq]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr
  intro randomness
  rw [simulateQ_bind, StateT.run_bind]
  have hroute :
      simulateQ romImpl
          (liftM (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) =
        simulateQ randomOracle
          (Concrete.signAttempt secretKey message randomness :
            OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) := by
    change simulateQ (unifFwdImpl HashSpec + randomOracle)
        (liftM (Concrete.signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) = _
    exact QueryImpl.simulateQ_add_liftM_right (unifFwdImpl HashSpec)
      (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))
      (Concrete.signAttempt secretKey message randomness :
        OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
  rw [hroute]
  apply bind_congr
  intro result
  rcases result with ⟨result, resultCache⟩
  cases result with
  | none => simp [Concrete.signDigestLoopContinuation]
  | some selected =>
      rcases selected with ⟨index, leaves⟩
      simp [Concrete.signDigestLoopContinuation]

theorem Concrete.signAfterDigest_some_randomness (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (signature : Signature)
    (heval : evalWithAnswerFn f
      (Concrete.signAfterDigest secretKey randomness index leaves) = some signature) :
    signature.randomness = randomness := by
  simp only [Concrete.signAfterDigest, evalWithAnswerFn_bind] at heval
  cases hparts : evalWithAnswerFn f (Concrete.sequenceLayers fun lay => Concrete.signLayer secretKey index lay) with
  | none => simp only [hparts, evalWithAnswerFn_pure, reduceCtorEq] at heval
  | some parts =>
      simp only [hparts, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Option.some.injEq] at heval
      subst signature
      rfl

theorem Concrete.signAfterDigest_support_some_randomness
    (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (beforeCache afterCache : QueryCache HashSpec)
    (signature : Signature)
    (hmem : (some signature, afterCache) ∈ support
      ((simulateQ (randomOracle : QueryImpl HashSpec _)
        (Concrete.signAfterDigest secretKey randomness index leaves)).run beforeCache)) :
    signature.randomness = randomness := by
  obtain ⟨_, answerFn, _, heval⟩ :=
    exists_answerFn_agrees_final_of_mem_support
      (Concrete.signAfterDigest secretKey randomness index leaves)
      beforeCache (some signature) afterCache hmem
  exact Concrete.signAfterDigest_some_randomness answerFn secretKey randomness index leaves
    signature heval

end SphincsSecurity
