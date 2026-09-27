import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Hypertree.Descent
import SphincsSecurity.Proof.Scheme.ReplayWorld
/-!
# Successful signer executions

A successful signer invocation exposes its chosen index and leaf vector, its honest few-time
opening, and one successful honest one-time signing computation at every layer.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev LayerPart :=
  Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest)

def SuccessfulDigestRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (message : Message) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : Prop :=
  randomness ∈ support sampleRandomness
    ∧ evalWithAnswerFn f (signAttempt secretKey message randomness) = some (index, leaves)
    ∧ CachedRun cache f (signAttempt secretKey message randomness)

theorem SuccessfulDigestRun.extract {f : QueryImpl HashSpec Id} {cache : QueryCache HashSpec}
    {secretKey : SecretKey} {message : Message} {randomness : Randomness} {index : Index}
    {leaves : IndexGroup → FtsLeaf}
    (hrun : SuccessfulDigestRun f cache secretKey message randomness index leaves) :
    randomness ∈ support sampleRandomness
      ∧ ∃ digest : MessageDigest,
        evalWithAnswerFn f
            (messageDigest secretKey.parameter secretKey.root message randomness) = digest
          ∧ Admissible digest
          ∧ index = digestIndex digest
          ∧ leaves = digestLeaves digest
          ∧ CachedRun cache f
            (messageDigest secretKey.parameter secretKey.root message randomness) := by
  refine ⟨hrun.1, ?_⟩
  have heval := hrun.2.1
  simp only [signAttempt, evalWithAnswerFn_bind] at heval
  let digest := evalWithAnswerFn f
    (messageDigest secretKey.parameter secretKey.root message randomness)
  by_cases hadmissible : Admissible digest
  · simp only [show Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_true, evalWithAnswerFn_pure] at heval
    have hresult : (digestIndex digest, digestLeaves digest) = (index, leaves) :=
      Option.some.inj heval
    have hfields := Prod.mk.inj hresult
    refine ⟨digest, rfl, hadmissible, hfields.1.symm, hfields.2.symm, ?_⟩
    exact hrun.2.2.bind_left
  · simp only [show ¬ Admissible (evalWithAnswerFn f
        (messageDigest secretKey.parameter secretKey.root message randomness)) from hadmissible,
      if_false, evalWithAnswerFn_pure] at heval
    simp at heval

theorem successfulDigestLoop_of_mem_support (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (message : Message) (attempts : Nat) (randomness : Randomness)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (beforeCache afterCache finalCache : QueryCache HashSpec)
    (hmem : (some (randomness, index, leaves), afterCache) ∈ support
      ((simulateQ (replayRomImpl f) (signDigestLoop attempts secretKey message)).run beforeCache))
    (hleFinal : afterCache ≤ finalCache) (hf : finalCache.AgreesWithFn f) :
    SuccessfulDigestRun f finalCache secretKey message randomness index leaves := by
  induction attempts generalizing beforeCache afterCache randomness index leaves with
  | zero =>
      simp only [signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      cases hmem.1
  | succ attempts ih =>
      rw [signDigestLoop, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨sampledRandomness, sampleCache⟩, hsample, hrest⟩ := hmem
      have hsample' : (sampledRandomness, sampleCache) ∈ support
          ((simulateQ (unifFwdImpl HashSpec) sampleRandomness).run beforeCache) := by
        simpa only [replayRomImpl, QueryImpl.simulateQ_add_liftM_left] using hsample
      rw [unifFwdImpl.simulateQ_run, support_map] at hsample'
      obtain ⟨sampledRandomness', hsampled, heq⟩ := hsample'
      obtain ⟨rfl, rfl⟩ := heq
      rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
      obtain ⟨⟨attempt, attemptCache⟩, hattempt, hfinish⟩ := hrest
      cases attempt with
      | none =>
          exact ih (randomness := randomness) (index := index) (leaves := leaves)
            (beforeCache := attemptCache) (afterCache := afterCache) hfinish hleFinal
      | some selected =>
          obtain ⟨selectedIndex, selectedLeaves⟩ := selected
          simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
            Prod.mk.injEq, Option.some.injEq] at hfinish
          obtain ⟨hresult, hcache⟩ := hfinish
          obtain ⟨rfl, rfl, rfl⟩ := hresult
          have hleAttempt : attemptCache ≤ finalCache := by
            rw [← hcache]
            exact hleFinal
          have hattempt' : (some (index, leaves), attemptCache) ∈ support
              ((simulateQ (replayHashImpl f)
                (signAttempt secretKey message randomness)).run beforeCache) := by
            simpa only [simulateQ_replayRom_liftM] using hattempt
          have hfAttempt : attemptCache.AgreesWithFn f :=
            fun _ _ hcached => hf (hleAttempt hcached)
          obtain ⟨_, heval, hcached⟩ := replayHash_of_mem_support f
            (signAttempt secretKey message randomness) beforeCache (some (index, leaves))
            attemptCache hattempt' hfAttempt
          exact ⟨hsampled, heval, hcached.mono hleAttempt⟩

theorem index_eq_of_bottom_position_eq {left right : Index}
    (htree : treeIndexAt left bottomLayer = treeIndexAt right bottomLayer)
    (hleaf : leafIndexAt left bottomLayer = leafIndexAt right bottomLayer) : left = right := by
  apply Fin.ext
  have htreeVal := congrArg Fin.val htree
  have hleafVal := congrArg Fin.val hleaf
  have habove : heightAbove bottomLayer = 28 := by decide
  have hheight : layerHeight bottomLayer = 6 := by decide
  have hleftTree : (treeIndexAt left bottomLayer).val = left.val / 64 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hrightTree : (treeIndexAt right bottomLayer).val = right.val / 64 := by
    rw [treeIndexAt_val, habove]
    norm_num [totalHeight]
  have hleftLeaf : (leafIndexAt left bottomLayer).val = left.val % 64 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  have hrightLeaf : (leafIndexAt right bottomLayer).val = right.val % 64 := by
    rw [leafIndexAt_bottomLayer, hheight]
    norm_num
  rw [hleftTree, hrightTree] at htreeVal
  rw [hleftLeaf, hrightLeaf] at hleafVal
  omega

theorem layerMessage_eq_of_position_eq (secretKey : SecretKey) (left right : Index)
    (lay : Layer) (htree : treeIndexAt left lay = treeIndexAt right lay)
    (hleaf : leafIndexAt left lay = leafIndexAt right lay) :
    layerMessage (m := OracleComp HashSpec) secretKey left lay =
      layerMessage secretKey right lay := by
  by_cases hnext : lay.val + 1 < numLayers
  · have htreeNext : treeIndexAt left ⟨lay.val + 1, hnext⟩ =
        treeIndexAt right ⟨lay.val + 1, hnext⟩ := by
      apply Fin.ext
      rw [layers_link_next left lay hnext, layers_link_next right lay hnext,
        congrArg Fin.val htree, congrArg Fin.val hleaf]
    rw [layerMessage_of_lt secretKey left lay hnext,
      layerMessage_of_lt secretKey right lay hnext]
    simp only [htreeNext]
  · have hbottom : lay = bottomLayer := by
      fin_cases lay <;> simp_all [bottomLayer, numLayers]
    subst lay
    have hindex := index_eq_of_bottom_position_eq htree hleaf
    subst right
    rfl

end SphincsSecurity.Concrete
