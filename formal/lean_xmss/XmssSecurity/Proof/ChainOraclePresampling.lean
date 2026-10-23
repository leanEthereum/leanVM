import XmssSecurity.Proof.QueryPresence
import XmssSecurity.Proof.StatementLemmas
import XmssSecurity.Proof.ChainTableUniformity
import XmssSecurity.Proof.AdaptiveFreshTarget
import XmssSecurity.Proof.RandomOraclePresampling
import XmssSecurity.Proof.HiddenValue
import XmssSecurity.Proof.UniformFiniteTable
import XmssSecurity.Proof.HonestKeygenRun
import XmssSecurity.Proof.TopKeygenFacts

/-!
# Presampling the chains of key generation

Key generation walks every chain of both layers, so its run equals the run that first computes every
chain trajectory and then runs key generation from the warmed cache.
-/

open OracleComp OracleSpec ENNReal
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational

namespace XmssSecurity.Concrete.CacheReplay

attribute [local irreducible] Concrete.topTreeNode

@[simp]
theorem eval_keyChainWalk (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    evalWithAnswerFn (answerFn cache)
      (Concrete.keyChainWalk parameter key chain position steps value :
        OracleComp HashSpec Digest) =
      Wots.walk (CacheView.keyChainStep cache parameter key chain) position steps value := by
  cases key with
  | inl leafIndex =>
      rw [Concrete.keyChainWalk_inl, eval_chainWalk]
      rfl
  | inr key =>
      rw [Concrete.keyChainWalk_inr, eval_topChainWalk]
      rfl

theorem keyChainWalk_query_cached_in_largerCache
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps)
    (hposition : position + offset < chainLength - 1)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.keyChainWalk parameter key chain position steps value :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.keyChainInput parameter key chain
        ⟨position + offset, hposition⟩
        (Wots.walk (Concrete.CacheView.keyChainStep largerCache parameter key chain)
          position offset value)) = some output := by
  induction steps generalizing offset initialCache resultCache digest with
  | zero => omega
  | succ steps ih =>
      rw [Concrete.keyChainWalk, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨previous, middleCache⟩, hprefix, hrest⟩ := hmem
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le
          (if hlast : position + steps < chainLength - 1 then
            Concrete.keyChainHash parameter key chain ⟨position + steps, hlast⟩ previous
          else pure 0 : OracleComp HashSpec Digest)
          middleCache (digest, resultCache) hrest
      by_cases hbefore : offset < steps
      · exact ih offset hbefore hposition initialCache middleCache previous hprefix
          (hmiddleLe.trans hle)
      · have hoffsetEq : offset = steps := by omega
        subst offset
        simp only [hposition, ↓reduceDIte] at hrest
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (key.chainDomain chain ⟨position + steps, hposition⟩)
          (Concrete.digestBytes previous) middleCache resultCache digest hrest
        have hprevious := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.keyChainWalk parameter key chain position steps value :
            OracleComp HashSpec Digest)
          initialCache middleCache largerCache previous hprefix (hmiddleLe.trans hle)
        rw [eval_keyChainWalk] at hprevious
        refine ⟨output, ?_⟩
        rw [hprevious]
        exact hle hcached

theorem chainWalk_query_cached_in_largerCache
    (parameter : PublicParameter) (leafIndex : LeafIndex) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) (offset : Nat)
    (hoffset : offset < steps)
    (hposition : position + offset < chainLength - 1)
    (initialCache resultCache largerCache : QueryCache HashSpec) (digest : Digest)
    (hmem : (digest, resultCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.chainWalk parameter leafIndex chain position steps value :
          OracleComp HashSpec Digest)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ output, largerCache
      (Concrete.CacheView.chainInput parameter leafIndex chain
        ⟨position + offset, hposition⟩
        (Wots.walk (Concrete.CacheView.chainStep largerCache parameter leafIndex chain)
          position offset value)) = some output := by
  induction steps generalizing offset initialCache resultCache digest with
  | zero => omega
  | succ steps ih =>
      rw [Concrete.chainWalk, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨previous, middleCache⟩, hprefix, hrest⟩ := hmem
      have hmiddleLe : middleCache ≤ resultCache :=
        randomOracle_cache_le
          (if hlast : position + steps < chainLength - 1 then
            Concrete.chainHash parameter leafIndex chain ⟨position + steps, hlast⟩ previous
          else pure 0 : OracleComp HashSpec Digest)
          middleCache (digest, resultCache) hrest
      by_cases hbefore : offset < steps
      · exact ih offset hbefore hposition initialCache middleCache previous hprefix
          (hmiddleLe.trans hle)
      · have hoffsetEq : offset = steps := by omega
        subst offset
        simp only [hposition, ↓reduceDIte] at hrest
        obtain ⟨output, hcached, _⟩ := tweakableHash_query_cached parameter
          (.chain leafIndex chain ⟨position + steps, hposition⟩)
          (Concrete.digestBytes previous) middleCache resultCache digest hrest
        have hprevious := eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainWalk parameter leafIndex chain position steps value :
            OracleComp HashSpec Digest)
          initialCache middleCache largerCache previous hprefix (hmiddleLe.trans hle)
        rw [eval_chainWalk] at hprevious
        refine ⟨output, ?_⟩
        rw [hprevious]
        exact hle hcached

theorem sequenceFin_component_support_in_largerCache {n : Nat}
    (computation : Fin n → OracleComp HashSpec α) (target : Fin n)
    (initialCache resultCache largerCache : QueryCache HashSpec) (values : Fin n → α)
    (hmem : (values, resultCache) ∈ support
      ((simulateQ randomOracle (Concrete.sequenceFin computation)).run initialCache))
    (hle : resultCache ≤ largerCache) :
    ∃ beforeCache afterCache value,
      (value, afterCache) ∈ support
        ((simulateQ randomOracle (computation target)).run beforeCache) ∧
      afterCache ≤ largerCache := by
  induction n generalizing initialCache resultCache largerCache with
  | zero => exact Fin.elim0 target
  | succ n ih =>
      rw [Concrete.sequenceFin, simulateQ_bind, StateT.run_bind,
        mem_support_bind_iff] at hmem
      obtain ⟨⟨head, headCache⟩, hhead, hrest⟩ := hmem
      obtain rfl | ⟨tailTarget, rfl⟩ := target.eq_zero_or_eq_succ
      · have hheadLe : headCache ≤ largerCache :=
          (randomOracle_cache_le
            (do
              let tail ← Concrete.sequenceFin fun index : Fin n => computation index.succ
              pure (Fin.cases head tail) : OracleComp HashSpec (Fin (n + 1) → α))
            headCache (values, resultCache) hrest).trans hle
        exact ⟨initialCache, headCache, head, hhead, hheadLe⟩
      · rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
        obtain ⟨⟨tail, tailCache⟩, htail, hfinal⟩ := hrest
        simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hfinal
        cases hfinal
        exact ih (fun index => computation index.succ) tailTarget headCache resultCache
          largerCache tail htail hle

/-- A prefix of a chain walk runs inside the walk's run. -/
theorem RunsBelow.keyChainWalk_prefix {parameter : PublicParameter} {key : ChainKey}
    {chain : ChainIndex} {position : Nat} {value : Digest} {cache : QueryCache HashSpec}
    {steps : Nat} (prefixSteps : Nat) (hprefix : prefixSteps ≤ steps)
    (hrun : RunsBelow (Concrete.keyChainWalk parameter key chain position steps value :
      OracleComp HashSpec Digest) cache) :
    RunsBelow (Concrete.keyChainWalk parameter key chain position prefixSteps value :
      OracleComp HashSpec Digest) cache := by
  induction steps with
  | zero =>
      obtain rfl : prefixSteps = 0 := by omega
      exact hrun
  | succ steps ih =>
      by_cases hsame : prefixSteps = steps + 1
      · subst hsame
        exact hrun
      obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
      rw [Concrete.keyChainWalk] at hmem
      obtain ⟨previous, middleCache, hprevious, _, hmiddleLe⟩ := runsBelow_bind_left hmem
      exact ih (by omega) ⟨beforeCache, middleCache, previous, hprevious, hmiddleLe.trans hafter⟩

/-- A chain walk that ran below a cache has its every step's input cached there. -/
theorem RunsBelow.keyChainInput_cached
    {parameter : PublicParameter} {key : ChainKey} {chain : ChainIndex} {steps : Nat}
    {value : Digest} {cache : QueryCache HashSpec}
    (hrun : RunsBelow (Concrete.keyChainWalk parameter key chain 0 steps value :
      OracleComp HashSpec Digest) cache)
    (step : ChainStep) (hstep : step.val < steps) :
    ∃ output, cache
      (Concrete.CacheView.keyChainInput parameter key chain step
        (Wots.walk (Concrete.CacheView.keyChainStep cache parameter key chain)
          0 step.val value)) = some output := by
  obtain ⟨beforeCache, afterCache, digest, hmem, hafter⟩ := hrun
  have h := keyChainWalk_query_cached_in_largerCache parameter key chain 0 steps value
    step.val hstep (by simp) beforeCache afterCache cache digest hmem hafter
  have hstepEq : (⟨0 + step.val, by simp⟩ : ChainStep) = step :=
    Fin.ext (by simp)
  rw [hstepEq] at h
  exact h

end XmssSecurity.Concrete.CacheReplay

namespace XmssSecurity

open Concrete.CacheReplay

/-- Key generation's honest computation from one start function for both layers' chains and fixed
top bases. -/
abbrev Concrete.honestKeygenFrom (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (topBase : TopIndex → Randomness) :
    OracleComp HashSpec (Digest × (TopIndex → Option (Randomness × Encoding))) :=
  Concrete.honestKeygen parameter (fun leafIndex => start (.inl leafIndex))
    (fun key => start (.inr key)) (fun key _ => pure (topBase key))

/-- Every run of a computation walks every chain of both layers from its start. -/
def CoversKeyChains {α : Type} (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (computation : OracleComp HashSpec α) : Prop :=
  ∀ initialCache result, result ∈ support ((simulateQ randomOracle computation).run initialCache) →
    ∀ key chain steps, steps ≤ chainLength - 1 →
      RunsBelow (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
        OracleComp HashSpec Digest) result.2

theorem honestKeygenFrom_coversKeyChains (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (topBase : TopIndex → Randomness) :
    CoversKeyChains parameter start (Concrete.honestKeygenFrom parameter start topBase) := by
  intro initialCache result hresult key chain steps hsteps
  cases key with
  | inl leafIndex =>
      rw [Concrete.keyChainWalk_inl]
      exact honestKeygen_runsBelow_chainWalk hresult leafIndex chain steps hsteps
  | inr key =>
      rw [Concrete.keyChainWalk_inr]
      exact honestKeygen_runsBelow_topChainWalk hresult key chain steps hsteps

theorem CoversKeyChains.input_cached {α : Type} {parameter : PublicParameter}
    {start : ChainKey → ChainIndex → Digest} {computation : OracleComp HashSpec α}
    (hcovers : CoversKeyChains parameter start computation)
    (initialCache : QueryCache HashSpec) (result : α × QueryCache HashSpec)
    (hresult : result ∈ support ((simulateQ randomOracle computation).run initialCache))
    (key : ChainKey) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, result.2
      (Concrete.CacheView.keyChainInput parameter key chain step
        (Wots.walk (Concrete.CacheView.keyChainStep result.2 parameter key chain)
          0 step.val (start key chain))) = some output :=
  (hcovers initialCache result hresult key chain (step.val + 1) (by omega)).keyChainInput_cached
    step (by omega)

/-- A key generation result: its cache holds every chain step of both layers. -/
theorem Concrete.keygen_cache_has_chainInput
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) (chain : ChainIndex) (step : ChainStep) :
    ∃ output, keyResult.2
      (Concrete.CacheView.keyChainInput keyResult.1.2.parameter key chain step
        (Wots.walk
          (Concrete.CacheView.keyChainStep keyResult.2 keyResult.1.2.parameter key chain)
          0 step.val (keyResult.1.2.keyChainStart key chain))) = some output := by
  obtain ⟨parameter, secret, topSecret, topBase, root, hkey, hroot⟩ :=
    Concrete.keygen_support_rootTree keyResult hmem
  rw [hkey]
  have hcovers := honestKeygenFrom_coversKeyChains parameter (Sum.elim secret topSecret) topBase
  exact hcovers.input_cached ∅ (root, keyResult.2) hroot key chain step

theorem Concrete.keygen_cache_chainInput_eq_none_of_ne
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (key : ChainKey) (chain : ChainIndex) (step : ChainStep) (value : Digest)
    (hne : value ≠ Wots.walk
      (Concrete.CacheView.keyChainStep keyResult.2 keyResult.1.2.parameter key chain)
      0 step.val (keyResult.1.2.keyChainStart key chain)) :
    keyResult.2
      (Concrete.CacheView.keyChainInput keyResult.1.2.parameter key chain step value) = none := by
  obtain ⟨honestOutput, hhonest⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hmem key chain step
  cases hcandidate : keyResult.2
      (Concrete.CacheView.keyChainInput keyResult.1.2.parameter key chain step value) with
  | none => rfl
  | some candidateOutput =>
      exfalso
      apply hne
      have heq := Concrete.keygen_cache_unique_keyChainAddress keyResult hmem key chain step
        _ _ candidateOutput honestOutput
        (Concrete.CacheView.keyChainInput_atHashAddress _ _ _ _ _)
        (Concrete.CacheView.keyChainInput_atHashAddress _ _ _ _ _) hcandidate hhonest
      exact ((Concrete.CacheView.keyChainInput_eq_iff _ _ _ _ _ _ _ _ _).mp heq).2.2.2

theorem Concrete.keygen_chainWalk_eq_of_cache_le
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hmem : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (largerCache : QueryCache HashSpec) (hle : keyResult.2 ≤ largerCache)
    (key : ChainKey) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) :
    Wots.walk
        (Concrete.CacheView.keyChainStep keyResult.2 keyResult.1.2.parameter key chain)
        0 steps (keyResult.1.2.keyChainStart key chain) =
      Wots.walk
        (Concrete.CacheView.keyChainStep largerCache keyResult.1.2.parameter key chain)
        0 steps (keyResult.1.2.keyChainStart key chain) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      have hstep : steps < chainLength - 1 := by omega
      have ih' := ih (by omega)
      obtain ⟨output, hcached⟩ := Concrete.keygen_cache_has_chainInput keyResult hmem
        key chain ⟨steps, hstep⟩
      have hcachedLarger := hle hcached
      rw [ih'] at hcached hcachedLarger
      simp only [Wots.walk, zero_add]
      rw [ih']
      rw [Concrete.CacheView.keyChainStep_eq _ _ _ _ _ _ hstep,
        Concrete.CacheView.keyChainStep_eq _ _ _ _ _ _ hstep]
      rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached,
        Concrete.CacheView.digestAt_eq_of_cache_eq_some hcachedLarger]

/-! ### Chain tables and their edges -/

abbrev ChainEdgeIndex := ChainKey × ChainStep

def chainTableEdgeInput
    (parameter : PublicParameter) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : HashInput :=
  Concrete.CacheView.keyChainInput parameter edge.1 chain edge.2
    (table (edge.1, chainStepDigit edge.2))

def chainStepNextDigit (step : ChainStep) : Digit :=
  ⟨step.val + 1, by
    have hstep := step.isLt
    omega⟩

def chainTableEdgeTarget
    (table : ChainValueIndex → Digest) (edge : ChainEdgeIndex) : Digest :=
  table (edge.1, chainStepNextDigit edge.2)

def ChainTableSeedsMatch
    (secretKey : SecretKey) (chain : ChainIndex)
    (table : ChainValueIndex → Digest) : Prop :=
  ∀ key, secretKey.keyChainStart key chain = table (key, ⟨0, by simp [chainLength]⟩)

def ChainTableEdgesMatch
    (cache : QueryCache HashSpec) (parameter : PublicParameter)
    (chain : ChainIndex) (table : ChainValueIndex → Digest) : Prop :=
  ∀ edge, ∃ output,
    cache (chainTableEdgeInput parameter chain table edge) = some output ∧
      truncateHash output = chainTableEdgeTarget table edge

theorem ChainTableEdgesMatch.mono
    {cache larger : QueryCache HashSpec} {parameter : PublicParameter}
    {chain : ChainIndex} {table : ChainValueIndex → Digest}
    (hmatch : ChainTableEdgesMatch cache parameter chain table)
    (hle : cache ≤ larger) :
    ChainTableEdgesMatch larger parameter chain table := by
  intro edge
  obtain ⟨output, hcached, htarget⟩ := hmatch edge
  exact ⟨output, hle hcached, htarget⟩

theorem evalDist_listOfFn_uniform_eq_drawList (count : Nat) :
    (List.ofFn <$> ($ᵗ (Fin count → Digest))) =ᵈ
      (OracleComp.drawList ($ᵗ Digest) count) :=
  (evalDist_drawList_uniform_eq_uniformFunction Digest count).symm

theorem keygenChainValueTable_seedsMatch
    (cache : QueryCache HashSpec) (secretKey : SecretKey) (chain : ChainIndex) :
    ChainTableSeedsMatch secretKey chain
      (keygenChainValueTable cache secretKey chain) := by
  intro key
  simp [keygenChainValueTable]

set_option maxRecDepth 10000 in
theorem Concrete.keygenChainValueTable_edgesMatch
    (keyResult : (PublicKey × SecretKey) × QueryCache HashSpec)
    (hkeygen : keyResult ∈ support
      ((simulateQ romImpl Concrete.keygen).run ∅))
    (chain : ChainIndex) :
    ChainTableEdgesMatch keyResult.2 keyResult.1.2.parameter chain
      (keygenChainValueTable keyResult.2 keyResult.1.2 chain) := by
  intro edge
  obtain ⟨output, hcached⟩ :=
    Concrete.keygen_cache_has_chainInput keyResult hkeygen edge.1 chain edge.2
  refine ⟨output, ?_, ?_⟩
  · simpa [chainTableEdgeInput, keygenChainValueTable, chainStepDigit] using hcached
  · have hstep := Concrete.CacheView.keyChainStep_eq keyResult.2 keyResult.1.2.parameter
      edge.1 chain edge.2.val
      (Wots.walk (Concrete.CacheView.keyChainStep keyResult.2 keyResult.1.2.parameter
        edge.1 chain) 0 edge.2.val (keyResult.1.2.keyChainStart edge.1 chain)) edge.2.isLt
    rw [Concrete.CacheView.digestAt_eq_of_cache_eq_some hcached] at hstep
    simp only [chainTableEdgeTarget, keygenChainValueTable, chainStepNextDigit, Wots.walk,
      zero_add]
    exact hstep.symm

/-! ### Warming the chains -/

section Warm

variable {α : Type} (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
  (computation : OracleComp HashSpec α)

theorem evalDist_run_eq_keyChainHash_then
    (hcovers : CoversKeyChains parameter start computation)
    (key : ChainKey) (chain : ChainIndex) (steps : Nat) (previous : Digest)
    (initialCache prefixCache : QueryCache HashSpec)
    (hvalid : steps < chainLength - 1)
    (hprefix : (previous, prefixCache) ∈ support
      ((simulateQ randomOracle
        (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
          OracleComp HashSpec Digest)).run initialCache)) :
    ((simulateQ randomOracle computation).run prefixCache) =ᵈ
      ((simulateQ randomOracle
        (Concrete.keyChainHash parameter key chain ⟨steps, hvalid⟩ previous :
          OracleComp HashSpec Digest)).run prefixCache >>= fun hashResult =>
        (simulateQ randomOracle computation).run hashResult.2) := by
  let target := Concrete.CacheView.keyChainInput parameter key chain ⟨steps, hvalid⟩ previous
  have hcached : ∀ result ∈ support ((simulateQ randomOracle computation).run prefixCache),
      ∃ output, result.2 target = some output := by
    intro result hresult
    have hprefixLe := randomOracle_cache_le computation prefixCache result hresult
    have hreplay := eval_answerFn_largerCache_eq_of_mem_support
      (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
        OracleComp HashSpec Digest)
      initialCache prefixCache result.2 previous hprefix hprefixLe
    rw [eval_keyChainWalk] at hreplay
    obtain ⟨output, houtput⟩ :=
      hcovers.input_cached prefixCache result hresult key chain ⟨steps, hvalid⟩
    refine ⟨output, ?_⟩
    change result.2 (Concrete.CacheView.keyChainInput parameter key chain ⟨steps, hvalid⟩
      previous) = some output
    rw [← hreplay]
    exact houtput
  calc
    ((simulateQ randomOracle computation).run prefixCache) =ᵈ
        ((randomOracle (spec := HashSpec) target).run prefixCache >>= fun queryResult =>
          (simulateQ randomOracle computation).run queryResult.2) :=
      OracleComp.evalDist_randomOracle_run_eq_query_then_of_cached computation prefixCache
        target hcached
    _ = _ := by
      simp [Concrete.keyChainHash, Concrete.tweakableHash, Concrete.oracleHash,
        target, Concrete.CacheView.keyChainInput]

theorem evalDist_run_eq_keyChainWalk_then
    (hcovers : CoversKeyChains parameter start computation)
    (key : ChainKey) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (initialCache : QueryCache HashSpec) :
    ((simulateQ randomOracle computation).run initialCache) =ᵈ
      ((simulateQ randomOracle
        (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
          OracleComp HashSpec Digest)).run initialCache >>= fun chainResult =>
        (simulateQ randomOracle computation).run chainResult.2) := by
  induction steps generalizing initialCache with
  | zero => simp [Concrete.keyChainWalk]
  | succ steps ih =>
      have hvalid : steps < chainLength - 1 := by omega
      calc
        _ =ᵈ ((simulateQ randomOracle
              (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
                OracleComp HashSpec Digest)).run initialCache >>= fun prefixResult =>
              (simulateQ randomOracle computation).run prefixResult.2) :=
          ih (by omega) initialCache
        _ =ᵈ ((simulateQ randomOracle
              (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
                OracleComp HashSpec Digest)).run initialCache >>= fun prefixResult =>
              (simulateQ randomOracle
                (Concrete.keyChainHash parameter key chain ⟨steps, hvalid⟩
                  prefixResult.1 : OracleComp HashSpec Digest)).run
                    prefixResult.2 >>= fun hashResult =>
              (simulateQ randomOracle computation).run hashResult.2) := by
          apply OracleComp.EvalDistEq.bind_congr_of_support
          intro prefixResult hprefix
          exact evalDist_run_eq_keyChainHash_then parameter start computation hcovers key chain
            steps prefixResult.1 initialCache prefixResult.2 hvalid hprefix
        _ = _ := by
          rw [Concrete.keyChainWalk, simulateQ_bind, StateT.run_bind]
          simp only [zero_add]
          simp only [hvalid, ↓reduceDIte, bind_assoc]

end Warm

theorem Concrete.chainTrajectory_back_map_eq_keyChainWalk
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest) :
    Vector.back <$> Concrete.chainTrajectory parameter key chain position steps value =
      (Concrete.keyChainWalk parameter key chain position steps value :
        OracleComp HashSpec Digest) := by
  induction steps with
  | zero =>
      rw [Concrete.chainTrajectory_zero]
      simp only [map_pure, Concrete.keyChainWalk]
      simp [Vector.back_ofFn]
  | succ steps ih =>
      calc
        Vector.back <$>
            Concrete.chainTrajectory parameter key chain position (steps + 1) value =
            (Vector.back <$> Concrete.chainTrajectory parameter key chain
              position steps value) >>= fun previous =>
              if hvalid : position + steps < chainLength - 1 then
                Concrete.keyChainHash parameter key chain ⟨position + steps, hvalid⟩ previous
              else pure 0 := by
          rw [Concrete.chainTrajectory_succ]
          by_cases hvalid : position + steps < chainLength - 1
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
          · simp [hvalid, map_eq_bind_pure_comp, bind_assoc]
        _ = Concrete.keyChainWalk parameter key chain position (steps + 1) value := by
          rw [ih]
          rfl

theorem evalDist_chainTrajectory_run_cache_eq_keyChainWalk_run_cache
    (parameter : PublicParameter) (key : ChainKey) (chain : ChainIndex)
    (position steps : Nat) (value : Digest)
    (initialCache : QueryCache HashSpec) :
    ((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
      (result.1.back, result.2)) <$>
        (simulateQ randomOracle
          (Concrete.chainTrajectory parameter key chain position steps value)).run
            initialCache) =ᵈ
      ((simulateQ randomOracle
        (Concrete.keyChainWalk parameter key chain position steps value :
          OracleComp HashSpec Digest)).run initialCache) := by
  rw [← StateT.run_map]
  rw [← simulateQ_map]
  rw [Concrete.chainTrajectory_back_map_eq_keyChainWalk]

theorem evalDist_run_eq_chainTrajectory_then {α : Type} (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (computation : OracleComp HashSpec α)
    (hcovers : CoversKeyChains parameter start computation)
    (key : ChainKey) (chain : ChainIndex) (steps : Nat)
    (hsteps : steps ≤ chainLength - 1) (initialCache : QueryCache HashSpec) :
    ((simulateQ randomOracle computation).run initialCache) =ᵈ
      ((simulateQ randomOracle
        (Concrete.chainTrajectory parameter key chain 0 steps (start key chain))).run
          initialCache >>= fun trajectoryResult =>
        (simulateQ randomOracle computation).run trajectoryResult.2) := by
  calc
    _ =ᵈ ((simulateQ randomOracle
          (Concrete.keyChainWalk parameter key chain 0 steps (start key chain) :
            OracleComp HashSpec Digest)).run initialCache >>= fun chainResult =>
          (simulateQ randomOracle computation).run chainResult.2) :=
      evalDist_run_eq_keyChainWalk_then parameter start computation hcovers key chain steps
        hsteps initialCache
    _ =ᵈ (((fun result : Vector Digest (steps + 1) × QueryCache HashSpec =>
          (result.1.back, result.2)) <$>
            (simulateQ randomOracle
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain))).run initialCache) >>= fun chainResult =>
          (simulateQ randomOracle computation).run chainResult.2) := by
      exact (evalDist_chainTrajectory_run_cache_eq_keyChainWalk_run_cache parameter key chain 0
        steps (start key chain) initialCache).symm.bind_left _
    _ = _ := by
      simp [map_eq_bind_pure_comp, bind_assoc]

noncomputable def Concrete.fixedSeedChainTrajectoriesFromCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    QueryCache HashSpec → List ChainKey →
      ProbComp (List (Vector Digest (steps + 1)) × QueryCache HashSpec)
  | cache, [] => pure ([], cache)
  | cache, key :: keys => do
      let first ← (simulateQ randomOracle
        (Concrete.chainTrajectory parameter key chain 0 steps (start key chain))).run cache
      let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
        parameter start chain steps first.2 keys
      return (first.1 :: rest.1, rest.2)

@[simp]
theorem Concrete.fixedSeedChainTrajectoriesFromCache_nil
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain steps
      cache [] = pure ([], cache) := rfl

theorem Concrete.fixedSeedChainTrajectoriesFromCache_cons
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) (cache : QueryCache HashSpec)
    (key : ChainKey) (keys : List ChainKey) :
    Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain steps
      cache (key :: keys) = (do
        let first ← (simulateQ randomOracle
          (Concrete.chainTrajectory parameter key chain 0 steps (start key chain))).run cache
        let rest ← Concrete.fixedSeedChainTrajectoriesFromCache
          parameter start chain steps first.2 keys
        return (first.1 :: rest.1, rest.2)) := rfl

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (keys : List ChainKey) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain
          steps cache keys) →
      cache ≤ result.2 ∧ result.1.length = keys.length ∧
        List.Forall₂
          (fun key trajectory =>
            evalWithAnswerFn (Concrete.CacheReplay.answerFn result.2)
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain)) = trajectory)
          keys result.1 := by
  intro keys
  induction keys with
  | nil =>
      intro cache result hresult
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, rfl, List.Forall₂.nil⟩
  | cons key keys ih =>
      intro cache result hresult
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      obtain ⟨hfirstCacheLe, hlength, hpairs⟩ := ih first.2 rest hrest
      constructor
      · exact (Concrete.CacheReplay.randomOracle_cache_le
          (Concrete.chainTrajectory parameter key chain 0 steps
            (start key chain)) cache first hfirst).trans hfirstCacheLe
      · constructor
        · simp [hlength]
        · apply List.Forall₂.cons
          · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain)) cache first.2 rest.2 first.1 hfirst hfirstCacheLe
          · exact hpairs

set_option maxRecDepth 100000 in
set_option linter.constructorNameAsVariable false in
theorem Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (steps : Nat) :
    ∀ (keys : List ChainKey) (cache : QueryCache HashSpec)
      (result : List (Vector Digest (steps + 1)) × QueryCache HashSpec)
      (largerCache : QueryCache HashSpec),
      result ∈ support
        (Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain
          steps cache keys) →
      result.2 ≤ largerCache →
      List.Forall₂
        (fun key trajectory =>
          evalWithAnswerFn (Concrete.CacheReplay.answerFn largerCache)
            (Concrete.chainTrajectory parameter key chain 0 steps
              (start key chain)) = trajectory)
        keys result.1 := by
  intro keys
  induction keys with
  | nil =>
      intro cache result largerCache hresult _hle
      simp only [Concrete.fixedSeedChainTrajectoriesFromCache_nil,
        support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact List.Forall₂.nil
  | cons key keys ih =>
      intro cache result largerCache hresult hlarger
      rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons,
        mem_support_bind_iff] at hresult
      obtain ⟨first, hfirst, hrest⟩ := hresult
      rw [mem_support_bind_iff] at hrest
      obtain ⟨rest, hrest, hpure⟩ := hrest
      simp only [support_pure, Set.mem_singleton_iff] at hpure
      subst result
      have hrestInfo :=
        Concrete.fixedSeedChainTrajectoriesFromCache_support_info parameter
          start chain steps keys first.2 rest hrest
      apply List.Forall₂.cons
      · exact Concrete.CacheReplay.eval_answerFn_largerCache_eq_of_mem_support
          (Concrete.chainTrajectory parameter key chain 0 steps
            (start key chain)) cache first.2 largerCache first.1 hfirst
            (hrestInfo.1.trans hlarger)
      · exact ih first.2 rest largerCache hrest hlarger

theorem Concrete.fixedSeedChainTrajectoriesFromCache_table_eq_in_largerCache
    (parameter : PublicParameter) (start : ChainKey → ChainIndex → Digest)
    (chain : ChainIndex) (initialCache : QueryCache HashSpec)
    (result : List FullChainTrajectory × QueryCache HashSpec)
    (largerCache : QueryCache HashSpec)
    (hresult : result ∈ support
      (Concrete.fixedSeedChainTrajectoriesFromCache parameter start chain
        (chainLength - 1) initialCache allChainKeys))
    (hle : result.2 ≤ largerCache)
    (secretKey : SecretKey) (hparameter : secretKey.parameter = parameter)
    (hstart : secretKey.keyChainStart = start) :
    chainValueTableOfList result.1 = keygenChainValueTable largerCache secretKey chain := by
  have hinfo := Concrete.fixedSeedChainTrajectoriesFromCache_support_info
    parameter start chain (chainLength - 1) allChainKeys initialCache result hresult
  have hpairs :=
    Concrete.fixedSeedChainTrajectoriesFromCache_replay_in_largerCache
      parameter start chain (chainLength - 1) allChainKeys initialCache result largerCache
      hresult hle
  funext index
  unfold chainValueTableOfList
  split
  · rename_i htableLength
    let position := chainKeyPosition index.1
    have hresultPosition : position.val < result.1.length := by
      rw [← htableLength]
      exact position.isLt
    have hpair := hpairs.get position.isLt hresultPosition
    have hkey : allChainKeys.get position = index.1 := by
      exact allChainKeys_get_chainKeyPosition index.1
    rw [hkey] at hpair
    have hvalue := congrArg
      (fun trajectory : FullChainTrajectory =>
        trajectory[index.2.val]'(by
          have hdigit := index.2.isLt
          omega)) hpair
    rw [Concrete.chainTrajectory_getElem] at hvalue
    rw [keygenChainValueTable, hparameter, hstart]
    exact hvalue.symm
  · rename_i htableLength
    exact (htableLength hinfo.2.1.symm).elim

theorem evalDist_run_eq_fixedSeedTrajectories_then {α : Type} (parameter : PublicParameter)
    (start : ChainKey → ChainIndex → Digest) (computation : OracleComp HashSpec α)
    (hcovers : CoversKeyChains parameter start computation)
    (chain : ChainIndex) (steps : Nat) (hsteps : steps ≤ chainLength - 1)
    (keys : List ChainKey) (initialCache : QueryCache HashSpec) :
    ((simulateQ randomOracle computation).run initialCache) =ᵈ
      (Concrete.fixedSeedChainTrajectoriesFromCache
        parameter start chain steps initialCache keys >>= fun trajectoryResult =>
        (simulateQ randomOracle computation).run trajectoryResult.2) := by
  induction keys generalizing initialCache with
  | nil => simp
  | cons key keys ih =>
      calc
        _ =ᵈ ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain))).run initialCache >>= fun first =>
              (simulateQ randomOracle computation).run first.2) :=
          evalDist_run_eq_chainTrajectory_then parameter start computation hcovers key chain
            steps hsteps initialCache
        _ =ᵈ ((simulateQ randomOracle
              (Concrete.chainTrajectory parameter key chain 0 steps
                (start key chain))).run initialCache >>= fun first =>
              Concrete.fixedSeedChainTrajectoriesFromCache
                parameter start chain steps first.2 keys >>= fun rest =>
              (simulateQ randomOracle computation).run rest.2) := by
          apply EvalDistEq.bind_right
          intro first
          exact ih first.2
        _ = _ := by
          rw [Concrete.fixedSeedChainTrajectoriesFromCache_cons]
          simp only [bind_assoc, pure_bind]

end XmssSecurity

namespace XmssSecurity

theorem Concrete.simulateQ_keyChainHash_run (parameter : PublicParameter) (key : ChainKey)
    (chain : ChainIndex) (step : ChainStep) (value : Digest) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle
      (Concrete.keyChainHash parameter key chain step value : OracleComp HashSpec Digest)).run cache =
      (fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.keyChainInput parameter key chain step value)).run cache := by
  simp only [Concrete.keyChainHash, Concrete.tweakableHash, Concrete.oracleHash,
    HasQuery.instOfMonadLift_query, bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_spec_query]
  rfl

theorem Concrete.simulateQ_encodingHash_run (parameter : PublicParameter) (leafIndex : LeafIndex)
    (message : Message) (randomness : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ randomOracle
      (Concrete.encodingHash parameter leafIndex message randomness :
        OracleComp HashSpec Digest)).run cache =
      (fun result : HashOutput × QueryCache HashSpec => (truncateHash result.1, result.2)) <$>
        (randomOracle (Concrete.CacheView.encodingInput parameter leafIndex
          (message, randomness))).run cache := by
  simp only [Concrete.encodingHash, Concrete.tweakableHash, Concrete.oracleHash,
    HasQuery.instOfMonadLift_query, bind_pure_comp, simulateQ_map, StateT.run_map, simulateQ_spec_query]
  rfl

end XmssSecurity
