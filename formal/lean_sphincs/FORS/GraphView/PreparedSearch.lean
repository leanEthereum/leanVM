module

public import FORS.GraphView.HonestSigner
public import FORS.LazyRun.PreparedEncodings
public import FORS.LazyRun.Replay

@[expose] public section

section

/-! The preparation's cache covers every key's counter search (`searchCached_preparation`): a
lazily sampled search caches each trial it makes and goes on only past a trial that encodes
nothing, and the later searches only grow the cache. With it the honest signer's searches read
only prepared trials (`HonestSigner.SignerReadsGood.searched`). -/

open OracleComp OracleSpec

namespace FORS.Security.GraphView

variable [Params]
open Concrete Completeness Prefix HiddenGraph HiddenDebt HiddenBridge
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] encodingAttemptLimit

/-- A lazily sampled query caches its answer. -/
theorem randomOracle_query_cached (input : HashInput) (cache0 : QueryCache HashSpec)
    (first : HashOutput × QueryCache HashSpec)
    (hfirst : first ∈ support ((simulateQ randomOracle (liftM (HashSpec.query input) :
      OracleComp HashSpec HashOutput)).run cache0)) :
    first.2 input = some first.1 := by
  rw [simulateQ_spec_query] at hfirst
  change first ∈ support ((randomOracle (spec := HashSpec) input).run cache0) at hfirst
  cases hc : cache0 input with
  | some u =>
      rw [QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hfirst
      subst hfirst
      exact hc
  | none =>
      rw [QueryImpl.withCaching_run_none _ hc, support_map] at hfirst
      obtain ⟨u, _, rfl⟩ := hfirst
      exact QueryCache.cacheQuery_self _ _ _

/-- A search's trials from `start` are cached in `cache`, the search going on past a trial whose
answer does not stop it. -/
def TrialsCached (cache : QueryCache HashSpec) (trial : ℕ → HashInput) (stop : HashOutput → Prop) :
    ℕ → ℕ → Prop
  | 0, _ => True
  | attempts + 1, start => ∃ output, cache (trial start) = some output ∧
      (¬stop output → TrialsCached cache trial stop attempts (start + 1))

/-- **A lazily sampled search caches what it searched**, for any search that queries its trial and
then either stops or goes on with the next trial. -/
theorem trialsCached_run {γ : Type} (trial : ℕ → HashInput) (stop : HashOutput → Prop)
    (search : ℕ → ℕ → OracleComp HashSpec γ) (next : ℕ → ℕ → HashOutput → OracleComp HashSpec γ)
    (hstep : ∀ attempts start, search (attempts + 1) start =
      liftM (HashSpec.query (trial start)) >>= next attempts start)
    (hgo : ∀ attempts start output, ¬stop output → next attempts start output = search attempts (start + 1))
    (hstop : ∀ attempts start output, stop output → ∃ value, next attempts start output = pure value) :
    ∀ (attempts start : ℕ) (cache0 : QueryCache HashSpec),
      ∀ result ∈ support ((simulateQ randomOracle (search attempts start)).run cache0),
        TrialsCached result.2 trial stop attempts start
  | 0, _, _, _, _ => trivial
  | attempts + 1, start, cache0, result, hresult => by
      rw [hstep, simulateQ_bind, StateT.run_bind, support_bind] at hresult
      obtain ⟨first, hfirst, hrest⟩ := Set.mem_iUnion₂.1 hresult
      have hcached := randomOracle_query_cached _ cache0 first hfirst
      refine ⟨first.1, ?_, fun hgoing => ?_⟩
      · by_cases hs : stop first.1
        · obtain ⟨value, hv⟩ := hstop attempts start first.1 hs
          rw [hv, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrest
          rw [hrest]
          exact hcached
        · rw [hgo attempts start first.1 hs] at hrest
          exact randomOracle_run_grows _ first.2 result hrest _ _ hcached
      · rw [hgo attempts start first.1 hgoing] at hrest
        exact trialsCached_run trial stop search next hstep hgo hstop attempts (start + 1) first.2 result hrest

theorem searchCached_of_trialsCached (cache : QueryCache HashSpec) (parameter : PublicParameter) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) :
    ∀ attempts start, TrialsCached cache (trialInput parameter lay tree leaf message)
        (fun output => TargetSum.decodeDigest (truncateHash output) ≠ none) attempts start →
      SearchCached cache parameter lay tree leaf message attempts start
  | 0, _, _ => trivial
  | attempts + 1, start, ⟨output, hout, hnext⟩ =>
      ⟨output, hout, fun hnone => searchCached_of_trialsCached cache parameter lay tree leaf message attempts
        (start + 1) (hnext fun h => h hnone)⟩

/-- The counter search's step: its trial, then the decoding's verdict. -/
theorem search_step (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (attempts start : ℕ) :
    ReferenceChoice.search parameter lay tree leaf message (attempts + 1) start =
      liftM (HashSpec.query (trialInput parameter lay tree leaf message start)) >>= fun output =>
        match TargetSum.decodeDigest (truncateHash output) with
        | none => ReferenceChoice.search parameter lay tree leaf message attempts (start + 1)
        | some encoding => pure (some (BitVec.ofNat counterBits start, encoding)) := by
  rw [ReferenceChoice.search, encode, tweakableHash, bind_assoc, bind_assoc]
  have hq : (oracleHash (tweakableHashInput parameter (.encoding lay tree leaf)
      (message ++ bytesBE 4 (BitVec.ofNat counterBits start))) : OracleComp HashSpec HashOutput) =
      liftM (HashSpec.query (trialInput parameter lay tree leaf message start)) := rfl
  rw [hq]
  refine congrArg (liftM (HashSpec.query (trialInput parameter lay tree leaf message start)) >>= ·)
    (funext fun output => ?_)
  rw [pure_bind, pure_bind]
  cases TargetSum.decodeDigest (truncateHash output) <;> rfl

/-- **A lazily sampled counter search caches what it searched.** -/
theorem searchCached_run (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : HashInput) (attempts start : ℕ) (cache0 : QueryCache HashSpec) :
    ∀ result ∈ support ((simulateQ randomOracle
      (ReferenceChoice.search parameter lay tree leaf message attempts start)).run cache0),
      SearchCached result.2 parameter lay tree leaf message attempts start :=
  fun result hresult => searchCached_of_trialsCached _ _ _ _ _ _ _ _
    (trialsCached_run (trialInput parameter lay tree leaf message)
      (fun output => TargetSum.decodeDigest (truncateHash output) ≠ none)
      (ReferenceChoice.search parameter lay tree leaf message)
      (fun attempts start output => match TargetSum.decodeDigest (truncateHash output) with
        | none => ReferenceChoice.search parameter lay tree leaf message attempts (start + 1)
        | some encoding => pure (some (BitVec.ofNat counterBits start, encoding)))
      (search_step parameter lay tree leaf message)
      (fun attempts start output hgo => by
        rw [show TargetSum.decodeDigest (truncateHash output) = none from not_not.mp hgo])
      (fun attempts start output hs => by
        obtain ⟨encoding, he⟩ := Option.ne_none_iff_exists'.mp hs
        exact ⟨_, by rw [he]⟩)
      attempts start cache0 result hresult)

/-- In a lazily sampled sequence, every computation ran from a cache the final one extends. -/
theorem sequenceFin_run_parts {α : Type} :
    ∀ {n : ℕ} (computation : Fin n → OracleComp HashSpec α) (cache0 : QueryCache HashSpec),
      ∀ result ∈ support ((simulateQ randomOracle (sequenceFin computation)).run cache0), ∀ i,
        ∃ cache, ∃ part ∈ support ((simulateQ randomOracle (computation i)).run cache),
          ∀ input output, part.2 input = some output → result.2 input = some output
  | 0, _, _, _, _, i => i.elim0
  | n + 1, computation, cache0, result, hresult, i => by
      rw [sequenceFin, simulateQ_bind, StateT.run_bind, support_bind] at hresult
      obtain ⟨head, hhead, hresult⟩ := Set.mem_iUnion₂.1 hresult
      rw [simulateQ_bind, StateT.run_bind, support_bind] at hresult
      obtain ⟨tail, htail, hresult⟩ := Set.mem_iUnion₂.1 hresult
      rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst hresult
      cases i using Fin.cases with
      | zero => exact ⟨cache0, head, hhead, fun input output h => randomOracle_run_grows _ head.2 tail htail _ _ h⟩
      | succ j => exact sequenceFin_run_parts (fun index : Fin n => computation index.succ) head.2 tail htail j

/-- **The preparation's searches are cached**: from any cache, after every key's counter search on
`message`, each key's search is cached. -/
theorem searchCached_searchAll (parameter : PublicParameter) (message : OtsKey → HashInput)
    (base : QueryCache HashSpec) :
    ∀ result ∈ support ((simulateQ randomOracle (searchAll parameter message)).run base),
      ∀ lay tree leaf, SearchCached result.2 parameter lay tree leaf (message (lay, tree, leaf))
        encodingAttemptLimit 0 := by
  intro result hresult lay tree leaf
  rw [searchAll, simulateQ_bind, StateT.run_bind, support_bind] at hresult
  obtain ⟨found, hfound, hresult⟩ := Set.mem_iUnion₂.1 hresult
  rw [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst hresult
  obtain ⟨cache1, part1, hpart1, hext1⟩ := sequenceFin_run_parts _ base found hfound lay
  obtain ⟨cache2, part2, hpart2, hext2⟩ := sequenceFin_run_parts _ cache1 part1 hpart1 tree
  obtain ⟨cache3, part3, hpart3, hext3⟩ := sequenceFin_run_parts _ cache2 part2 hpart2 leaf
  exact searchCached_mono (fun input output h => hext1 _ _ (hext2 _ _ (hext3 _ _ h))) _ _ _ _ _ _ _
    (searchCached_run parameter lay tree leaf _ encodingAttemptLimit 0 cache3 part3 hpart3)

section Game

open SeedModel Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Every key's counter search is cached in the preparation.** -/
theorem searchCached_preparation (parameterOutput : HashOutput) (fixed : HiddenGraph.Table)
    (highs : CoordinateHighs) (remaining : RemainingOutputs) :
    ∀ prepared ∈ support (preparation parameterOutput fixed highs remaining), ∀ lay tree leaf,
      SearchCached prepared.2 (truncateHash parameterOutput) lay tree leaf
        ((sampleData parameterOutput fixed highs remaining).keyMessage lay tree leaf) encodingAttemptLimit 0 :=
  fun prepared hprepared lay tree leaf =>
    searchCached_searchAll _ _ _ prepared hprepared lay tree leaf

end Game

end FORS.Security.GraphView

end
