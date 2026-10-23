import Sphincs.SecurityGraphCache
import SphincsBase.Proof.Hypertree.FiniteGraphReplay

/-! Actual lazy-oracle graph preparation equals independent full-output labels followed by
canonical cache programming. Pruned positions keep their initial boundary labels. -/

open OracleComp OracleSpec

namespace Sphincs.Security.Graph
open Concrete Completeness

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
attribute [local irreducible] canonicalGraphInput canonicalGraphSlots

noncomputable opaque graphLabelsSampleable : SampleableType CanonicalGraphLabels :=
  SampleableType.ofFintype CanonicalGraphLabels
noncomputable local instance : SampleableType CanonicalGraphLabels := graphLabelsSampleable

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : ForestSecrets)

def FreshPositions (positions : List Position) (cache : QueryCache HashSpec) : Prop :=
  ∀ position ∈ positions, ∀ labels,
    cache (canonicalGraphInput parameter otsSecret ftsSecret position labels) = none

theorem freshPositions_of_structural (positions : List Position) (cache : QueryCache HashSpec)
    (hfresh : FreshStructural parameter cache) :
    FreshPositions parameter otsSecret ftsSecret positions cache := by
  intro position _ labels
  rw [canonicalGraphInput]
  exact hfresh position _

theorem freshPositions_tail (position : Position) (rest : List Position)
    (hnodup : (position :: rest).Nodup) (cache : QueryCache HashSpec)
    (hfresh : FreshPositions parameter otsSecret ftsSecret (position :: rest) cache)
    (labels : CanonicalGraphLabels) (output : HashOutput) :
    FreshPositions parameter otsSecret ftsSecret rest
      (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels) output) := by
  intro next hnext values
  rw [QueryCache.cacheQuery_of_ne]
  · exact hfresh next (List.mem_cons_of_mem _ hnext) values
  · apply canonicalGraphInput_separated
    intro heq
    subst next
    exact (List.nodup_cons.mp hnodup).1 hnext

noncomputable def samplePrepare : List Position → CanonicalGraphLabels → QueryCache HashSpec →
    ProbComp (CanonicalGraphLabels × QueryCache HashSpec)
  | [], labels, cache => pure (labels, cache)
  | position :: rest, labels, cache => do
      let output ← $ᵗ HashOutput
      samplePrepare rest (Function.update labels position output)
        (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels) output)

theorem run_prepare_eq_sample (positions : List Position) (hnodup : positions.Nodup)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (hfresh : FreshPositions parameter otsSecret ftsSecret positions cache) :
    (simulateQ randomOracle (prepare parameter otsSecret ftsSecret positions labels)).run cache =
      samplePrepare parameter otsSecret ftsSecret positions labels cache := by
  induction positions generalizing labels cache with
  | nil => rfl
  | cons position rest ih =>
      simp only [prepare, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      rw [QueryImpl.withCaching_run_none _ (hfresh position List.mem_cons_self labels)]
      simp only [bind_map_left, samplePrepare]
      change (($ᵗ HashOutput) >>= _) = (($ᵗ HashOutput) >>= _)
      apply bind_congr
      intro output
      exact ih (List.nodup_cons.mp hnodup).2 _ _
        (freshPositions_tail parameter otsSecret ftsSecret position rest hnodup cache hfresh labels output)

def replayPrepare (answers : CanonicalGraphLabels) : List Position → CanonicalGraphLabels →
    QueryCache HashSpec → CanonicalGraphLabels × QueryCache HashSpec
  | [], labels, cache => (labels, cache)
  | position :: rest, labels, cache =>
      replayPrepare answers rest (Function.update labels position (answers position))
        (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels) (answers position))

theorem replayPrepare_congr (left right : CanonicalGraphLabels) (positions : List Position)
    (hagrees : ∀ position ∈ positions, left position = right position)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec) :
    replayPrepare parameter otsSecret ftsSecret left positions labels cache =
      replayPrepare parameter otsSecret ftsSecret right positions labels cache := by
  induction positions generalizing labels cache with
  | nil => rfl
  | cons position rest ih =>
      simp only [replayPrepare, hagrees position List.mem_cons_self]
      exact ih (fun p hp => hagrees p (List.mem_cons_of_mem _ hp)) _ _

theorem replayPrepare_update (answers : CanonicalGraphLabels) (positions : List Position)
    (position : Position) (hposition : position ∉ positions) (output : HashOutput)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec) :
    replayPrepare parameter otsSecret ftsSecret (Function.update answers position output) positions labels cache =
      replayPrepare parameter otsSecret ftsSecret answers positions labels cache := by
  apply replayPrepare_congr
  intro other hother
  apply Function.update_of_ne
  intro heq
  subst other
  exact hposition hother

/-- The selected rows are independent uniform full hash outputs; no independence condition on
the secret-derived canonical input strings is assumed. Their exact separation suffices. -/
theorem evalDist_samplePrepare_eq_uniform (positions : List Position) (hnodup : positions.Nodup)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec) :
    samplePrepare parameter otsSecret ftsSecret positions labels cache =ᵈ ((fun answers => replayPrepare parameter otsSecret ftsSecret answers positions labels cache) <$>
        ($ᵗ CanonicalGraphLabels)) := by
  induction positions generalizing labels cache with
  | nil =>
      simp only [samplePrepare, replayPrepare, map_eq_bind_pure_comp]
      exact (OracleComp.EvalDistEq.bind_const ($ᵗ CanonicalGraphLabels) (pure (labels, cache))).symm
  | cons position rest ih =>
      obtain ⟨hposition, hrest⟩ := List.nodup_cons.mp hnodup
      have hextract := SphincsBase.Concrete.FiniteGraphSampling.evalDist_table_extract position
        (fun answers output => pure (replayPrepare parameter otsSecret ftsSecret answers rest
          (Function.update labels position output)
          (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels) output)))
      rw [map_eq_bind_pure_comp]
      change samplePrepare parameter otsSecret ftsSecret (position :: rest) labels cache =ᵈ (do
          let answers ← $ᵗ CanonicalGraphLabels
          pure (replayPrepare parameter otsSecret ftsSecret answers rest
            (Function.update labels position (answers position))
            (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels) (answers position))))
      refine EvalDistEq.trans ?_ hextract.symm
      simp_rw [replayPrepare_update parameter otsSecret ftsSecret _ rest position hposition]
      rw [samplePrepare]
      refine EvalDistEq.bind_right _ fun output => ?_
      exact (ih hrest _ _).trans (by rw [map_eq_bind_pure_comp]; exact EvalDistEq.rfl)

theorem evalDist_prepare_uniform (positions : List Position) (hnodup : positions.Nodup)
    (labels : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (hfresh : FreshPositions parameter otsSecret ftsSecret positions cache) :
    ((simulateQ randomOracle (prepare parameter otsSecret ftsSecret positions labels)).run cache) =ᵈ ((fun answers => replayPrepare parameter otsSecret ftsSecret answers positions labels cache) <$>
        ($ᵗ CanonicalGraphLabels)) := by
  rw [run_prepare_eq_sample parameter otsSecret ftsSecret positions hnodup labels cache hfresh]
  exact evalDist_samplePrepare_eq_uniform parameter otsSecret ftsSecret positions hnodup labels cache

omit parameter otsSecret ftsSecret in
def completedLabels (positions : List Position) (initial answers : CanonicalGraphLabels) :
    CanonicalGraphLabels := fun position => if position ∈ positions then answers position else initial position

def programGraphCache (positions : List Position) (labels : CanonicalGraphLabels)
    (cache : QueryCache HashSpec) : QueryCache HashSpec :=
  positions.foldl (fun current position =>
    current.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels)
      (labels position)) cache

theorem replayPrepare_eq_program (answers target : CanonicalGraphLabels) (positions : List Position)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (before : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (hbefore : ∀ position, position ∉ positions → before position = target position)
    (hanswers : ∀ position ∈ positions, answers position = target position) :
    replayPrepare parameter otsSecret ftsSecret answers positions before cache =
      (target, programGraphCache parameter otsSecret ftsSecret positions target cache) := by
  induction positions generalizing before cache with
  | nil =>
      have heq : before = target := funext fun position => hbefore position (by simp)
      rw [heq]
      rfl
  | cons first rest ih =>
      obtain ⟨hdepth, hsorted⟩ := List.pairwise_cons.mp hsorted
      have hinput : canonicalGraphInput parameter otsSecret ftsSecret first before =
          canonicalGraphInput parameter otsSecret ftsSecret first target := by
        apply canonicalGraphInput_congr
        intro child hchild
        apply congrArg truncateHash
        apply hbefore
        intro hmem
        have hlt := Position.depth_lt_of_mem_children hchild
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst child; omega
        · have := hdepth child hmem; omega
      have hafter : ∀ position, position ∉ rest →
          Function.update before first (target first) position = target position := by
        intro position hposition
        by_cases heq : position = first
        · subst position; exact Function.update_self _ _ _
        · rw [Function.update_of_ne heq]
          exact hbefore position (fun hmem => (List.mem_cons.mp hmem).elim heq hposition)
      rw [replayPrepare, hanswers first List.mem_cons_self, hinput]
      exact ih hsorted _ _ hafter (fun position hposition =>
        hanswers position (List.mem_cons_of_mem _ hposition))

/-- All canonical addresses can be computed from the final independent labels. Inactive
positions keep their initial values, so no random-oracle value replaces a pruned surrogate. -/
theorem evalDist_prepare_programmed (positions : List Position) (hnodup : positions.Nodup)
    (hsorted : positions.Pairwise (fun left right => left.depth ≤ right.depth))
    (initial : CanonicalGraphLabels) (cache : QueryCache HashSpec)
    (hfresh : FreshPositions parameter otsSecret ftsSecret positions cache) :
    ((simulateQ randomOracle (prepare parameter otsSecret ftsSecret positions initial)).run cache) =ᵈ ((fun answers =>
        let labels := completedLabels positions initial answers
        (labels, programGraphCache parameter otsSecret ftsSecret positions labels cache)) <$>
        ($ᵗ CanonicalGraphLabels)) := by
  refine (evalDist_prepare_uniform parameter otsSecret ftsSecret positions hnodup initial cache hfresh).trans ?_
  have hfun : (fun answers => replayPrepare parameter otsSecret ftsSecret answers positions initial cache) =
      (fun answers =>
        let labels := completedLabels positions initial answers
        (labels, programGraphCache parameter otsSecret ftsSecret positions labels cache)) := by
    funext answers
    exact replayPrepare_eq_program parameter otsSecret ftsSecret answers
      (completedLabels positions initial answers) positions hsorted initial cache
      (fun position hposition => by simp only [completedLabels, ite_eq_right hposition])
      (fun position hposition => by simp only [completedLabels, ite_eq_left hposition])
  rw [hfun]

theorem evalDist_activeGraph_programmed (active : Position → Prop) (initial : CanonicalGraphLabels)
    (cache : QueryCache HashSpec) (hfresh : FreshStructural parameter cache) :
    ((simulateQ randomOracle
      (prepare parameter otsSecret ftsSecret (graphOrder active) initial)).run cache) =ᵈ ((fun answers =>
        let labels := completedLabels (graphOrder active) initial answers
        (labels, programGraphCache parameter otsSecret ftsSecret (graphOrder active) labels cache)) <$>
        ($ᵗ CanonicalGraphLabels)) :=
  evalDist_prepare_programmed parameter otsSecret ftsSecret (graphOrder active)
    (graphOrder_nodup active) (graphOrder_sorted active) initial cache
    (freshPositions_of_structural parameter otsSecret ftsSecret _ cache hfresh)

/-- Eager independent graph programming preserves every actual-world continuation. Query
counts already included in the output remain unchanged; preparation itself is unobserved. -/
theorem evalDist_graph_continuation {α : Type} (program : OracleComp OracleWorld α)
    (active : Position → Prop) (initial : CanonicalGraphLabels)
    (cache : QueryCache HashSpec) (hfresh : FreshStructural parameter cache) :
    ((simulateQ romImpl program).run' cache) =ᵈ (do
        let answers ← $ᵗ CanonicalGraphLabels
        let labels := completedLabels (graphOrder active) initial answers
        (simulateQ romImpl program).run'
          (programGraphCache parameter otsSecret ftsSecret (graphOrder active) labels cache)) := by
  refine (SeedCoupling.evalDist_presample_computation program
    (liftM (prepare parameter otsSecret ftsSecret (graphOrder active) initial) :
      OracleComp OracleWorld CanonicalGraphLabels) cache).trans ?_
  rw [simulate_lift_hash]
  refine ((evalDist_activeGraph_programmed parameter otsSecret ftsSecret active initial cache
    hfresh).bind_left _).trans ?_
  rw [bind_map_left]

end Sphincs.Security.Graph
