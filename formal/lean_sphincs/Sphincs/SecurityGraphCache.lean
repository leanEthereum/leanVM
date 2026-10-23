import Sphincs.SecurityGraph
import Sphincs.SecuritySeedCoupling

/-! The structural reference table of a canonical graph: active positions exempt their canonical
input, and omitted positions carry their surrogate targets. Programmed seed material leaves every
structural address free, and every final entry of a lazy random-oracle cache either existed
initially or was queried in the run. -/

open OracleComp OracleSpec ENNReal

namespace Sphincs.Security.Graph

open Concrete Completeness TargetAssignment
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 512
set_option maxHeartbeats 400000
attribute [local irreducible] canonicalGraphInput canonicalGraphSlots

noncomputable def positionAt (fields : TweakFields) : Option Position :=
  @dite (Option Position) (∃ position : Position, hashDomainFields position.domain = fields)
    (Classical.propDecidable _) (fun h => some h.choose) (fun _ => none)

theorem positionAt_some_iff (fields : TweakFields) (position : Position) :
    positionAt fields = some position ↔ hashDomainFields position.domain = fields := by
  rw [positionAt]
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hp; exact Position.fields_injective (h.choose_spec.trans hp.symm)
  · rename_i h
    constructor
    · intro heq; cases heq
    · intro hp; exact False.elim (h ⟨position, hp⟩)

attribute [local irreducible] positionAt

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : ForestSecrets)

/-- Active nodes have their canonical input exempted. Boundary nodes have no such input. -/
noncomputable def referenceTable (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) : Table := fun fields =>
  match positionAt fields with
  | none => none
  | some position =>
      if active position then
        some ⟨some (canonicalGraphInput parameter otsSecret ftsSecret position labels),
          truncateHash (labels position)⟩
      else (boundary position).map fun value => ⟨none, value⟩

theorem referenceTable_active (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (position : Position) (hactive : active position) :
    referenceTable parameter otsSecret ftsSecret active boundary labels
      (hashDomainFields position.domain) =
        some ⟨some (canonicalGraphInput parameter otsSecret ftsSecret position labels),
          truncateHash (labels position)⟩ := by
  unfold referenceTable
  rw [(positionAt_some_iff _ position).2 rfl]
  exact ite_eq_left hactive

theorem referenceTable_boundary (active : Position → Prop) (boundary : Position → Option Digest)
    (labels : CanonicalGraphLabels) (position : Position) (hactive : ¬active position)
    (value : Digest) (hboundary : boundary position = some value) :
    referenceTable parameter otsSecret ftsSecret active boundary labels
      (hashDomainFields position.domain) = some ⟨none, value⟩ := by
  unfold referenceTable
  rw [(positionAt_some_iff _ position).2 rfl]
  simp only [ite_eq_right hactive, hboundary, Option.map_some]

/-- Preparation starts with no structural addresses populated; seed material satisfies this
because its serialized domain tags are disjoint. -/
def FreshStructural (cache : QueryCache HashSpec) : Prop :=
  ∀ (position : Position) (payload : HashInput),
    cache (tweakableHashInput parameter position.domain payload) = none

omit parameter otsSecret ftsSecret in
theorem query_cache_origin (queried input : HashInput) (cache : QueryCache HashSpec)
    (answer : HashOutput) (cache' : QueryCache HashSpec)
    (hmem : (answer, cache') ∈ support ((randomOracle (spec := HashSpec) queried).run cache))
    (value : HashOutput) (hentry : cache' input = some value) :
    cache input = some value ∨ input = queried := by
  cases hc : cache queried with
  | some old =>
      rw [QueryImpl.withCaching_run_some uniformSampleImpl hc, support_pure,
        Set.mem_singleton_iff] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact Or.inl hentry
  | none =>
      rw [QueryImpl.withCaching_run_none uniformSampleImpl hc, support_map] at hmem
      obtain ⟨sample, _, heq⟩ := hmem
      obtain ⟨rfl, rfl⟩ := heq
      by_cases hi : input = queried
      · exact Or.inr hi
      · exact Or.inl (by rwa [QueryCache.cacheQuery_of_ne _ _ hi] at hentry)

omit parameter otsSecret ftsSecret in
/-- Every final cache entry either existed initially or occurs in this supported run's trace. -/
theorem hash_cache_origin {α : Type} (oa : OracleComp HashSpec α)
    (cache : QueryCache HashSpec) (result : α) (cache' : QueryCache HashSpec)
    (hmem : (result, cache') ∈ support ((simulateQ randomOracle oa).run cache))
    (f : QueryImpl HashSpec Id) (hf : cache'.AgreesWithFn f)
    (input : HashInput) (value : HashOutput) (hentry : cache' input = some value) :
    cache input = some value ∨ input ∈ queriedInputs f oa := by
  induction oa using OracleComp.inductionOn generalizing cache result cache' with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact Or.inl hentry
  | query_bind queried next ih =>
      simp only [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨answer, mid⟩, hquery, hnext⟩ := hmem
      obtain ⟨_, hcached⟩ := query_support_cached queried cache answer mid hquery
      have hle := hash_support_cache_le _ mid result cache' hnext
      have hanswer : f queried = answer := hf (hle hcached)
      rw [queriedInputs_query_bind, hanswer]
      rcases ih answer mid result cache' hnext hf hentry with hold | htrace
      · rcases query_cache_origin queried input cache answer mid hquery value hold with hold | rfl
        · exact Or.inl hold
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ htrace)

/-- All programmed seed material is disjoint from structural graph addresses. -/
theorem material_freshStructural (seed : MasterSeed) (material : SeedModel.Material) :
    FreshStructural parameter (SeedModel.programCache ∅ seed material) := by
  intro position payload
  exact SeedModel.programCache_verifier ∅ seed material parameter position.domain payload

end Sphincs.Security.Graph
