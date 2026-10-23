import SphincsFors.SecurityHiddenGraph
import SphincsFors.SecurityGraphSampling

/-! Exact connection between the graph preparation table and the candidate hidden-row
oracle. Secret coordinates come from the material tables; all other coordinates and the
adversary-visible high halves come from the independently prepared full hash labels. -/

open OracleComp OracleSpec
namespace SphincsFors.Security.HiddenGraph
open Graph
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

def coordinates
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (labels : CanonicalGraphLabels) : Table
  | .chain lay tree leaf chainIdx position =>
      if h : position.val = 0 then otsSecret lay tree leaf chainIdx
      else truncateHash (labels (.chain lay tree leaf chainIdx
        ⟨position.val - 1, by have := position.isLt; simp only [chainLength, winternitzBits] at *; omega⟩))
  | .ftsSecret index tree leaf => ftsSecret index tree leaf
  | .ftsValue index tree leaf => truncateHash (labels (.ftsLeaf index tree leaf))

def highHalves (labels : CanonicalGraphLabels) (address : Address) : Prefix.High :=
  (splitHashOutput digestBits (labels address.position)).2

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
  (labels : CanonicalGraphLabels)

theorem coordinates_outgoing (address : Address) :
    coordinates otsSecret ftsSecret labels address.outputCoordinate =
      truncateHash (labels address.position) := by
  cases address with
  | chain lay tree leaf chainIdx step =>
      fin_cases step <;> rfl
  | ftsLeaf index tree leaf => rfl

/-- Canonical inputs are the actual one-digest serialized inputs prepared for the graph. -/
theorem coordinates_input (address : Address) :
    input parameter (address, coordinates otsSecret ftsSecret labels address.inputCoordinate) =
      canonicalGraphInput parameter otsSecret ftsSecret address.position labels := by
  cases address with
  | chain lay tree leaf chainIdx step =>
      fin_cases step <;>
        simp [input, Address.inputCoordinate, Address.position, coordinates, canonicalGraphInput,
          canonicalGraphSlots, Position.domain, Position.children, chainLength, winternitzBits]
  | ftsLeaf index tree leaf =>
      simp [input, Address.inputCoordinate, Address.position, coordinates, canonicalGraphInput,
        canonicalGraphSlots, Position.domain]

attribute [local irreducible] canonicalGraphInput canonicalGraphSlots

/-- Programming other distinct structural addresses preserves an already correct entry. -/
theorem programGraphCache_preserves_label (positions : List Position) (cache : QueryCache HashSpec)
    (position : Position)
    (hcache : cache (canonicalGraphInput parameter otsSecret ftsSecret position labels) =
      some (labels position)) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) = some (labels position) := by
  induction positions generalizing cache with
  | nil => exact hcache
  | cons first rest ih =>
      apply ih
      change (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret first labels)
        (labels first)) (canonicalGraphInput parameter otsSecret ftsSecret position labels) = _
      by_cases heq : position = first
      · subst first
        exact QueryCache.cacheQuery_self _ _ _
      · rw [QueryCache.cacheQuery_of_ne]
        · exact hcache
        · exact canonicalGraphInput_separated parameter otsSecret ftsSecret position first heq labels labels

/-- Membership in the prepared graph is enough to identify the programmed full answer. -/
theorem programGraphCache_label (positions : List Position) (cache : QueryCache HashSpec)
    (position : Position) (hposition : position ∈ positions) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (canonicalGraphInput parameter otsSecret ftsSecret position labels) = some (labels position) := by
  induction positions generalizing cache with
  | nil => simp at hposition
  | cons first rest ih =>
      rcases List.mem_cons.mp hposition with heq | hrest
      · subst first
        exact programGraphCache_preserves_label parameter otsSecret ftsSecret labels rest
          (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret position labels)
            (labels position)) position (QueryCache.cacheQuery_self _ _ _)
      · exact ih _ hrest

theorem programGraphCache_preserves_other (positions : List Position) (cache : QueryCache HashSpec)
    (bytes : HashInput)
    (hmiss : ∀ position ∈ positions,
      bytes ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache bytes = cache bytes := by
  induction positions generalizing cache with
  | nil => rfl
  | cons first rest ih =>
      change Graph.programGraphCache parameter otsSecret ftsSecret rest labels
        (cache.cacheQuery (canonicalGraphInput parameter otsSecret ftsSecret first labels)
          (labels first)) bytes = _
      rw [ih _ (fun position hp => hmiss position (List.mem_cons_of_mem _ hp))]
      exact QueryCache.cacheQuery_of_ne _ _ (hmiss first List.mem_cons_self)

/-- A noncanonical payload at a parsed chain/FORS-leaf address cannot alias any other
prepared structural input, including the multi-digest tree and leaf-compression inputs. -/
theorem row_miss_all_inputs (address : Address) (value : Digest)
    (hmiss : value ≠ coordinates otsSecret ftsSecret labels address.inputCoordinate)
    (position : Position) :
    input parameter (address, value) ≠ canonicalGraphInput parameter otsSecret ftsSecret position labels := by
  intro heq
  have hposition : address.position = position := by
    have heq' := heq
    unfold input canonicalGraphInput at heq'
    have hfields := (tweakableInput_injective heq').1
    exact Position.domain_injective
      (hashFields_injective address.position.domain_inRange position.domain_inRange hfields)
  subst position
  rw [← coordinates_input parameter otsSecret ftsSecret labels address] at heq
  exact hmiss (congrArg Prod.snd (input_injective parameter heq))

theorem programGraphCache_row_miss (positions : List Position) (cache : QueryCache HashSpec)
    (address : Address) (value : Digest)
    (hmiss : value ≠ coordinates otsSecret ftsSecret labels address.inputCoordinate) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (input parameter (address, value)) = cache (input parameter (address, value)) :=
  programGraphCache_preserves_other parameter otsSecret ftsSecret labels positions cache _
    (fun position _ => row_miss_all_inputs parameter otsSecret ftsSecret labels address value hmiss position)

/-- Full lookup equation for every payload at a prepared one-digest row. The fallback is
the original cache; no freshness or independence of that original cache is presumed. -/
theorem programGraphCache_row_lookup (positions : List Position) (cache : QueryCache HashSpec)
    (address : Address) (hposition : address.position ∈ positions) (value : Digest) :
    Graph.programGraphCache parameter otsSecret ftsSecret positions labels cache
      (input parameter (address, value)) =
        if value = coordinates otsSecret ftsSecret labels address.inputCoordinate then
          some (labels address.position) else cache (input parameter (address, value)) := by
  by_cases heq : value = coordinates otsSecret ftsSecret labels address.inputCoordinate
  · rw [ite_eq_left heq, heq, coordinates_input]
    exact programGraphCache_label parameter otsSecret ftsSecret labels positions cache _ hposition
  · rw [ite_eq_right heq]
    exact programGraphCache_row_miss parameter otsSecret ftsSecret labels positions cache address value heq

end SphincsFors.Security.HiddenGraph
