import SphincsSecurity.Proof.Ots.OtsPrefixVisible
import SphincsSecurity.Proof.Ots.OtsPrefixAllocation
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec PartialChainEndpoint
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

theorem visibleWorldImpl_counted (segment : OtsPrefix) (high : segment.Query → High) (input : OracleWorld.Domain) :
    QueryCap.counted IsPrefixQuery (segment.visibleWorldImpl high input) =
      (fun answer => (answer, if segment.Selects input then 1 else 0)) <$> segment.visibleWorldImpl high input := by
  cases input with
  | inl input =>
      simp only [visibleWorldImpl, QueryCap.counted_query, IsPrefixQuery, Selects, if_false]
      rfl
  | inr bytes =>
      cases hparse : segment.parse bytes with
      | none =>
          simp only [visibleWorldImpl, visibleHashImpl, hparse, QueryCap.counted_query, IsPrefixQuery, Selects, ne_self_iff_false, if_false]
          rfl
      | some query =>
          simp only [visibleWorldImpl, visibleHashImpl, hparse, QueryCap.counted_map, QueryCap.counted_query,
            IsPrefixQuery, Selects, if_pos (Option.some_ne_none query), if_true, Functor.map_map]
          rfl

theorem visible_counted_program (segment : OtsPrefix) (high : segment.Query → High) {Result : Type}
    (computation : OracleComp OracleWorld Result) :
    QueryCap.counted IsPrefixQuery (simulateQ (segment.visibleWorldImpl high) computation) =
      simulateQ (segment.visibleWorldImpl high) (QueryCap.counted segment.Selects computation) := by
  have h := QueryCap.simulate_counted segment.Selects IsPrefixQuery (segment.visibleWorldImpl high)
    (QueryImpl.id' segment.VisibleWorld) (segment.visibleWorldImpl high)
    (fun input => by rw [simulateQ_id']; exact segment.visibleWorldImpl_counted high input) computation
  simpa only [simulateQ_id'] using h

theorem visibleGame_counted_le (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsPrefixQuery (segment.visibleGame high outside ftsSecret words frontier adversary))) :
    result.2 ≤ result.1.2.hashCalls := by
  let charge : CausalFrontierProgram.TraceCharge segment.parameter := {
    selected := segment.Selects
    decidable := inferInstance
    cost := SigningBoundaryTrace.hashCalls
    cost_mul := SigningBoundaryTrace.hashCalls_mul
    uniform := fun _ => not_false
    step := by
      intro input answer
      cases input with
      | inl input => simp only [Selects, if_false, Nat.zero_le]
      | inr bytes =>
          rw [signingBoundaryTrace_hashCalls_eq]
          by_cases hs : segment.Selects (.inr bytes) <;> simp only [if_pos hs, if_neg hs, if_true, Nat.zero_le, le_refl]
  }
  rw [visibleGame, visible_counted_program] at hresult
  exact CausalFrontierProgram.TraceCharge.game_counted_le charge outside ftsSecret words frontier adversary result
    (QueryCap.simulate_oracle_mem_support _ _ result hresult)

theorem visibleSeedGame_counted_le (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) (endpoint : Digest)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted IsPrefixQuery
      (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint))) :
    result.2 ≤ result.1.2.hashCalls :=
  segment.visibleGame_counted_le auxiliary.high _ ftsSecret words _ adversary result hresult

end SphincsSecurity.Concrete.OtsPrefix
