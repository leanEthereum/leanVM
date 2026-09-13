import SphincsSecurity.Proof.Ots.OtsPrefixSeedGame
import SphincsSecurity.Proof.Base.QueryCapAccounting
namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierSigningRun boundaryEval frontierRoot

theorem worldImpl_queryBound (segment : OtsPrefix) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (input : OracleWorld.Domain) :
    (segment.worldImpl high outside input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery
      (if input matches .inr _ then 1 else 0) := by
  cases input with
  | inl input =>
      simp only [worldImpl, isQueryBoundP_query_iff, PartialChainEndpoint.IsPrefixQuery, false_implies]
  | inr bytes => exact segment.hashImpl_queryBound high outside bytes

private theorem withTrace_run {Input Target Trace : Type} {spec : OracleSpec Input} {target : OracleSpec Target} [Monoid Trace]
    (impl : QueryImpl spec (OracleComp target)) (trace : (input : spec.Domain) → spec.Range input → Trace) (input : spec.Domain) :
    (impl.withTrace trace input).run = (fun answer => (answer, trace input answer)) <$> impl input := by
  simp [QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]

theorem worldTrace_counted_le (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (result : (OracleWorld.Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      ((segment.worldImpl high outside).withTrace (signingBoundaryTrace segment.parameter) input).run)) :
    result.2 ≤ result.1.2.hashCalls := by
  rw [withTrace_run, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  rw [signingBoundaryTrace_hashCalls_eq]
  have h := QueryCap.counted_le_of_queryBound _ _ _ (segment.worldImpl_queryBound high outside input) original horiginal
  cases input <;> exact h

theorem boundary_counted_le (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    {Result : Type} (computation : OracleComp OracleWorld Result) (result : (Result × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery (segment.boundary high outside computation))) :
    result.2 ≤ result.1.2.hashCalls :=
  QueryCap.counted_writer_simulate_le _ SigningBoundaryTrace.hashCalls SigningBoundaryTrace.hashCalls_mul _
    (segment.worldTrace_counted_le high outside) computation result hresult

theorem adversaryImpl_counted_le (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (input : (OracleWorld + SigningSpec).Domain)
    (result : ((OracleWorld + SigningSpec).Range input × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.adversaryImpl root high outside ftsSecret words frontier input).run)) : result.2 ≤ result.1.2.hashCalls := by
  cases input with
  | inl input => exact segment.worldTrace_counted_le high outside input result hresult
  | inr message =>
      rw [segment.adversaryImpl_signing, WriterT.run_mk] at hresult
      have hzero := QueryCap.counted_le_of_queryBound _ _ 0 (segment.lift_prob_queryBound _) result hresult
      exact hzero.trans (Nat.zero_le _)

theorem adversaryRun_counted_le (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : ((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.adversaryRun root high outside ftsSecret words frontier computation))) : result.2 ≤ result.1.2.hashCalls :=
  QueryCap.counted_writer_simulate_le _ SigningBoundaryTrace.hashCalls SigningBoundaryTrace.hashCalls_mul _
    (segment.adversaryImpl_counted_le root high outside ftsSecret words frontier) (logged computation) result hresult

theorem gameRest_counted_le (segment : OtsPrefix) (root : Digest) (high : segment.Query → High)
    (outside : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.gameRest root high outside ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls := by
  simp only [gameRest, QueryCap.counted_bind, QueryCap.counted_pure, bind_assoc, pure_bind, Nat.add_zero] at hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨first, hfirst, hresult⟩ := hresult
  rw [mem_support_bind_iff] at hresult
  obtain ⟨second, hsecond, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  rw [SigningBoundaryTrace.hashCalls_mul]
  exact Nat.add_le_add (segment.adversaryRun_counted_le root high outside ftsSecret words frontier _ first hfirst)
    (segment.boundary_counted_le high outside _ second hsecond)

theorem game_counted_le (segment : OtsPrefix) (high : segment.Query → High) (outside : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.game high outside ftsSecret words frontier adversary))) : result.2 ≤ result.1.2.hashCalls := by
  rw [game, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  have h := segment.gameRest_counted_le _ high outside ftsSecret words frontier adversary original horiginal
  simp only [SigningBoundaryTrace.hashCalls_mul]
  omega

theorem seedGame_counted_le (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (endpoint : Digest) (adversary : Adversary)
    (result : (Bool × SigningBoundaryTrace) × Nat)
    (hresult : result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
      (segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary))) :
    result.2 ≤ result.1.2.hashCalls :=
  segment.game_counted_le _ _ ftsSecret words _ adversary result hresult

end SphincsSecurity.Concrete.OtsPrefix
