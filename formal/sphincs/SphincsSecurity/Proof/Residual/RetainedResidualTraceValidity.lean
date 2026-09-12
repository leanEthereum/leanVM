import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Proof.Ots.PrefixEncodingRisk
import SphincsSecurity.Proof.Residual.RetainedResidualMessageTrace
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def TraceValid (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id) (trace : SigningBoundaryTrace) : Prop :=
  ∀ entry ∈ trace.messageCalls, FtsProbeSimulation.MessageHashInput parameter entry.1 ∧ entry.2 = oracle entry.1

theorem traceValid_one (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id) : TraceValid parameter oracle 1 := by
  intro entry hentry
  cases hentry

theorem traceValid_mul (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id) (left right : SigningBoundaryTrace)
    (hleft : TraceValid parameter oracle left) (hright : TraceValid parameter oracle right) : TraceValid parameter oracle (left * right) := by
  intro entry hentry
  rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append] at hentry
  exact hentry.elim (hleft entry) (hright entry)

theorem fixedHashWorld_traceValid (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (answer : OracleWorld.Range input) (hanswer : 𝒟[fixedHashWorld oracle input] answer ≠ 0) :
    TraceValid parameter oracle (signingBoundaryTrace parameter input answer) := by
  cases input with
  | inl input => exact traceValid_one parameter oracle
  | inr input =>
      simp only [fixedHashWorld, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hanswer
      subst answer
      change TraceValid parameter oracle (FreeMonoid.of
        (if FtsProbeSimulation.MessageHashInput parameter input then some (input, oracle input) else none))
      by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input
      · rw [if_pos hmessage]
        intro entry hentry
        change entry ∈ [(input, oracle input)] at hentry
        obtain rfl := List.mem_singleton.mp hentry
        exact ⟨hmessage, rfl⟩
      · rw [if_neg hmessage]
        intro entry hentry
        cases hentry

theorem fixedBoundaryRun_traceValid {Result : Type} (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld Result) (result : Result × SigningBoundaryTrace)
    (hresult : 𝒟[fixedBoundaryRun parameter oracle computation] result ≠ 0) : TraceValid parameter oracle result.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      simp only [fixedBoundaryRun_pure, evalDist_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact traceValid_one parameter oracle
  | query_bind input next ih =>
      rw [ResidualByteFrontend.fixedBoundaryRun_query_bind, evalDist_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨answer, hanswer, hresult⟩ := hresult
      rw [evalDist_map, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨tail, htail, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact traceValid_mul parameter oracle _ _ (fixedHashWorld_traceValid parameter oracle input answer hanswer) (ih answer tail htail)

theorem cacheFold_property (property : HashInput → HashOutput → Prop) (entries : List (HashInput × HashOutput))
    (hentries : ∀ entry ∈ entries, property entry.1 entry.2) (cache : ExternalCache)
    (hcache : ∀ input answer, cache input = some answer → property input answer) :
    ∀ (input : HashInput) (answer : HashOutput),
      (entries.foldl (fun (current : ExternalCache) entry => Function.update current entry.1 (some entry.2)) cache) input = some answer → property input answer := by
  induction entries generalizing cache with
  | nil => exact hcache
  | cons entry entries ih =>
      apply ih (fun item hitem => hentries item (List.mem_cons_of_mem entry hitem))
      intro input answer h
      change Function.update cache entry.1 (some entry.2) input = some answer at h
      by_cases heq : input = entry.1
      · subst input
        simp only [Function.update_self, Option.some.injEq] at h
        subst answer
        exact hentries entry (List.mem_cons_self ..)
      · rw [Function.update_of_ne heq] at h
        exact hcache input answer h

theorem applyBoundary_cacheMatches (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (memory : Memory) (trace : SigningBoundaryTrace) (htrace : TraceValid parameter oracle trace)
    (hmatches : ResidualByteFrontend.CacheMatches oracle memory.external.cache) :
    ResidualByteFrontend.CacheMatches oracle (memory.applyBoundary trace).external.cache :=
  cacheFold_property (fun input answer => answer = oracle input) trace.messageCalls (fun entry hentry => (htrace entry hentry).2) memory.external.cache hmatches

theorem applyBoundary_cacheClean (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (actual : Labels)
    (memory : Memory) (trace : SigningBoundaryTrace) (htrace : TraceValid parameter oracle trace)
    (hclean : CacheClean parameter words disclosed actual memory.external.cache) :
    CacheClean parameter words disclosed actual (memory.applyBoundary trace).external.cache := by
  apply cacheFold_property (fun input answer => ¬CanonicalProbeRouting.Bad parameter words disclosed actual input answer)
    trace.messageCalls _ memory.external.cache hclean
  rintro ⟨input, answer⟩ hentry ⟨position, hat, _⟩
  obtain ⟨payload, heq⟩ := (htrace (input, answer) hentry).1
  rw [← heq] at hat
  exact (decodePosition_none_iff parameter _).mp (decodePosition_message parameter payload) position hat

theorem applyBoundary_encodingClean (parameter : PublicParameter) (oracle : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (messages : EncodingPosition → Digest) (selections : ReferenceFamily)
    (memory : Memory) (trace : SigningBoundaryTrace) (htrace : TraceValid parameter oracle trace)
    (hclean : ResidualByteFrontend.ReplyClean (PublicEncodingMatch.Match parameter messages words selections) memory.external.cache) :
    ResidualByteFrontend.ReplyClean (PublicEncodingMatch.Match parameter messages words selections) (memory.applyBoundary trace).external.cache := by
  apply cacheFold_property (fun input answer => ¬PublicEncodingMatch.Match parameter messages words selections input answer)
    trace.messageCalls _ memory.external.cache hclean
  rintro ⟨input, answer⟩ hentry ⟨position, hat, _⟩
  exact ResidualByteFrontend.message_not_encoding parameter input (htrace (input, answer) hentry).1 position hat

end SphincsSecurity.Concrete.RetainedResidual
