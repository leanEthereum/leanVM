import SphincsSecurity.Proof.Fts.OriginalCertificateBound
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def hashRowsCache : List (HashInput × HashOutput) → QueryCache HashSpec
  | [] => ∅
  | row :: rows => (hashRowsCache rows).cacheQuery row.1 row.2

theorem hashRowsCache_le (rows : List (HashInput × HashOutput)) (cache : QueryCache HashSpec)
    (hrows : ∀ row ∈ rows, cache row.1 = some row.2) : hashRowsCache rows ≤ cache := by
  induction rows with
  | nil => exact bot_le
  | cons row rows ih =>
      intro input output houtput
      by_cases heq : input = row.1
      · subst input
        simp only [hashRowsCache, QueryCache.cacheQuery_self, Option.some.injEq] at houtput
        exact (hrows row (List.mem_cons_self ..)).trans (congrArg some houtput)
      · apply ih (fun entry hentry => hrows entry (List.mem_cons_of_mem _ hentry))
        simpa only [hashRowsCache, QueryCache.cacheQuery_of_ne _ _ heq] using houtput

theorem hashRowsCache_lookup (rows : List (HashInput × HashOutput)) (f : QueryImpl HashSpec Id)
    (hrows : ∀ row ∈ rows, row.2 = f row.1) (input : HashInput) (hinput : (input, f input) ∈ rows) :
    hashRowsCache rows input = some (f input) := by
  induction rows with
  | nil => cases hinput
  | cons row rows ih =>
      by_cases heq : input = row.1
      · rw [heq, hashRowsCache, QueryCache.cacheQuery_self, hrows row (List.mem_cons_self ..)]
      · rw [hashRowsCache, QueryCache.cacheQuery_of_ne _ _ heq]
        apply ih (fun entry hentry => hrows entry (List.mem_cons_of_mem _ hentry))
        rcases List.mem_cons.mp hinput with hhead | htail
        · exact False.elim (heq (congrArg Prod.fst hhead))
        · exact htail

private theorem romImpl_hash_cached (input : HashInput) (cache : QueryCache HashSpec)
    (result : HashOutput × QueryCache HashSpec) (hr : result ∈ support ((romImpl (.inr input)).run cache)) :
    result.2 input = some result.1 := by
  change result ∈ support ((randomOracle input).run cache) at hr
  cases hc : cache input with
  | some output =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc, mem_support_pure_iff] at hr
      subst result
      exact hc
  | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map] at hr
      obtain ⟨output, _, rfl⟩ := hr
      exact QueryCache.cacheQuery_self cache input output

theorem boundaryRun_message_cached {Result : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld Result) (cache : QueryCache HashSpec)
    (result : (Result × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    ∀ row ∈ result.1.2.messageCalls, result.2 row.1 = some row.2 := by
  induction computation using OracleComp.inductionOn generalizing cache result with
  | pure value =>
      simp only [boundaryRun, simulateQ_pure, WriterT.run_pure, StateT.run_pure, mem_support_pure_iff] at hr
      subst result
      intro row hrow
      cases hrow
  | query_bind input next ih =>
      rw [boundaryRun_bind, boundaryRun_query, mem_support_bind_iff] at hr
      obtain ⟨middle, hmiddle, hr⟩ := hr
      rw [support_map] at hmiddle
      obtain ⟨source, hsource, rfl⟩ := hmiddle
      rw [support_map] at hr
      obtain ⟨last, hlast, rfl⟩ := hr
      have hcache : source.2 ≤ last.2 := by
        apply simulateQ_romImpl_cache_le (next source.1) source.2 (last.1.1, last.2)
        rw [← boundaryRun_forget parameter (next source.1) source.2, support_map]
        exact ⟨last, hlast, rfl⟩
      intro row hrow
      rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append] at hrow
      rcases hrow with hhead | htail
      · cases input with
        | inl sample => cases hhead
        | inr input =>
            by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
            · simp only [signingBoundaryTrace, if_pos hm] at hhead
              change row ∈ [(input, source.1)] at hhead
              obtain rfl := List.mem_singleton.mp hhead
              exact hcache (romImpl_hash_cached input cache source hsource)
            · simp [signingBoundaryTrace, SigningBoundaryTrace.messageCalls, hm] at hhead
      · exact ih source.1 source.2 last hlast row htail

theorem boundaryRun_messageCache_le {Result : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld Result) (cache : QueryCache HashSpec)
    (result : (Result × SigningBoundaryTrace) × QueryCache HashSpec)
    (hr : result ∈ support (boundaryRun parameter computation cache)) :
    hashRowsCache result.1.2.messageCalls ≤ result.2 :=
  hashRowsCache_le _ _ (boundaryRun_message_cached parameter computation cache result hr)

theorem eligibleSigningView?_some_mono (parameter : PublicParameter) (root : Digest)
    (before after : QueryCache HashSpec) (hcache : before ≤ after) (payload : HashInput)
    (entry : SigningEntry) (view : FewTimeView)
    (hview : eligibleSigningView? (messageAnswers parameter before) root payload entry = some view) :
    eligibleSigningView? (messageAnswers parameter after) root payload entry = some view := by
  cases hs : entry.2 with
  | none => simp [eligibleSigningView?, hs] at hview
  | some signature =>
      by_cases hp : messageDigestPayload root entry.1 signature.randomness = payload
      · simp [eligibleSigningView?, hs, hp] at hview
      · simp only [eligibleSigningView?, observedSigningView?, hs, Option.bind_eq_bind', Option.bind_some, if_neg hp] at hview ⊢
        cases ho : messageAnswers parameter before (messageDigestPayload root entry.1 signature.randomness) with
        | none => simp [ho] at hview
        | some output =>
            have ha : messageAnswers parameter after (messageDigestPayload root entry.1 signature.randomness) = some output := hcache ho
            simpa only [ha, ho] using hview

theorem TargetCertificateAt.mono {key : SecretKey} {required : Finset FtsTree}
    {before after : QueryCache HashSpec} {log : QueryLog SigningSpec} {input : HashInput}
    (h : TargetCertificateAt key required (before, log) input) (hcache : before ≤ after) :
    TargetCertificateAt key required (after, log) input := by
  obtain ⟨output, houtput, hm, ha, hcovered⟩ := h
  refine ⟨output, hcache houtput, hm, ha, ?_⟩
  intro tree ht
  obtain ⟨slot, view, hv, hi, hl⟩ := (targetTreeMatchCount_pos_iff _ _ tree).mp (hcovered tree ht)
  exact (targetTreeMatchCount_pos_iff _ _ tree).mpr ⟨slot, view,
    eligibleSigningView?_some_mono key.parameter key.root before after hcache (payloadOf input) (log.get slot) view hv, hi, hl⟩

end SphincsSecurity.Concrete
