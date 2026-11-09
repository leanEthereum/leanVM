/-
# Support invariants of the wrapped committed soundness game

Structural facts about runs of `CommittedSoundness.runTrace`, needed to relate the winning
event to the fork point and to discharge the forking lemma's side conditions:

* every cached commitment appears in the miss log (the log records exactly the
  cache misses, and the cache only grows);
* consequently the output commitment always appears in the miss log (the
  wrapped adversary's final query either hits the cache, so the commitment
  was logged at its first miss, or misses and is logged then), and its
  challenge is the cached one;
* the miss log stays within the query budget (each miss consumes one unit);
* therefore, on the support of `runTrace`, winning is *equivalent* to the fork
  point being defined.

Benedikt Wagner's formalization (https://github.com/b-wagn/fv-pq-da), ported at 4475179c and
modified for VCVio afa6593.
-/
module

public import PqDas.Proof.CommittedSoundness.Fork

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section coupling

variable [DecidableEq ComVC]

omit [DecidableEq ComVC] in
/-- The wrapped adversary, with the final query spelled as a lifted sum-spec
query (the canonical form for structural analyses). Definitionally equal to
`wrappedAdv`. -/
private lemma wrappedAdv_eq (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC) :
    wrappedAdv A ckVC =
      A ckVC >>= fun out =>
        (liftM ((unifSpec + (ComVC →ₒ L)).query (Sum.inr out.1))) >>= fun l =>
          pure (out.1, out.2, l) := by
  unfold wrappedAdv
  simp only [monad_norm]
  rfl

/-- Dispatch of a single lifted sum-spec query through the caching simulator. -/
private lemma sim_run_liftM_query (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (st : SimState ComVC L) :
    (simulateQ (unifForward ComVC L + roImpl ComVC L)
        (liftM ((unifSpec + (ComVC →ₒ L)).query t))).run st =
      ((unifForward ComVC L + roImpl ComVC L) t).run st := by
  simp only [simulateQ_liftM_query, monadLift_self, QueryImpl.mapQuery_query]

private lemma wrappedSim_HasQuery_query (q : ComVC) :
    simulateQ (unifForward ComVC L + roImpl ComVC L)
      (HasQuery.query (spec := (ComVC →ₒ L))
        (m := OracleComp (unifSpec + (ComVC →ₒ L))) q) =
      roImpl ComVC L q := by
  change simulateQ (unifForward ComVC L + roImpl ComVC L)
    (liftM (liftM ((ComVC →ₒ L).query q) :
      OracleQuery (unifSpec + (ComVC →ₒ L)) _)) = _
  simp [simulateQ_query]

private lemma wrappedSim_query_bind {β : Type} (st : SimState ComVC L) (q : ComVC)
    (f : L → OracleComp (unifSpec + (ComVC →ₒ L)) β) :
    (simulateQ (unifForward ComVC L + roImpl ComVC L)
        (HasQuery.query (spec := (ComVC →ₒ L)) q >>= f)).run st =
      (roImpl ComVC L q).run st >>= fun x =>
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (f x.1)).run x.2 := by
  simp only [simulateQ_bind, wrappedSim_HasQuery_query, StateT.run_bind]

/-- The caching simulation preserves the invariant that every cached
commitment appears in the miss log. -/
theorem cached_mem_queryLog_of_support {α : Type}
    {oa : OracleComp (unifSpec + (ComVC →ₒ L)) α}
    (st : SimState ComVC L) {z : α × SimState ComVC L}
    (hz : z ∈ support ((simulateQ (unifForward ComVC L + roImpl ComVC L) oa).run st))
    (hinv : ∀ com : ComVC, (st.1 com).isSome → com ∈ st.2) :
    ∀ com : ComVC, (z.2.1 com).isSome → com ∈ z.2.2 := by
  induction oa using OracleComp.inductionOn generalizing st z with
  | pure x =>
      obtain rfl : z = (x, st) := by
        simpa [simulateQ_pure, StateT.run_pure, support_pure] using hz
      exact hinv
  | query_bind t mx ih =>
      rw [simulateQ_query_bind, StateT.run_bind, support_bind] at hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨us, hus, hz'⟩ := hz
      cases t with
      | inl i =>
          rcases st with ⟨cache, log⟩
          obtain ⟨u, rfl⟩ : us ∈ Set.range (fun u => (u, cache, log)) := by
            simpa [QueryImpl.add_apply_inl, unifForward, support_map] using hus
          exact ih u (cache, log) hz' hinv
      | inr com =>
          rcases st with ⟨cache, log⟩
          cases hcache : cache com with
          | some v =>
              have hus' : us ∈ ({(v, cache, log)} : Set _) := by
                convert hus using 1
                simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, hcache]
                exact Iff.rfl
              obtain rfl := Set.mem_singleton_iff.mp hus'
              exact ih v (cache, log) hz' hinv
          | none =>
              obtain ⟨u, rfl⟩ : us ∈ Set.range (fun u : L =>
                  (u, cache.cacheQuery com u, log ++ [com])) := by
                convert hus using 1
                simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                  hcache, StateT.run_set]
                exact Iff.rfl
              refine ih u ((cache.cacheQuery com u :
                (ComVC →ₒ L).QueryCache), log ++ [com]) hz' ?_
              intro com' hcom'
              by_cases heq : com' = com
              · exact List.mem_append_right _ (heq ▸ List.mem_singleton_self com)
              · dsimp only at hcom'
                rw [QueryCache.cacheQuery_of_ne _ _ heq] at hcom'
                exact List.mem_append_left _ (hinv com' hcom')

/-- On the support of the caching simulation of the wrapped adversary, the
output commitment's challenge is cached and the commitment is logged. -/
theorem chal_cached_of_support (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC)
    {com : ComVC} {c : Fin n → Λ} {l : L} {st : SimState ComVC L}
    (hz : ((com, c, l), st) ∈ support ((simulateQ (unifForward ComVC L + roImpl ComVC L)
      (wrappedAdv A ckVC)).run (∅, []))) :
    st.1 com = some l ∧ com ∈ st.2 := by
  unfold wrappedAdv at hz
  rw [simulateQ_bind, StateT.run_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨⟨o1, o2⟩, st₁⟩, hout, hz⟩ := hz
  have hinv : ∀ com : ComVC, (st₁.1 com).isSome → com ∈ st₁.2 :=
    cached_mem_queryLog_of_support (∅, []) hout (by simp)
  dsimp only at hz
  rw [wrappedSim_query_bind, support_bind] at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨⟨l', st₂⟩, hl, hz⟩ := hz
  have heq : ((com, c, l), st) = ((o1, o2, l'), st₂) := by
    simpa [simulateQ_pure, StateT.run_pure, support_pure] using hz
  obtain ⟨⟨rfl, -, rfl⟩, rfl⟩ :
      (com = o1 ∧ c = o2 ∧ l = l') ∧ st = st₂ := by
    simpa [Prod.ext_iff] using heq
  rcases st₁ with ⟨cache, log⟩
  cases hcache : cache com with
  | some v =>
      rw [roImpl_run_hit hcache] at hl
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨hcache, hinv com (by simp [hcache])⟩
  | none =>
      obtain ⟨u, hu⟩ : (l, st) ∈ Set.range (fun u : L =>
          (u, cache.cacheQuery com u, log ++ [com])) := by
        convert hl using 1
        simp [roImpl, StateT.run_bind, StateT.run_get, hcache, StateT.run_set]
      obtain ⟨rfl, rfl⟩ : u = l ∧ (cache.cacheQuery com u,
          log ++ [com]) = st := by simpa [Prod.mk.injEq] using hu
      refine ⟨?_, ?_⟩
      · show QueryCache.cacheQuery (spec := (ComVC →ₒ L)) cache com u com = some u
        exact QueryCache.cacheQuery_self cache com u
      · show com ∈ log ++ [com]
        exact List.mem_append_right _ (List.mem_singleton_self _)

variable [Fintype Γ] [DecidableEq Λ]

/-- On the support of `runTrace`, the output commitment appears in the miss
log and its challenge is the cached one. -/
theorem trace_com_mem_queryLog
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC)
    {trace : Trace Λ n ComVC L}
    (htrace : trace ∈ support (runTrace C vc chk A ckVC)) :
    trace.com ∈ trace.queryLog ∧ trace.roCache trace.com = some trace.chal := by
  unfold runTrace at htrace
  rw [support_bind] at htrace
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at htrace
  obtain ⟨⟨⟨com, c, l⟩, st⟩, hz, rfl⟩ := htrace
  have h := chal_cached_of_support A ckVC hz
  exact ⟨h.2, h.1⟩

/-- The miss log of a `runTrace` run of an adversary with hash-query bound `Q`
has length at most `Q + 1` (the `+ 1` accounting for the wrapped final query). -/
theorem trace_queryLog_length_le
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) {A : NiCsAdv Λ n CkVC ComVC L} {Q : ℕ} (ckVC : CkVC)
    (hA : HashQueryBound (A ckVC) Q) {trace : Trace Λ n ComVC L}
    (htrace : trace ∈ support (runTrace C vc chk A ckVC)) :
    trace.queryLog.length ≤ Q + 1 := by
  unfold runTrace at htrace
  rw [support_bind] at htrace
  simp only [Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at htrace
  obtain ⟨⟨out, st⟩, hz, rfl⟩ := htrace
  have hbound : HashQueryBound (wrappedAdv A ckVC) (Q + 1) := by
    rw [wrappedAdv_eq]
    refine OracleComp.isQueryBoundP_bind hA fun out _ => ?_
    show HashQueryBound _ (0 + 1)
    rw [hashQueryBound_query_bind_iff]
    exact ⟨Nat.one_pos, fun u => by simp [HashQueryBound]⟩
  simpa using queryLog_length_le_of_hashQueryBound hbound (∅, []) hz

/-- On the support of `runTrace` (for a query-bounded adversary), winning is
equivalent to the fork point being defined. -/
theorem win_iff_forkPoint_isSome
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) {A : NiCsAdv Λ n CkVC ComVC L} {Q : ℕ} (ckVC : CkVC)
    (hA : HashQueryBound (A ckVC) Q) {trace : Trace Λ n ComVC L}
    (htrace : trace ∈ support (runTrace C vc chk A ckVC)) :
    trace.win = true ↔ (forkPoint Q trace).isSome := by
  constructor
  · intro hwin
    have hmem := (trace_com_mem_queryLog C vc chk A ckVC htrace).1
    have hlen := trace_queryLog_length_le C vc chk ckVC hA htrace
    have hidx : trace.queryLog.findIdx (· == trace.com) < Q + 1 :=
      lt_of_lt_of_le
        (List.findIdx_lt_length_of_exists ⟨trace.com, hmem, by simp⟩) hlen
    simp [forkPoint, hwin, hmem, hidx]
  · intro hsome
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp hsome
    exact win_of_forkPoint_eq_some hs

end coupling

end CommittedSoundness

end PqDas
