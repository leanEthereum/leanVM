/-
# Lockstep coupling between the miss log and the counted challenge oracle

Value-level coupling between `CommittedSoundness.runTrace`'s internal miss log and the
outer log of counted `Sum.inr ()` challenge queries, transliterated from the
analogous Fiat-Shamir machinery in VCVio
(`VCVio.CryptoFoundations.FiatShamir.Sigma.Fork`), with the hash-point type
`M × Commit` replaced by the single commitment type `ComVC`:

* a step-support engine characterizing one step of the layered simulation
  `loggingOracle ∘ (unifForward + roImpl)` and a generic layered invariant
  skeleton (`preservesInv_layered`);
* the counting coupling: the miss log grows by exactly one entry per outer
  `Sum.inr ()` query (`runTrace_queryLog_length_eq`);
* the value coupling: each miss-log entry is cached with exactly the answer
  recorded at the corresponding outer-log position
  (`runTrace_cache_outer_lockstep`);
* prefix determinism: two runs of the same wrapped adversary whose outer logs
  share a prefix (up to and including a focused `Sum.inr ()` query with
  possibly different answers) agree on the corresponding prefix of their miss
  logs (`runTrace_queryLog_take_eq`);
* the two `ReplayFork`-facing corollaries: the fork point always points at an
  existing outer query (`runTrace_forkPoint_CfReachable`), and both branches
  of a successful contextual fork agree on the output commitment and on the
  miss log up to the fork point (`runTrace_com_eq_of_mem_contextFork`).

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

section lockstep

variable [DecidableEq ComVC]

/-! ### Per-step support characterizations

Two thin lemmas that describe the support of a single step of the layered simulation
`(simulateQ loggingOracle (((unifForward + roImpl) t).run (c₀, l₀))).run`. Used by the
layered preservation helper below to do *all* per-step case analysis in one place. The
`Sum.inl` step always issues a forwarded uniform query and logs it; the `Sum.inr` step
branches on whether the cache already contains the asked commitment. -/

private lemma support_step_inl
    (i : ℕ) (s : SimState ComVC L)
    (z : ((unifSpec + (ComVC →ₒ L)).Range (Sum.inl i) × SimState ComVC L) ×
      QueryLog (wrappedSpec L)) :
    z ∈ support ((simulateQ (wrappedSpec L).loggingOracle
      (((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run s)).run) ↔
    ∃ u : (unifSpec + (ComVC →ₒ L)).Range (Sum.inl i),
      z = ((u, s), [⟨Sum.inl i, u⟩]) := by
  obtain ⟨c₀, l₀⟩ := s
  have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run (c₀, l₀) =
      (liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
        fun u => pure (u, (c₀, l₀)) := by
    simp [QueryImpl.add_apply_inl, unifForward]
  rw [hrun]
  change z ∈ support (simulateQ loggingOracle
      ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
        fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run ↔ _
  rw [OracleComp.run_simulateQ_loggingOracle_query_bind
    (spec := wrappedSpec L) (Sum.inl i) (fun u => pure (u, (c₀, l₀)))]
  simp only [support_bind, support_map, support_query, Set.mem_univ, simulateQ_pure,
    WriterT.run_pure', support_pure, Set.image_singleton, Set.iUnion_const]
  exact Set.mem_iUnion.trans (exists_congr fun _ => Set.mem_singleton_iff)

private lemma support_step_inr
    (com : ComVC) (s : SimState ComVC L)
    (z : ((unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × SimState ComVC L) ×
      QueryLog (wrappedSpec L)) :
    z ∈ support ((simulateQ (wrappedSpec L).loggingOracle
      (((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run s)).run) ↔
    (∃ v, s.1 com = some v ∧ z = ((v, s), [])) ∨
    (s.1 com = none ∧ ∃ v,
      z = ((v, (s.1.cacheQuery com v, s.2 ++ [com])), [⟨Sum.inr (), v⟩])) := by
  obtain ⟨c₀, l₀⟩ := s
  by_cases hcache : c₀ com = none
  · have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (c₀, l₀) =
        (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
          fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) := by
      simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
        StateT.run_set, hcache]
    rw [hrun]
    change z ∈ support (simulateQ loggingOracle
        ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
          fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
            OracleComp _ _))).run ↔ _
    rw [OracleComp.run_simulateQ_loggingOracle_query_bind
      (spec := wrappedSpec L) (Sum.inr ())
      (fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])))]
    simp only [support_bind, support_map, support_query, Set.mem_univ,
      simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
      Set.iUnion_const]
    refine ⟨fun ⟨_, ⟨v, rfl⟩, hzeq⟩ => Or.inr ⟨hcache, v, hzeq⟩, ?_⟩
    rintro (⟨v, hv, _⟩ | ⟨_, v, hzeq⟩)
    · exact absurd hv.symm (hcache ▸ Option.some_ne_none v)
    · exact ⟨_, ⟨v, rfl⟩, hzeq⟩
  · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
    have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (c₀, l₀) =
        pure (v, (c₀, l₀)) := by
      simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
    rw [hrun]
    change z ∈ support (simulateQ loggingOracle
        (pure (v, (c₀, l₀)) : OracleComp _ _)).run ↔ _
    simp only [simulateQ_pure, WriterT.run_pure', support_pure]
    refine ⟨fun h => Or.inl ⟨v, hv.symm, h⟩, ?_⟩
    rintro (⟨v', hv', hzeq⟩ | ⟨h0, _⟩)
    · obtain rfl : v = v' := Option.some_inj.mp (hv.trans hv')
      exact hzeq
    · exact absurd h0 (Option.ne_none_iff_exists.mpr ⟨v, hv⟩)

/-- Unfolds one bind step of the layered `unifForward + roImpl` simulation: running the
simulator on `liftM (query t) >>= oa` from state `s` first runs the single-query step
`((unifForward + roImpl) t).run s`, then continues the simulation of `oa` from the resulting
state. Shared opener for the `query_bind` case of every structural induction below. -/
private lemma simulateQ_add_run_query_bind {γ : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (oa : (unifSpec + (ComVC →ₒ L)).Range t →
      OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (s : SimState ComVC L) :
    (simulateQ (unifForward ComVC L + roImpl ComVC L)
        (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= oa)).run s =
      (((unifForward ComVC L + roImpl ComVC L) t).run s) >>= fun us =>
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (oa us.1)).run us.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

/-! ### Layered preservation helpers

Two skeletons that capture the entire structural induction `OracleComp.inductionOn`
on `Y` for the layered simulation. All five Coupling lemmas below boil down to writing
the per-step preservation in *three* concrete cases (Sum.inl, Sum.inr cache hit, Sum.inr
cache miss) using the support characterizations above; the inductive bookkeeping is
factored out once. -/

private theorem preservesInv_layered {γ : Type}
    (Inv : SimState ComVC L → QueryLog (wrappedSpec L) → Prop)
    (hstep : ∀ t (s : SimState ComVC L) (w : QueryLog (wrappedSpec L)),
      Inv s w →
      ∀ z ∈ support ((simulateQ (wrappedSpec L).loggingOracle
        (((unifForward ComVC L + roImpl ComVC L) t).run s)).run),
      Inv z.1.2 (w ++ z.2))
    (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (s₀ : SimState ComVC L) (w₀ : QueryLog (wrappedSpec L))
    (hinit : Inv s₀ w₀)
    {z : (γ × SimState ComVC L) × QueryLog (wrappedSpec L)}
    (hz : z ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run s₀)).run)) :
    Inv z.1.2 (w₀ ++ z.2) := by
  classical
  induction Y using OracleComp.inductionOn generalizing s₀ w₀ z with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinit
  | query_bind t oa ih =>
      rw [simulateQ_add_run_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, rfl⟩ := hz
      simp only [Prod.map_fst, Prod.map_snd, id_eq, ← List.append_assoc]
      exact ih us_w.1.1 (s₀ := us_w.1.2) (w₀ := w₀ ++ us_w.2)
        (hstep t s₀ w₀ hinit us_w hus_w) hpw

private theorem queryLog_length_eq_outer_inr_count
    {γ : Type} (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (c₀ : (ComVC →ₒ L).QueryCache) (l₀ : List ComVC) {z : γ × SimState ComVC L}
    {outerLog : QueryLog (wrappedSpec L)} (hz : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run)) :
    z.2.2.length = l₀.length + outerLog.countQ (· = Sum.inr ()) := by
  have h := preservesInv_layered
    (Inv := fun s w => s.2.length = l₀.length + w.countQ (· = Sum.inr ()))
    (hstep := ?_) Y (c₀, l₀) [] (by simp [QueryLog.countQ]) hz
  · simpa [List.nil_append] using h
  · intro t s w hI z hz
    cases t with
    | inl i =>
        rw [support_step_inl] at hz
        obtain ⟨u, rfl⟩ := hz
        simpa [QueryLog.countQ, QueryLog.getQ, QueryLog.countQ_append] using hI
    | inr com =>
        rw [support_step_inr] at hz
        rcases hz with ⟨v, _, rfl⟩ | ⟨_, v, rfl⟩
        · simpa using hI
        · have h1 : QueryLog.countQ (spec := wrappedSpec L)
              [⟨Sum.inr (), v⟩] (· = Sum.inr ()) = 1 := by
            simp [QueryLog.countQ, QueryLog.getQ]
          simp only [List.length_append, List.length_singleton, QueryLog.countQ_append, h1, hI]
          lia

/- Lockstep value invariant for `runTrace`'s inner simulation. Three coupled invariants
travel together along the simulation:

* **(prefix)** the trace's internal `queryLog` only ever extends `l₀`;
* **(monotonicity)** any pre-existing entry in `c₀` is preserved in the final `roCache`;
* **(lockstep)** every cache-miss entry in the trace's `queryLog` is paired in lockstep with
  the corresponding `Sum.inr ()` answer in the outer log. Specifically, for every position
  `i ∈ [l₀.length, z.queryLog.length)`, the trace's cache stores some value `ω` for the
  query `z.queryLog[i]`, and the outer log's `(i - l₀.length)`-th `Sum.inr ()` response is
  the same `ω`.

This is the value-level strengthening of `queryLog_length_eq_outer_inr_count`: the latter
only counts entries, while this lemma threads the recorded values through the cache and the
outer log together. -/
private theorem queryLog_cache_outer_lockstep [DecidableEq L] {γ : Type}
    (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ) (c₀ : (ComVC →ₒ L).QueryCache)
    (l₀ : List ComVC) {z : γ × SimState ComVC L}
    {outerLog : QueryLog (wrappedSpec L)}
    (hz : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run)) :
    (∃ l_new, z.2.2 = l₀ ++ l_new) ∧
    (∀ com ω, c₀ com = some ω → z.2.1 com = some ω) ∧
    (∀ i, l₀.length ≤ i → ∀ (h_hi : i < z.2.2.length),
      ∃ ω, z.2.1 (z.2.2[i]'h_hi) = some ω ∧
        QueryLog.getQueryValue? outerLog (Sum.inr ()) (i - l₀.length) = some ω) := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hz
      obtain ⟨hz_eq, hlog_eq⟩ := hz
      subst hz_eq
      subst hlog_eq
      refine ⟨⟨[], by simp⟩, fun _ _ h => h, ?_⟩
      intro i h_lo h_hi
      change i < l₀.length at h_hi
      lia
  | query_bind t oa ih =>
      rw [simulateQ_add_run_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at hz
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at hz
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := hz
      have hih := ih (u := us_w.1.1) (c₀ := us_w.1.2.1) (l₀ := us_w.1.2.2)
        (z := pw.1) (outerLog := pw.2) hpw
      have hz_eq' : (pw.1, us_w.2 ++ pw.2) = (z, outerLog) := by
        rw [show ((pw.1, us_w.2 ++ pw.2) : _ × QueryLog (wrappedSpec L)) =
              Prod.map id (fun x => us_w.2 ++ x) pw from rfl]
        exact hz_eq
      obtain ⟨hz_eq1, hz_eq2⟩ := Prod.mk.inj hz_eq'
      subst hz_eq1
      subst hz_eq2
      cases t with
      | inl j =>
          have hrun :
              ((unifForward ComVC L + roImpl ComVC L) (Sum.inl j)).run (c₀, l₀) =
              (liftM ((wrappedSpec L).query (Sum.inl j)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifForward]
          rw [hrun] at hus_w
          change us_w ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl j)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec L) (Sum.inl j) (fun u => pure (u, (c₀, l₀)))] at hus_w
          rw [support_bind] at hus_w
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at hus_w
          obtain ⟨_, ⟨u, hu_eq⟩, hus_w_in_u⟩ := hus_w
          subst hu_eq
          rw [Set.mem_singleton_iff] at hus_w_in_u
          subst hus_w_in_u
          obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
          refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
          intro i h_lo h_hi
          obtain ⟨ω, hcache, hlog⟩ := hlock i h_lo h_hi
          refine ⟨ω, hcache, ?_⟩
          change QueryLog.getQueryValue?
            ((⟨Sum.inl j, u⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec L).Range j) ::
              pw.2) (Sum.inr ()) (i - l₀.length) = some ω
          rw [QueryLog.getQueryValue?_cons_of_ne]
          · exact hlog
          · exact Sum.inl_ne_inr
      | inr com =>
          by_cases hcache : c₀ com = none
          · have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) =
                (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at hus_w
            change us_w ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec L) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])))] at hus_w
            rw [support_bind] at hus_w
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at hus_w
            obtain ⟨_, ⟨v, hv_eq⟩, hus_w_in_u⟩ := hus_w
            subst hv_eq
            rw [Set.mem_singleton_iff] at hus_w_in_u
            subst hus_w_in_u
            obtain ⟨⟨l_new', hpref'⟩, hmono', hlock'⟩ := hih
            dsimp only at hpref' hmono' hlock'
            have hpref_z : pw.1.2.2 = l₀ ++ ([com] ++ l_new') := by
              rw [hpref']
              simp [List.append_assoc]
            refine ⟨⟨[com] ++ l_new', hpref_z⟩, ?_, ?_⟩
            · intro com' ω hmc'
              apply hmono'
              by_cases heq : com' = com
              · subst heq
                rw [hcache] at hmc'
                exact (Option.some_ne_none ω hmc'.symm).elim
              · rwa [QueryCache.cacheQuery_of_ne _ _ heq]
            · intro i h_lo h_hi
              by_cases hi_eq : i = l₀.length
              · subst hi_eq
                have hidx : pw.1.2.2[l₀.length]'h_hi = com := by
                  have h_hi'' : l₀.length < (l₀ ++ ([com] ++ l_new')).length := by
                    rwa [← List.append_assoc, ← hpref']
                  have hcongr : pw.1.2.2[l₀.length]'h_hi =
                      (l₀ ++ ([com] ++ l_new'))[l₀.length]'h_hi'' :=
                    List.getElem_of_eq hpref_z _
                  rw [hcongr, List.getElem_append_right (Nat.le_refl _)]
                  simp
                refine ⟨v, ?_, ?_⟩
                · rw [hidx]
                  exact hmono' com v (QueryCache.cacheQuery_self c₀ com v)
                · change QueryLog.getQueryValue?
                    ((⟨Sum.inr (), v⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec L).Range j) ::
                      pw.2) (Sum.inr ()) (l₀.length - l₀.length) = some v
                  rw [Nat.sub_self]
                  exact QueryLog.getQueryValue?_cons_self_zero (Sum.inr ()) v pw.2
              · have h_lo' : (l₀ ++ [com]).length ≤ i := by
                  simp only [List.length_append, List.length_singleton]
                  lia
                obtain ⟨ω, hcacheω, hlogω⟩ := hlock' i h_lo' h_hi
                refine ⟨ω, hcacheω, ?_⟩
                obtain ⟨k, hk⟩ : ∃ k, i - l₀.length = k + 1 := ⟨i - l₀.length - 1, by lia⟩
                have hk_eq : k = i - (l₀ ++ [com]).length := by
                  simp only [List.length_append, List.length_singleton] at hk ⊢
                  lia
                change QueryLog.getQueryValue?
                  ((⟨Sum.inr (), v⟩ : (j : ℕ ⊕ Unit) × (wrappedSpec L).Range j) ::
                    pw.2) (Sum.inr ()) (i - l₀.length) = some ω
                rw [hk, QueryLog.getQueryValue?_cons_self_succ, hk_eq]
                exact hlogω
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at hus_w
            change us_w ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at hus_w
            subst hus_w
            obtain ⟨⟨l_new, hpref⟩, hmono, hlock⟩ := hih
            refine ⟨⟨l_new, hpref⟩, hmono, ?_⟩
            intro i h_lo h_hi
            obtain ⟨ω, hcacheω, hlogω⟩ := hlock i h_lo h_hi
            refine ⟨ω, hcacheω, ?_⟩
            change QueryLog.getQueryValue? ([] ++ pw.2)
              (Sum.inr ()) (i - l₀.length) = some ω
            rw [List.nil_append]
            exact hlogω

/- Prefix monotonicity: running `(simulateQ (unifForward + roImpl) Y).run (c₀, l₀)` produces a
final simulator state whose `queryLog` component extends `l₀`. The resulting list always
starts with the initial `l₀`: cache misses only append entries, and cache hits plus
`unifForward`-forwarded queries never touch `l₀`. Used by `inner_prefix_det` to fix the first
`l₀.length` positions of the final `queryLog`. -/
private theorem queryLog_extends_l₀
    {γ : Type} (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (c₀ : (ComVC →ₒ L).QueryCache) (l₀ : List ComVC)
    {z : γ × SimState ComVC L}
    {outerLog : QueryLog (wrappedSpec L)}
    (h : (z, outerLog) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run)) :
    z.2.2.take l₀.length = l₀ := by
  classical
  induction Y using OracleComp.inductionOn generalizing c₀ l₀ z outerLog with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h
      obtain ⟨hz_eq, _⟩ := h
      rw [hz_eq]
      exact List.take_length
  | query_bind t oa ih =>
      rw [simulateQ_add_run_query_bind, simulateQ_bind, WriterT.run_bind', support_bind] at h
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h
      obtain ⟨us_w, hus_w, pw, hpw, hz_eq⟩ := h
      obtain ⟨hzeq, _⟩ := Prod.mk.inj hz_eq
      subst hzeq
      cases t with
      | inl i =>
          have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run
              (c₀, l₀) =
              (liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifForward]
          rw [hrun] at hus_w
          change us_w ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec L) (Sum.inl i) (fun u => pure (u, (c₀, l₀)))] at hus_w
          rw [support_bind] at hus_w
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at hus_w
          obtain ⟨_, ⟨u, hu_eq⟩, hus_w_in⟩ := hus_w
          subst hu_eq
          rw [Set.mem_singleton_iff] at hus_w_in
          subst hus_w_in
          exact ih u c₀ l₀ hpw
      | inr com =>
          by_cases hcache : c₀ com = none
          · have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) =
                (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at hus_w
            change us_w ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec L) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])))] at hus_w
            rw [support_bind] at hus_w
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at hus_w
            obtain ⟨_, ⟨v, hv_eq⟩, hus_w_in⟩ := hus_w
            subst hv_eq
            rw [Set.mem_singleton_iff] at hus_w_in
            subst hus_w_in
            calc pw.1.2.2.take l₀.length
                = (pw.1.2.2.take (l₀ ++ [com]).length).take l₀.length := by
                    rw [List.take_take, min_eq_left (by simp [List.length_append])]
              _ = (l₀ ++ [com]).take l₀.length := by
                    rw [ih v (c₀.cacheQuery com v) (l₀ ++ [com]) hpw]
              _ = l₀ := List.take_left
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at hus_w
            change us_w ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at hus_w
            subst hus_w
            exact ih v c₀ l₀ hpw

/- Outer-log prefix-determinism for `runTrace`'s inner simulation. If the two outer
logs share a common prefix `p` (with `#{Sum.inr ()} = j` in `p`), then the first
`l₀.length + j` positions of the final internal `queryLog`s coincide. This is the
bisimulation up to the focused query used by
`runTrace_com_eq_of_mem_contextFork`: a common outer prefix fixes the
adversary's state (and hence the next cache-miss input) through that query. -/
private theorem inner_prefix_det
    {γ : Type} (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (c₀ : (ComVC →ₒ L).QueryCache) (l₀ : List ComVC)
    {z₁ z₂ : γ × SimState ComVC L}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec L)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run))
    (p suffix₁ suffix₂ : QueryLog (wrappedSpec L))
    (hlog₁ : outerLog₁ = p ++ suffix₁)
    (hlog₂ : outerLog₂ = p ++ suffix₂) :
    z₁.2.2.take (l₀.length + p.countQ (· = Sum.inr ())) =
      z₂.2.2.take (l₀.length + p.countQ (· = Sum.inr ())) := by
  classical
  induction Y using OracleComp.inductionOn generalizing
      c₀ l₀ z₁ z₂ outerLog₁ outerLog₂ p suffix₁ suffix₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
      obtain ⟨hz₁_eq, houter₁'⟩ := h₁
      obtain ⟨hz₂_eq, _⟩ := h₂
      rw [houter₁'] at hlog₁
      have hp_empty : p = [] := by
        cases p with
        | nil => rfl
        | cons _ _ => simp at hlog₁
      subst hp_empty
      simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
      rw [hz₁_eq, hz₂_eq]
  | query_bind t oa ih =>
      rw [simulateQ_add_run_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := hz_eq₂
      obtain ⟨rfl, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨rfl, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ suffix₁ := hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ suffix₂ := hz_eq2₂.trans hlog₂
      cases t with
      | inl i =>
          have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run
              (c₀, l₀) =
              (liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifForward]
          rw [hrun] at hus_w₁ hus_w₂
          change us_w₁ ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w₁
          change us_w₂ ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w₂
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec L) (Sum.inl i) (fun u => pure (u, (c₀, l₀)))] at hus_w₁ hus_w₂
          rw [support_bind] at hus_w₁ hus_w₂
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at hus_w₁ hus_w₂
          obtain ⟨_, ⟨u₁, hu₁_eq⟩, hus_w₁_in⟩ := hus_w₁
          obtain ⟨_, ⟨u₂, hu₂_eq⟩, hus_w₂_in⟩ := hus_w₂
          subst hu₁_eq
          subst hu₂_eq
          rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
          subst hus_w₁_in
          subst hus_w₂_in
          cases p with
          | nil =>
              simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
              have h₁' : pw₁.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀
                  (oa u₁) c₀ l₀ hpw₁
              have h₂' : pw₂.1.2.2.take l₀.length = l₀ :=
                queryLog_extends_l₀
                  (oa u₂) c₀ l₀ hpw₂
              rw [h₁', h₂']
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq]
                at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]
                intro h
                cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec L) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁ hpw₂ p_tail suffix₁ suffix₂ htail₁ htail₂
      | inr com =>
          by_cases hcache : c₀ com = none
          · have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) =
                (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at hus_w₁ hus_w₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w₂
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec L) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])))] at hus_w₁ hus_w₂
            rw [support_bind] at hus_w₁ hus_w₂
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at hus_w₁ hus_w₂
            obtain ⟨_, ⟨v₁, hv₁_eq⟩, hus_w₁_in⟩ := hus_w₁
            obtain ⟨_, ⟨v₂, hv₂_eq⟩, hus_w₂_in⟩ := hus_w₂
            subst hv₁_eq
            subst hv₂_eq
            rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
            subst hus_w₁_in
            subst hus_w₂_in
            cases p with
            | nil =>
                simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                have take_eq : ∀ (v : (wrappedSpec L).Range (Sum.inr ()))
                    (pw : (γ × SimState ComVC L) × QueryLog (wrappedSpec L)),
                    pw ∈ support ((simulateQ (wrappedSpec L).loggingOracle
                      ((simulateQ (unifForward ComVC L + roImpl ComVC L)
                        (oa v)).run (c₀.cacheQuery com v, l₀ ++ [com]))).run) →
                    pw.1.2.2.take l₀.length = l₀ := fun v pw h => by
                  have hext := queryLog_extends_l₀
                    (oa v) (c₀.cacheQuery com v) (l₀ ++ [com]) h
                  calc pw.1.2.2.take l₀.length
                      = (pw.1.2.2.take (l₀ ++ [com]).length).take l₀.length := by
                          rw [List.take_take, min_eq_left (by simp [List.length_append])]
                    _ = (l₀ ++ [com]).take l₀.length := by rw [hext]
                    _ = l₀ := List.take_left
                rw [take_eq v₁ pw₁ hpw₁, take_eq v₂ pw₂ hpw₂]
            | cons p_head p_tail =>
                simp only [List.cons_append, List.cons.injEq]
                  at houter₁_eq houter₂_eq
                obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                have hv_eq : v₁ = v₂ := by
                  obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                  exact eq_of_heq hheq
                subst hv_eq
                have hpH_fst : p_head.1 = Sum.inr () := by rw [← hhead₁]
                have hp_count :
                    QueryLog.countQ (spec := wrappedSpec L) (p_head :: p_tail)
                        (· = Sum.inr ()) =
                      QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ()) + 1 := by
                  simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
                rw [hp_count]
                have hlen_eq : l₀.length +
                      (QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ()) + 1) =
                    (l₀ ++ [com]).length +
                      QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ()) := by
                  have : (l₀ ++ [com]).length = l₀.length + 1 := by
                    simp [List.length_append]
                  lia
                rw [hlen_eq]
                exact ih v₁ (c₀.cacheQuery com v₁) (l₀ ++ [com])
                  hpw₁ hpw₂ p_tail suffix₁ suffix₂ htail₁ htail₂
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at hus_w₁ hus_w₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w₂
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at hus_w₁ hus_w₂
            subst hus_w₁
            subst hus_w₂
            exact ih v c₀ l₀ hpw₁ hpw₂ p suffix₁ suffix₂ houter₁_eq houter₂_eq

/- One-more-step extension of `inner_prefix_det`: if the outer logs of two runs share the
prefix `p ++ [⟨Sum.inr (), v_i⟩]` (allowing the values `v₁, v₂` at position `|p|` to differ),
then the internal `queryLog`s coincide for one more entry than `inner_prefix_det` guarantees,
namely up to position `l₀.length + p.countQ(· = Sum.inr ()) + 1`. The extra entry is the
input `com` of the next cache-miss query issued by the adversary: its value is determined by
the adversary's state after consuming the shared prefix `p`, which is common to both runs. -/
private theorem inner_prefix_det_one_more_inr
    {γ : Type} (Y : OracleComp (unifSpec + (ComVC →ₒ L)) γ)
    (c₀ : (ComVC →ₒ L).QueryCache) (l₀ : List ComVC)
    {z₁ z₂ : γ × SimState ComVC L}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec L)}
    (h₁ : (z₁, outerLog₁) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run))
    (h₂ : (z₂, outerLog₂) ∈ support
      ((simulateQ (wrappedSpec L).loggingOracle
        ((simulateQ (unifForward ComVC L + roImpl ComVC L) Y).run
          (c₀, l₀))).run))
    (p : QueryLog (wrappedSpec L))
    {v₁ v₂ : L} {rest₁ rest₂ : QueryLog (wrappedSpec L)}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    z₁.2.2.take (l₀.length + p.countQ (· = Sum.inr ()) + 1) =
      z₂.2.2.take (l₀.length + p.countQ (· = Sum.inr ()) + 1) := by
  classical
  induction Y using OracleComp.inductionOn generalizing
      c₀ l₀ z₁ z₂ outerLog₁ outerLog₂ p v₁ v₂ rest₁ rest₂ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure, simulateQ_pure, WriterT.run_pure',
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at h₁
      obtain ⟨_, houter₁'⟩ := h₁
      rw [houter₁'] at hlog₁
      simp at hlog₁
  | query_bind t oa ih =>
      rw [simulateQ_add_run_query_bind, simulateQ_bind, WriterT.run_bind',
        support_bind] at h₁ h₂
      simp only [Set.mem_iUnion, support_map, Set.mem_image] at h₁ h₂
      obtain ⟨us_w₁, hus_w₁, pw₁, hpw₁, hz_eq₁⟩ := h₁
      obtain ⟨us_w₂, hus_w₂, pw₂, hpw₂, hz_eq₂⟩ := h₂
      have hz_eq'₁ : (pw₁.1, us_w₁.2 ++ pw₁.2) = (z₁, outerLog₁) := hz_eq₁
      have hz_eq'₂ : (pw₂.1, us_w₂.2 ++ pw₂.2) = (z₂, outerLog₂) := hz_eq₂
      obtain ⟨rfl, hz_eq2₁⟩ := Prod.mk.inj hz_eq'₁
      obtain ⟨rfl, hz_eq2₂⟩ := Prod.mk.inj hz_eq'₂
      have houter₁_eq : us_w₁.2 ++ pw₁.2 = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁) :=
        hz_eq2₁.trans hlog₁
      have houter₂_eq : us_w₂.2 ++ pw₂.2 = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂) :=
        hz_eq2₂.trans hlog₂
      cases t with
      | inl i =>
          have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run
              (c₀, l₀) =
              (liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => pure (u, (c₀, l₀)) := by
            simp [QueryImpl.add_apply_inl, unifForward]
          rw [hrun] at hus_w₁ hus_w₂
          change us_w₁ ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w₁
          change us_w₂ ∈ support (simulateQ loggingOracle
              ((liftM ((wrappedSpec L).query (Sum.inl i)) : OracleComp _ _) >>=
                fun u => (pure (u, (c₀, l₀)) : OracleComp _ _))).run at hus_w₂
          rw [OracleComp.run_simulateQ_loggingOracle_query_bind
            (spec := wrappedSpec L) (Sum.inl i)
            (fun u => pure (u, (c₀, l₀)))] at hus_w₁ hus_w₂
          rw [support_bind] at hus_w₁ hus_w₂
          simp only [support_map, support_query, Set.mem_univ,
            simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
            Set.iUnion_const] at hus_w₁ hus_w₂
          obtain ⟨_, ⟨u₁, hu₁_eq⟩, hus_w₁_in⟩ := hus_w₁
          obtain ⟨_, ⟨u₂, hu₂_eq⟩, hus_w₂_in⟩ := hus_w₂
          subst hu₁_eq
          subst hu₂_eq
          rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
          subst hus_w₁_in
          subst hus_w₂_in
          cases p with
          | nil =>
              simp at houter₁_eq
          | cons p_head p_tail =>
              simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
              obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
              obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
              have hu_eq : u₁ = u₂ := by
                obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                exact eq_of_heq hheq
              subst hu_eq
              have hpH_fst : p_head.1 ≠ Sum.inr () := by
                rw [← hhead₁]
                intro h
                cases h
              have hp_count :
                  QueryLog.countQ (spec := wrappedSpec L) (p_head :: p_tail)
                      (· = Sum.inr ()) =
                    QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ()) := by
                simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
              rw [hp_count]
              exact ih u₁ c₀ l₀ hpw₁ hpw₂ p_tail htail₁ htail₂
      | inr com =>
          by_cases hcache : c₀ com = none
          · have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) =
                (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get,
                StateT.run_set, hcache]
            rw [hrun] at hus_w₁ hus_w₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp _ _) >>=
                  fun v => (pure (v, (c₀.cacheQuery com v, l₀ ++ [com])) :
                    OracleComp _ _))).run at hus_w₂
            rw [OracleComp.run_simulateQ_loggingOracle_query_bind
              (spec := wrappedSpec L) (Sum.inr ())
              (fun v => pure (v, (c₀.cacheQuery com v, l₀ ++ [com])))] at hus_w₁ hus_w₂
            rw [support_bind] at hus_w₁ hus_w₂
            simp only [support_map, support_query, Set.mem_univ,
              simulateQ_pure, WriterT.run_pure', support_pure, Set.image_singleton,
              Set.iUnion_const] at hus_w₁ hus_w₂
            obtain ⟨_, ⟨w₁, hw₁_eq⟩, hus_w₁_in⟩ := hus_w₁
            obtain ⟨_, ⟨w₂, hw₂_eq⟩, hus_w₂_in⟩ := hus_w₂
            subst hw₁_eq
            subst hw₂_eq
            rw [Set.mem_singleton_iff] at hus_w₁_in hus_w₂_in
            subst hus_w₁_in
            subst hus_w₂_in
            cases p with
            | nil =>
                simp only [QueryLog.countQ, QueryLog.getQ_nil, List.length_nil, add_zero]
                have h₁' : pw₁.1.2.2.take (l₀ ++ [com]).length = l₀ ++ [com] :=
                  queryLog_extends_l₀
                    (oa w₁) (c₀.cacheQuery com w₁) (l₀ ++ [com]) hpw₁
                have h₂' : pw₂.1.2.2.take (l₀ ++ [com]).length = l₀ ++ [com] :=
                  queryLog_extends_l₀
                    (oa w₂) (c₀.cacheQuery com w₂) (l₀ ++ [com]) hpw₂
                have hlen : (l₀ ++ [com]).length = l₀.length + 1 := by
                  simp [List.length_append]
                rw [← hlen, h₁', h₂']
            | cons p_head p_tail =>
                simp only [List.cons_append, List.cons.injEq] at houter₁_eq houter₂_eq
                obtain ⟨hhead₁, htail₁⟩ := houter₁_eq
                obtain ⟨hhead₂, htail₂⟩ := houter₂_eq
                have hw_eq : w₁ = w₂ := by
                  obtain ⟨_, hheq⟩ := Sigma.mk.inj (hhead₁.trans hhead₂.symm)
                  exact eq_of_heq hheq
                subst hw_eq
                have hpH_fst : p_head.1 = Sum.inr () := by rw [← hhead₁]
                have hp_count :
                    QueryLog.countQ (spec := wrappedSpec L) (p_head :: p_tail)
                        (· = Sum.inr ()) =
                      QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ())
                        + 1 := by
                  simp [QueryLog.countQ, QueryLog.getQ_cons, hpH_fst]
                rw [hp_count]
                have hlen_eq : l₀.length +
                      (QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ())
                        + 1) + 1 =
                    (l₀ ++ [com]).length +
                      QueryLog.countQ (spec := wrappedSpec L) p_tail (· = Sum.inr ())
                        + 1 := by
                  have : (l₀ ++ [com]).length = l₀.length + 1 := by
                    simp [List.length_append]
                  lia
                rw [hlen_eq]
                exact ih w₁ (c₀.cacheQuery com w₁) (l₀ ++ [com])
                  hpw₁ hpw₂ p_tail htail₁ htail₂
          · rcases Option.ne_none_iff_exists.mp hcache with ⟨v, hv⟩
            have hrun : ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run
                (c₀, l₀) = pure (v, (c₀, l₀)) := by
              simp [QueryImpl.add_apply_inr, roImpl, StateT.run_bind, StateT.run_get, ← hv]
            rw [hrun] at hus_w₁ hus_w₂
            change us_w₁ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w₁
            change us_w₂ ∈ support (simulateQ loggingOracle
                ((pure (v, (c₀, l₀)) : OracleComp _ _) : OracleComp _ _)).run at hus_w₂
            simp only [simulateQ_pure, WriterT.run_pure', support_pure] at hus_w₁ hus_w₂
            subst hus_w₁
            subst hus_w₂
            exact ih v c₀ l₀ hpw₁ hpw₂ p houter₁_eq houter₂_eq

/-! ### `runTrace`-level corollaries

Specializations of the engine to `runTrace`'s initial state `(∅, [])`, phrased at the
`replayFirstRun`/`contextFork` level consumed by the forking analysis. -/

variable [Fintype Γ] [DecidableEq Λ]

/-- Specialization of `queryLog_length_eq_outer_inr_count` to `runTrace`'s initial state
`(∅, [])`: the trace's miss log has the same length as the count of `Sum.inr ()` outer
queries in the recorded log. -/
theorem runTrace_queryLog_length_eq
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC)
    {x : Trace Λ n ComVC L} {outerLog : QueryLog (wrappedSpec L)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (runTrace C vc chk A ckVC))) :
    x.queryLog.length = outerLog.countQ (· = Sum.inr ()) := by
  classical
  unfold replayFirstRun withQueryLog runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq)).symm
  have hlog_eq : a.2 = outerLog := by simpa [Prod.map_apply] using congrArg Prod.snd ha_eq
  rw [hxqueryLog, ← hlog_eq]
  simpa using queryLog_length_eq_outer_inr_count
    (γ := ComVC × (Fin n → Λ) × L)
    (wrappedAdv A ckVC) ∅ [] (z := a.1) (outerLog := a.2) ha_mem

/-- Specialization of `queryLog_cache_outer_lockstep` to `runTrace`'s initial state
`(∅, [])`: the trace's `queryLog[i]` is cached in `x.roCache`, and the cached value matches
the outer log's `i`-th `Sum.inr ()` response. -/
theorem runTrace_cache_outer_lockstep [DecidableEq L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC)
    {x : Trace Λ n ComVC L} {outerLog : QueryLog (wrappedSpec L)}
    (hx : (x, outerLog) ∈ support (replayFirstRun (runTrace C vc chk A ckVC))) :
    ∀ i, ∀ (h_hi : i < x.queryLog.length),
      ∃ ω, x.roCache (x.queryLog[i]'h_hi) = some ω ∧
        QueryLog.getQueryValue? outerLog (Sum.inr ()) i = some ω := by
  classical
  unfold replayFirstRun withQueryLog runTrace at hx
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  have hxqueryLog : x.queryLog = a.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq)).symm
  have hxroCache : x.roCache = a.1.2.1 := by
    simpa [Prod.map_apply, Trace.roCache] using
      (congrArg Trace.roCache (congrArg Prod.fst ha_eq)).symm
  have hlog_eq : a.2 = outerLog := by simpa [Prod.map_apply] using congrArg Prod.snd ha_eq
  intro i h_hi
  obtain ⟨_, _, hlock⟩ :=
    queryLog_cache_outer_lockstep
      (γ := ComVC × (Fin n → Λ) × L)
      (wrappedAdv A ckVC) ∅ [] (z := a.1) (outerLog := a.2) ha_mem
  obtain ⟨ω, hcache, hlog⟩ := hlock i (Nat.zero_le _) (hxqueryLog ▸ h_hi)
  refine ⟨ω, ?_, ?_⟩
  · rwa [hxroCache, List.getElem_of_eq hxqueryLog]
  · simpa [← hlog_eq] using hlog

/-- The `forkPoint`-based reachability invariant for `runTrace`: whenever
`forkPoint Q x = some s`, the outer `QueryLog` of `replayFirstRun (runTrace ...)` has a
`Sum.inr ()` query at position `↑s`. This discharges `ReplayFork`'s `CfReachable` side
condition. -/
theorem runTrace_forkPoint_CfReachable [DecidableEq L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (Q : ℕ) (ckVC : CkVC) :
    CfReachable (runTrace C vc chk A ckVC)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q) (Sum.inr ())
      (forkPoint Q) := by
  intro x log hx s hs
  have hslt : (↑s : ℕ) < log.countQ (· = Sum.inr ()) :=
    runTrace_queryLog_length_eq C vc chk A ckVC hx ▸
      (List.getElem?_eq_some_iff.mp (forkPoint_getElem?_eq_some_com hs)).1
  exact QueryLog.getQueryValue?_isSome_of_lt log (Sum.inr ()) ↑s hslt

/-- **Determinism of `runTrace`'s miss log from the outer-log prefix.** If the outer logs
of two runs of `runTrace` share a prefix `p` followed by a `Sum.inr ()` query (whose
response may differ across runs), then the traces' miss logs coincide on the first
`p.countQ (· = Sum.inr ()) + 1` entries. This is the `runTrace` specialization of
`inner_prefix_det_one_more_inr`, rephrased at the `replayFirstRun`-visible level. -/
theorem runTrace_queryLog_take_eq
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (ckVC : CkVC)
    {x₁ x₂ : Trace Λ n ComVC L}
    {outerLog₁ outerLog₂ : QueryLog (wrappedSpec L)}
    (h₁ : (x₁, outerLog₁) ∈ support (replayFirstRun (runTrace C vc chk A ckVC)))
    (h₂ : (x₂, outerLog₂) ∈ support (replayFirstRun (runTrace C vc chk A ckVC)))
    (p : QueryLog (wrappedSpec L))
    {v₁ v₂ : L} {rest₁ rest₂ : QueryLog (wrappedSpec L)}
    (hlog₁ : outerLog₁ = p ++ (⟨Sum.inr (), v₁⟩ :: rest₁))
    (hlog₂ : outerLog₂ = p ++ (⟨Sum.inr (), v₂⟩ :: rest₂)) :
    x₁.queryLog.take (p.countQ (· = Sum.inr ()) + 1) =
      x₂.queryLog.take (p.countQ (· = Sum.inr ()) + 1) := by
  classical
  unfold replayFirstRun withQueryLog runTrace at h₁ h₂
  simp only [bind_pure_comp, simulateQ_map, WriterT.run_map', support_map] at h₁ h₂
  obtain ⟨a₁, ha_mem₁, ha_eq₁⟩ := h₁
  obtain ⟨a₂, ha_mem₂, ha_eq₂⟩ := h₂
  have hxqL₁ : x₁.queryLog = a₁.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq₁)).symm
  have hxqL₂ : x₂.queryLog = a₂.1.2.2 := by
    simpa [Prod.map_apply, Trace.queryLog] using
      (congrArg Trace.queryLog (congrArg Prod.fst ha_eq₂)).symm
  have hlog_eq₁ : a₁.2 = outerLog₁ := by
    simpa [Prod.map_apply] using congrArg Prod.snd ha_eq₁
  have hlog_eq₂ : a₂.2 = outerLog₂ := by
    simpa [Prod.map_apply] using congrArg Prod.snd ha_eq₂
  have hdet := inner_prefix_det_one_more_inr
    (γ := ComVC × (Fin n → Λ) × L)
    (wrappedAdv A ckVC) ∅ []
    (z₁ := a₁.1) (z₂ := a₂.1)
    (outerLog₁ := a₁.2) (outerLog₂ := a₂.2)
    ha_mem₁ ha_mem₂ p (v₁ := v₁) (v₂ := v₂)
    (rest₁ := rest₁) (rest₂ := rest₂)
    (hlog_eq₁.trans hlog₁) (hlog_eq₂.trans hlog₂)
  simpa [hxqL₁, hxqL₂] using hdet

/-- If two successful contextual forks select the same fork index, their output
commitments agree, and their miss logs agree up to (and including) the fork point. -/
theorem runTrace_com_eq_of_mem_contextFork [DecidableEq L]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) (Q : ℕ) (ckVC : CkVC)
    (x₁ x₂ : Trace Λ n ComVC L) (s : Fin (Q + 1))
    (hsup : some (x₁, x₂) ∈ support (contextFork (runTrace C vc chk A ckVC)
      (fun j : ℕ ⊕ Unit => match j with | .inl _ => 0 | .inr () => Q) (Sum.inr ())
      (forkPoint Q)))
    (h₁ : forkPoint Q x₁ = some s)
    (h₂ : forkPoint Q x₂ = some s) :
    x₁.com = x₂.com ∧
      x₁.queryLog.take (↑s + 1) = x₂.queryLog.take (↑s + 1) := by
  classical
  let qb : ℕ ⊕ Unit → ℕ := fun j => match j with | .inl _ => 0 | .inr () => Q
  let cf := forkPoint (Λ := Λ) (n := n) (ComVC := ComVC) (L := L) Q
  let main := runTrace C vc chk A ckVC
  obtain ⟨path, s', located, second, hpath, hcf₁, _hsecond,
      _hne, _hcf₂, hx₁, hx₂⟩ :=
    contextFork_success main qb (Sum.inr ()) cf hsup
  have hs' : s' = s := by
    apply Option.some.inj
    calc
      some s' = cf (PFunctor.FreeM.output main path) := hcf₁.symm
      _ = cf x₁ := by rw [hx₁]
      _ = some s := h₁
  subst s'
  let commonLog : QueryLog (wrappedSpec L) := located.occurrence.before
  have hfirst := replayPathResult_mem_support_replayFirstRun main path hpath
  have hsecond := replayPathResult_mem_support_replayFirstRun main second.path
    (mem_support_replayFirstPath main second.path)
  have hxlog₁ : (x₁, (replayPathResult main path).2) ∈
      support (replayFirstRun main) := by
    simpa [replayPathResult, pathLogResult, hx₁] using hfirst
  have hxlog₂ : (x₂, (replayPathResult main second.path).2) ∈
      support (replayFirstRun main) := by
    simpa [replayPathResult, pathLogResult, hx₂] using hsecond
  have hlog₁ : (replayPathResult main path).2 =
      commonLog ++
        (⟨Sum.inr (), located.completion.answer⟩ ::
          (replayPathResult (located.occurrence.resume
            located.completion.answer) located.completion.suffix).2) := by
    have htrace := congrArg
      (fun p : PFunctor.FreeM.Path main =>
        (show QueryLog (wrappedSpec L) from
          PFunctor.FreeM.Path.trace main p)) located.path_eq
    calc
      (replayPathResult main path).2
          = (replayPathResult main located.completion.path).2 := htrace.symm
      _ = _ := by
        change PFunctor.FreeM.Path.trace main located.completion.path =
          List.append
            (show PFunctor.TraceList (wrappedSpec L).toPFunctor from
              commonLog)
            (⟨Sum.inr (), located.completion.answer⟩ ::
              PFunctor.FreeM.Path.trace
                (located.occurrence.resume located.completion.answer)
                located.completion.suffix)
        unfold commonLog
        exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
          located.occurrence located.completion.answer
            located.completion.suffix
  have hlog₂ : (replayPathResult main second.path).2 =
      commonLog ++
        (⟨Sum.inr (), second.answer⟩ ::
          (replayPathResult (located.occurrence.resume second.answer)
            second.suffix).2) := by
    change PFunctor.FreeM.Path.trace main second.path =
      List.append
        (show PFunctor.TraceList (wrappedSpec L).toPFunctor from
          commonLog)
        (⟨Sum.inr (), second.answer⟩ ::
          PFunctor.FreeM.Path.trace
            (located.occurrence.resume second.answer) second.suffix)
    unfold commonLog
    exact PFunctor.FreeM.Cursor.Occurrence.trace_plug
      located.occurrence second.answer second.suffix
  have htakeEq := runTrace_queryLog_take_eq C vc chk A ckVC
    (x₁ := x₁) (x₂ := x₂)
    (outerLog₁ := (replayPathResult main path).2)
    (outerLog₂ := (replayPathResult main second.path).2)
    hxlog₁ hxlog₂
    (p := commonLog)
    (v₁ := located.completion.answer) (v₂ := second.answer)
    (rest₁ := (replayPathResult (located.occurrence.resume
      located.completion.answer) located.completion.suffix).2)
    (rest₂ := (replayPathResult (located.occurrence.resume second.answer)
      second.suffix).2) hlog₁ hlog₂
  have hprefixCount : commonLog.countQ
      (fun x => x = Sum.inr ()) = (↑s : ℕ) := by
    calc
      commonLog.countQ (fun x => x = Sum.inr ()) =
          PFunctor.TraceList.occurrences (P := (wrappedSpec L).toPFunctor)
            (Sum.inr ())
            (show PFunctor.TraceList (wrappedSpec L).toPFunctor from
              commonLog) := QueryLog.countQ_eq_occurrences commonLog (Sum.inr ())
      _ = (↑s : ℕ) := by
        simp [commonLog]
  rw [hprefixCount] at htakeEq
  refine ⟨?_, htakeEq⟩
  have htgt₁ : x₁.queryLog[(↑s : ℕ)]? = some x₁.com :=
    forkPoint_getElem?_eq_some_com h₁
  have htgt₂ : x₂.queryLog[(↑s : ℕ)]? = some x₂.com :=
    forkPoint_getElem?_eq_some_com h₂
  have hgetElemTake (l : List ComVC) :
      (l.take ((↑s : ℕ) + 1))[(↑s : ℕ)]? = l[(↑s : ℕ)]? :=
    List.getElem?_take_of_lt (Nat.lt_succ_self _)
  apply Option.some.inj
  rw [← htgt₁, ← htgt₂, ← hgetElemTake x₁.queryLog,
    ← hgetElemTake x₂.queryLog, htakeEq]

end lockstep

end CommittedSoundness

end PqDas
