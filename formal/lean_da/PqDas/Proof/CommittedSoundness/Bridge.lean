/-
# Bridge between the two formulations of the committed soundness game

`niCommittedSoundnessExp` interprets the game with the caching random oracle
implemented directly over plain probabilistic computations (`romImpl`,
cf. `RomRuntime`). The forking analysis instead uses `CommittedSoundness.runTrace`, where
the same caching logic (`CommittedSoundness.roImpl`) draws its fresh answers from a
*counted* challenge oracle of the wrapped spec, interpreted uniformly. This
file proves the two agree: the simulations differ only in where the uniform
entropy is drawn from, so the value distributions coincide
(`evalDistEq_fst_run_wrapped`).

The one-step helpers below are continuation-parameterized: each states how a
single simulated query composed with an arbitrary continuation unfolds, so
that rewriting never mixes differently-spelled (definitionally equal) range
types.

Ported from b-wagn/fv-pq-da at 4475179c, modified for VCVio afa6593.
-/
import PqDas.Proof.CommittedSoundness.Fork
import VCVio.OracleComp.EvalDist.Sum

open OracleComp OracleSpec ENNReal

namespace PqDas

namespace CommittedSoundness

variable {Γ Λ : Type} {k n : ℕ} {CkVC ComVC Opn L : Type}

section bridge

variable [DecidableEq ComVC] [SampleableType L] [Fintype L] [Inhabited L]

/-- Uniform interpretation of the counted challenge oracle. Opt-in per
`UniformAnswerMeasure`'s design; combined with the ambient `unifSpec` instance this
interprets the whole wrapped spec uniformly. -/
noncomputable scoped instance : UniformAnswerMeasure ((Unit →ₒ L) : OracleSpec Unit) :=
  UniformAnswerMeasure.ofFiniteNonempty _

/-! #### One-step unfolding helpers -/

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_run_query_bind {α : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (mx : (unifSpec + (ComVC →ₒ L)).Range t → OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (st : SimState ComVC L) :
    (simulateQ (unifForward ComVC L + roImpl ComVC L)
        (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= mx)).run st =
      ((unifForward ComVC L + roImpl ComVC L) t).run st >>= fun x =>
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (mx x.1)).run x.2 := by
  rw [simulateQ_query_bind, StateT.run_bind]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_run_query_bind {α : Type}
    (t : (unifSpec + (ComVC →ₒ L)).Domain)
    (mx : (unifSpec + (ComVC →ₒ L)).Range t → OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (cache : (ComVC →ₒ L).QueryCache) :
    simulateRomWithCache cache (liftM ((unifSpec + (ComVC →ₒ L)).query t) >>= mx) =
      ((romImpl ComVC L) t).run cache >>= fun x =>
        simulateRomWithCache x.2 (mx x.1) := by
  simp only [simulateRomWithCache, simulateQ_query_bind, StateT.run'_eq, StateT.run_bind,
    map_bind]
  rfl

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_inl {β : Type} (i : ℕ) (st : SimState ComVC L)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inl i) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inl i)).run st >>= K =
      (query (spec := wrappedSpec L) (Sum.inl i)) >>= fun u => K (u, st) := by
  simp only [QueryImpl.add_apply_inl, unifForward]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_step_inl {β : Type} (i : ℕ) (cache : (ComVC →ₒ L).QueryCache)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inl i) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inl i)).run cache >>= K =
      (query (spec := unifSpec) i) >>= fun u => K (u, cache) := by
  simp only [romImpl, QueryImpl.add_apply_inl]
  rfl

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_hit {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC} {v : L}
    (h : cache com = some v)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (cache, log) >>= K =
      K (v, cache, log) := by
  show (roImpl ComVC L com).run (cache, log) >>= K = _
  rw [roImpl_run_hit h, pure_bind]

omit [Fintype L] [Inhabited L] in
private lemma rom_step_hit {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {v : L} (h : cache com = some v)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inr com)).run cache >>= K = K (v, cache) := by
  show ((randomOracle : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) com).run cache >>= K = _
  rw [randomOracle_run_hit h, pure_bind]

omit [SampleableType L] [Fintype L] [Inhabited L] in
private lemma wrapped_step_miss {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} {log : List ComVC}
    (h : cache com = none)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × SimState ComVC L →
      OracleComp (wrappedSpec L) β) :
    ((unifForward ComVC L + roImpl ComVC L) (Sum.inr com)).run (cache, log) >>= K =
      (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp (wrappedSpec L) L) >>=
        fun u => K (u, cache.cacheQuery com u, log ++ [com]) := by
  show (roImpl ComVC L com).run (cache, log) >>= K = _
  simp only [roImpl, StateT.run_bind, StateT.run_get, pure_bind, h, StateT.run_set,
    bind_assoc, StateT.run_monadLift]
  rfl

omit [Fintype L] [Inhabited L] in
private lemma rom_step_miss {β : Type} {com : ComVC}
    {cache : (ComVC →ₒ L).QueryCache} (h : cache com = none)
    (K : (unifSpec + (ComVC →ₒ L)).Range (Sum.inr com) × (ComVC →ₒ L).QueryCache →
      ProbComp β) :
    ((romImpl ComVC L) (Sum.inr com)).run cache >>= K =
      ($ᵗ L) >>= fun u => K (u, cache.cacheQuery com u) := by
  show ((randomOracle : QueryImpl (ComVC →ₒ L)
      (StateT ((ComVC →ₒ L).QueryCache) ProbComp)) com).run cache >>= K = _
  simp only [randomOracle, QueryImpl.withCaching_apply, StateT.run_bind, StateT.run_get,
    pure_bind, h, uniformSampleImpl, liftM, MonadLiftT.monadLift, MonadLift.monadLift,
    StateT.run_lift, StateT.run_modifyGet, bind_assoc]

omit [SampleableType L] in
/-- A uniform-sampling query of the wrapped spec is distributed as the same
query of `unifSpec`. -/
private lemma evalDistEq_query_inl (i : ℕ) :
    (query (spec := wrappedSpec L) (Sum.inl i) :
        OracleComp (wrappedSpec L) ((wrappedSpec L).Range (Sum.inl i))) =ᵈ
      (query (spec := unifSpec) i : ProbComp (unifSpec.Range i)) := by
  intro p
  classical
  rw [prEvent_query_eq_card_div (spec := wrappedSpec L), prEvent_query_eq_card_div (spec := unifSpec)]
  rfl

/-- The counted challenge oracle is distributed as a uniform sample. -/
private lemma evalDistEq_query_inr :
    (liftM ((wrappedSpec L).query (Sum.inr ())) : OracleComp (wrappedSpec L) L) =ᵈ
      ($ᵗ L : ProbComp L) := by
  intro p
  classical
  rw [prEvent_liftM_query_eq_card_div (spec := wrappedSpec L) (Sum.inr ()),
    SampleableType.prEvent_uniformSample]
  rfl

omit [SampleableType L] in
/-- `pure` is distributed alike in the wrapped world and in `ProbComp`. -/
private lemma evalDistEq_pure {α : Type} (x : α) :
    (pure x : OracleComp (wrappedSpec L) α) =ᵈ (pure x : ProbComp α) := by
  intro p
  classical
  rw [prEvent_pure, prEvent_pure]

/-- The two caching simulations of a computation in the adversary's oracle
world, drawing fresh answers from the wrapped spec's counted challenge
oracle (left) or from plain uniform sampling (right), produce identically
distributed values, for any common initial cache and any initial log. -/
theorem evalDistEq_fst_run_wrapped {α : Type}
    (prog : OracleComp (unifSpec + (ComVC →ₒ L)) α)
    (cache : (ComVC →ₒ L).QueryCache) (log : List ComVC) :
    Prod.fst <$> (simulateQ (unifForward ComVC L + roImpl ComVC L) prog).run (cache, log) =ᵈ
      simulateRomWithCache cache prog := by
  induction prog using OracleComp.inductionOn generalizing cache log with
  | pure x =>
      simpa [simulateRomWithCache, simulateQ_pure, StateT.run_pure, StateT.run'_eq] using
        evalDistEq_pure x
  | query_bind t mx ih =>
      rw [wrapped_run_query_bind, rom_run_query_bind, map_bind]
      cases t with
      | inl i =>
          rw [wrapped_step_inl, rom_step_inl]
          exact (evalDistEq_query_inl i).bind fun u => ih u cache log
      | inr com =>
          cases hcache : cache com with
          | some v =>
              rw [wrapped_step_hit hcache, rom_step_hit hcache]
              exact ih v cache log
          | none =>
              rw [wrapped_step_miss hcache, rom_step_miss hcache]
              exact evalDistEq_query_inr.bind fun u =>
                ih u (cache.cacheQuery com u) (log ++ [com])

/-- The winning probability of the non-interactive committed soundness game is
the expectation, over the commitment key, of the probability that the recorded
trace of the wrapped game wins. -/
theorem niCommittedSoundnessExp_true_eq_tsum [Fintype Γ] [DecidableEq Λ]
    (C : ErasureCode Γ Λ k n) (vc : VectorCommitment Λ n CkVC ComVC Opn)
    (chk : CodeChecker Λ n L) (A : NiCsAdv Λ n CkVC ComVC L) :
    niCommittedSoundnessExp C vc chk A {true} =
      ∑' ckVC : CkVC, Pr{let x ← vc.setup}[x = ckVC] *
        Pr{let t ← runTrace C vc chk A ckVC}[t.win = true] := by
  unfold niCommittedSoundnessExp
  rw [← evalDist_simulateRom, evalDist_singleton_eq_prEvent]
  simp only [simulateRom]
  rw [show (do
      let ckVC ← (liftM vc.setup : OracleComp (unifSpec + (ComVC →ₒ L)) CkVC)
      let (com, c) ← A ckVC
      let l ← HasQuery.query (spec := (ComVC →ₒ L)) com
      return (decide (c ∉ C.code) && chk.check l c && decide (vc.commit ckVC c = com))) =
    (liftM vc.setup : OracleComp (unifSpec + (ComVC →ₒ L)) CkVC) >>= fun ckVC =>
      winOn C vc chk ckVC <$> wrappedAdv A ckVC from by
    simp only [wrappedAdv, winOn, map_bind, monad_norm, Function.comp_apply]]
  rw [simulateRomWithCache_liftM_bind, OracleComp.prEvent_bind_eq_tsum]
  refine tsum_congr fun ckVC => ?_
  refine congrArg _ ?_
  rw [simulateRomWithCache_map, prEvent_map]
  refine ((evalDistEq_fst_run_wrapped (wrappedAdv A ckVC) ∅ []).symm.prEvent_eq _).trans ?_
  rw [prEvent_map]
  unfold runTrace
  rw [show (do
      let (out, st) ← StateT.run
        (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)) (∅, [])
      pure { com := out.1, vec := out.2.1, chal := out.2.2, roCache := st.1,
             queryLog := st.2, win := winOn C vc chk ckVC out }) =
    (fun z => (⟨z.1.1, z.1.2.1, z.1.2.2, z.2.1, z.2.2, winOn C vc chk ckVC z.1⟩ :
        Trace Λ n ComVC L)) <$>
      (simulateQ (unifForward ComVC L + roImpl ComVC L) (wrappedAdv A ckVC)).run (∅, [])
    from by simp only [map_eq_bind_pure_comp]; rfl]
  rw [prEvent_map]

end bridge

end CommittedSoundness

end PqDas
