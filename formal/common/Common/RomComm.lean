module

public import Common.Prob
public import Common.Defs

@[expose] public section

/-!
# Random-oracle queries commute

In the random oracle model (`hs.romImpl`: uniform sampling forwarded, `hs` answered by the lazily
sampled random oracle), a hash query whose answer is not used can be moved anywhere: running
`query t` and then `oa` gives the same joint distribution of output and final cache as running
`oa` and then `query t` (`run_query_bind_evalDistEq`). This is the eager/lazy sampling principle
for random oracles: the random function is fixed from the start, and *when* a point is first
queried does not matter.

Consequences used by the indifferentiability proof:

* discarded queries can be postponed to the end of a run, where their answers are fresh
  (`run_queries_bind_evalDistEq`);
* a query at a point that is already cached changes nothing (`run_bind_query_of_cached`).
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)] {α : Type}

/-- One step of the lazy random oracle at `t` from the cache `c`: the cached answer, or a fresh
uniform answer recorded in the cache. -/
def roStep (t : ι) (c : hs.QueryCache) : ProbComp (hs.Range t × hs.QueryCache) :=
  match c t with
  | some u => pure (u, c)
  | none => ($ᵗ hs.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u)

theorem roStep_of_some {t : ι} {c : hs.QueryCache} {u : hs.Range t} (h : c t = some u) :
    roStep t c = pure (u, c) := by
  simp [roStep, h]

theorem roStep_of_none {t : ι} {c : hs.QueryCache} (h : c t = none) :
    roStep t c = (($ᵗ hs.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u)) := by
  simp [roStep, h]

/-- The hash summand of `romImpl` is one random-oracle step. -/
theorem romImpl_inr_run (t : ι) (c : hs.QueryCache) :
    (hs.romImpl (.inr t)).run c = roStep t c := by
  rw [romImpl_apply_inr, randomOracle.run_eq]; rfl

/-- The run of a hash query is one random-oracle step. -/
theorem run_hq (t : ι) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (hq t)).run c = roStep t c := by
  rw [hq, roSim.simulateQ_liftM_spec_query, randomOracle.run_eq]; rfl

/-- A hash query keeps every cached answer and caches its own answer. -/
theorem le_of_mem_support_roStep (t : ι) (c : hs.QueryCache) {z : hs.Range t × hs.QueryCache}
    (hz : z ∈ support (roStep t c)) : c ≤ z.2 ∧ z.2 t = some z.1 := by
  rcases h : c t with _ | u
  · rw [roStep_of_none h] at hz
    simp only [support_bind, support_uniformSample, Set.mem_univ, support_pure,
      Set.iUnion_true, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, rfl⟩ := hz
    exact ⟨QueryCache.le_cacheQuery _ h, by simp⟩
  · rw [roStep_of_some h] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨le_rfl, h⟩

/-- A random-oracle-model run only adds cached answers. -/
theorem le_of_mem_support_run (oa : OracleComp (unifSpec + hs) α) (c : hs.QueryCache)
    {z : α × hs.QueryCache} (hz : z ∈ support ((simulateQ hs.romImpl oa).run c)) : c ≤ z.2 := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz; exact le_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    refine le_trans ?_ (ih w.1 w.2 hz)
    rcases t with n | t
    · rw [roSim.run_apply_inl] at hw
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨u, -, rfl⟩ := hw
      exact le_rfl
    · rw [romImpl_inr_run] at hw
      exact (le_of_mem_support_roStep t c hw).1

theorem roStep_cacheQuery_self (s : ι) (c : hs.QueryCache) (u : hs.Range s) :
    roStep s (c.cacheQuery s u) = pure (u, c.cacheQuery s u) :=
  roStep_of_some (QueryCache.cacheQuery_self c s u)

theorem roStep_cacheQuery_of_none {s t : ι} {c : hs.QueryCache} (h : c t = none) (hst : s ≠ t)
    (u : hs.Range s) :
    roStep t (c.cacheQuery s u) =
      (($ᵗ hs.Range t) >>= fun x ↦ pure (x, (c.cacheQuery s u).cacheQuery t x)) :=
  roStep_of_none (by rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hst)]; exact h)

theorem roStep_cacheQuery_of_some {s t : ι} {c : hs.QueryCache} {v : hs.Range t}
    (h : c t = some v) (hst : s ≠ t) (u : hs.Range s) :
    roStep t (c.cacheQuery s u) = pure (v, c.cacheQuery s u) :=
  roStep_of_some (by rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm hst)]; exact h)

/-- Two hash queries commute: their answers and the final cache have the same joint distribution
in either order. -/
theorem roStep_roStep_comm (s t : ι) (c : hs.QueryCache) {β : Type}
    (f : hs.Range s → hs.Range t → hs.QueryCache → ProbComp β) :
    (roStep s c >>= fun v ↦ roStep t v.2 >>= fun w ↦ f v.1 w.1 w.2) =ᵈ
      (roStep t c >>= fun w ↦ roStep s w.2 >>= fun v ↦ f v.1 w.1 v.2) := by
  by_cases hst : s = t
  · subst hst
    rcases h : c s with _ | u
    · simp only [roStep_of_none h, bind_assoc, pure_bind, roStep_cacheQuery_self]
      exact EvalDistEq.rfl
    · simp only [roStep_of_some h, pure_bind]
      exact EvalDistEq.rfl
  · rcases hs' : c s with _ | u <;> rcases ht' : c t with _ | v
    · simp only [roStep_of_none hs', roStep_of_none ht', bind_assoc, pure_bind,
        roStep_cacheQuery_of_none ht' hst, roStep_cacheQuery_of_none hs' (Ne.symm hst)]
      refine (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun x ↦
        EvalDistEq.bind_right _ fun u ↦ ?_)
      rw [QueryCache.cacheQuery_comm _ (Ne.symm hst)]
    · simp only [roStep_of_none hs', roStep_of_some ht', bind_assoc, pure_bind,
        roStep_cacheQuery_of_some ht' hst]
      exact EvalDistEq.rfl
    · simp only [roStep_of_some hs', roStep_of_none ht', bind_assoc, pure_bind,
        roStep_cacheQuery_of_some hs' (Ne.symm hst)]
      exact EvalDistEq.rfl
    · simp only [roStep_of_some hs', roStep_of_some ht', pure_bind]
      exact EvalDistEq.rfl

/-- The run of `oa` after a discarded hash query at `t`. -/
private def lhsRun (t : ι) (oa : OracleComp (unifSpec + hs) α) (c : hs.QueryCache) :
    ProbComp (α × hs.QueryCache) :=
  roStep t c >>= fun w ↦ (simulateQ hs.romImpl oa).run w.2

/-- The run of `oa` followed by a discarded hash query at `t`. -/
private def rhsRun (t : ι) (oa : OracleComp (unifSpec + hs) α) (c : hs.QueryCache) :
    ProbComp (α × hs.QueryCache) :=
  (simulateQ hs.romImpl oa).run c >>= fun z ↦ roStep t z.2 >>= fun w ↦ pure (z.1, w.2)

private theorem lhsRun_eq_rhsRun (t : ι) (oa : OracleComp (unifSpec + hs) α)
    (c : hs.QueryCache) : lhsRun t oa c =ᵈ rhsRun t oa c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a => simp [lhsRun, rhsRun]
  | query_bind q k ih =>
    simp only [lhsRun, rhsRun, simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc] at ih ⊢
    rcases q with n | s
    · simp only [roSim.run_apply_inl, bind_map_left]
      exact (EvalDistEq.bind_bind_swap _ _ _).trans (EvalDistEq.bind_right _ fun u ↦ ih u c)
    · simp only [romImpl_inr_run]
      exact (roStep_roStep_comm s t c fun v _ c' ↦
        (simulateQ hs.romImpl (k v)).run c').symm.trans
          (EvalDistEq.bind_right _ fun v ↦ ih v.1 v.2)

/-- **Random-oracle queries commute.** Querying `t` before `oa` and discarding the answer gives
the same joint distribution of output and final cache as querying `t` after `oa`. -/
theorem run_query_bind_evalDistEq (t : ι) (oa : OracleComp (unifSpec + hs) α)
    (c : hs.QueryCache) :
    (simulateQ hs.romImpl (hq t >>= fun _ ↦ oa)).run c =ᵈ
      (simulateQ hs.romImpl (oa >>= fun a ↦ hq t >>= fun _ ↦ pure a)).run c := by
  have e1 : (simulateQ hs.romImpl (hq t >>= fun _ ↦ oa)).run c = lhsRun t oa c := by
    simp only [simulateQ_bind, StateT.run_bind, run_hq, lhsRun]
  have e2 : (simulateQ hs.romImpl (oa >>= fun a ↦ hq t >>= fun _ ↦ pure a)).run c =
      rhsRun t oa c := by
    simp only [simulateQ_bind, StateT.run_bind, run_hq, rhsRun, simulateQ_pure, StateT.run_pure]
  rw [e1, e2]
  exact lhsRun_eq_rhsRun t oa c

end Common

namespace Common

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]

/-- One step of the random oracle model: a uniform draw (cache unchanged) or a random-oracle
step. -/
abbrev romStep (q : (unifSpec + hs).Domain) (c : hs.QueryCache) :
    ProbComp ((unifSpec + hs).Range q × hs.QueryCache) :=
  (hs.romImpl q).run c

/-- Any two steps of the random oracle model commute. -/
theorem romStep_romStep_comm (q q' : (unifSpec + hs).Domain) (c : hs.QueryCache) {β : Type}
    (f : (unifSpec + hs).Range q → (unifSpec + hs).Range q' → hs.QueryCache → ProbComp β) :
    (romStep q c >>= fun v ↦ romStep q' v.2 >>= fun w ↦ f v.1 w.1 w.2) =ᵈ
      (romStep q' c >>= fun w ↦ romStep q w.2 >>= fun v ↦ f v.1 w.1 v.2) := by
  rcases q with n | s <;> rcases q' with n' | t
  · simp only [romStep, roSim.run_apply_inl, bind_map_left]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [romStep, roSim.run_apply_inl, bind_map_left, romImpl_inr_run]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [romStep, roSim.run_apply_inl, bind_map_left, romImpl_inr_run]
    exact EvalDistEq.bind_bind_swap _ _ _
  · simp only [romStep, romImpl_inr_run]
    exact roStep_roStep_comm s t c f

/-- A single query commutes with any computation that does not use its answer. -/
theorem run_query_bind_comm (q : (unifSpec + hs).Domain) {γ δ : Type}
    (Y : OracleComp (unifSpec + hs) γ)
    (V : (unifSpec + hs).Range q → γ → OracleComp (unifSpec + hs) δ) (c : hs.QueryCache) :
    (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a ↦
        Y >>= fun r ↦ V a r)).run c =ᵈ
      (simulateQ hs.romImpl (Y >>= fun r ↦
        liftM ((unifSpec + hs).query q) >>= fun a ↦ V a r)).run c := by
  induction Y using OracleComp.inductionOn generalizing c with
  | pure r => simp
  | query_bind q' k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, bind_assoc] at ih ⊢
    refine (romStep_romStep_comm q q' c fun a a' c' ↦
      (simulateQ hs.romImpl (k a')).run c' >>= fun p ↦
        (simulateQ hs.romImpl (V a p.1)).run p.2).trans
      (EvalDistEq.bind_right _ fun w ↦ ?_)
    exact ih w.1 w.2

/-- **Independent computations commute** in the random oracle model: running `X` then `Y`
gives the joint distribution of outputs and final cache of running `Y` then `X`. -/
theorem run_bind_bind_comm {β γ δ : Type} (X : OracleComp (unifSpec + hs) β)
    (Y : OracleComp (unifSpec + hs) γ) (W : β → γ → OracleComp (unifSpec + hs) δ)
    (c : hs.QueryCache) :
    (simulateQ hs.romImpl (X >>= fun b ↦ Y >>= fun r ↦ W b r)).run c =ᵈ
      (simulateQ hs.romImpl (Y >>= fun r ↦ X >>= fun b ↦ W b r)).run c := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure b => simp
  | query_bind q k ih =>
    calc (simulateQ hs.romImpl ((liftM ((unifSpec + hs).query q) >>= k) >>= fun b ↦
          Y >>= fun r ↦ W b r)).run c
        = (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a ↦
            k a >>= fun b ↦ Y >>= fun r ↦ W b r)).run c := by rw [bind_assoc]
      _ =ᵈ (simulateQ hs.romImpl (liftM ((unifSpec + hs).query q) >>= fun a ↦
            Y >>= fun r ↦ k a >>= fun b ↦ W b r)).run c := by
          simp only [simulateQ_bind, StateT.run_bind]
          exact EvalDistEq.bind_right _ fun w ↦ by
            have := ih w.1 w.2
            simp only [simulateQ_bind, StateT.run_bind] at this
            exact this
      _ =ᵈ (simulateQ hs.romImpl (Y >>= fun r ↦ liftM ((unifSpec + hs).query q) >>= fun a ↦
            k a >>= fun b ↦ W b r)).run c :=
          run_query_bind_comm q Y (fun a r ↦ k a >>= fun b ↦ W b r) c
      _ = _ := by simp only [bind_assoc]

end Common
