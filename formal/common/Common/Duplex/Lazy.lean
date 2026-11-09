module

public import Common.Duplex.Defs
public import Common.Defs

@[expose] public section

/-!
# The simulator with lazy challenges is the random function

With the challenges `G` a random oracle on `(r, j)` (`gaP`), the simulator's fresh answers are
uniform: a programmed answer `build (G r j, w)` uses a challenge never used before, so `G r j` is
fresh, and `build` of two uniform parts is uniform. So running any computation with `F` answered
by the simulator is running it with `F` a random function (`run'_simImpl_evalDistEq`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The two-oracle cache a simulated state shows: `H` from the cache, `F` from the log. -/
def mergeCache (c : (GSpec Msg Dg Root Z n).QueryCache) (s : SimSt Dg St Root n) :
    (hfSpec Msg Dg St).QueryCache :=
  QueryCache.ofFn fun
    | .inl m => c (.inl m)
    | .inr x => s.answer x

end Common.SeedDuplex

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The projection of the simulated world's state. -/
def projSC (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) :
    (hfSpec Msg Dg St).QueryCache := mergeCache sc.2 sc.1

theorem projSC_log {s s' : SimSt Dg St Root n} (h : s'.log = s.log)
    (c : (GSpec Msg Dg Root Z n).QueryCache) : projSC (s', c) = projSC (s, c) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | x
  · rfl
  · simp [projSC, mergeCache, SimSt.answer, h]

@[simp] theorem projSC_x0 (s : SimSt Dg St Root n) (o : Option St) (d : Option Dg)
    (c : (GSpec Msg Dg Root Z n).QueryCache) :
    projSC ({ s with x0 := o, iv := d }, c) = projSC (s, c) := projSC_log rfl c

theorem projSC_cacheQuery_inl (s : SimSt Dg St Root n) (c : (GSpec Msg Dg Root Z n).QueryCache)
    (m : Msg) (u : Dg) :
    projSC (s, c.cacheQuery (.inl m) u) = (projSC (s, c)).cacheQuery (.inl m) u := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | x
  · by_cases h : m' = m
    · subst h; simp [projSC, mergeCache]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp [projSC, mergeCache, QueryCache.cacheQuery_of_ne _ _ (show (Sum.inl m' : Msg ⊕ _) ≠ .inl m
        by simpa using h)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    rfl

theorem projSC_cacheQuery_inr (s : SimSt Dg St Root n) (c : (GSpec Msg Dg Root Z n).QueryCache)
    (rj : Root × Fin n) (z : Z) :
    projSC (s, c.cacheQuery (.inr rj) z) = projSC (s, c) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | x
  · simp only [projSC, mergeCache, QueryCache.ofFn_apply]
    rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · rfl

theorem projSC_record (s : SimSt Dg St Root n) (c : (GSpec Msg Dg Root Z n).QueryCache)
    (x y : St) (lbl : Option (Root × Fin n)) :
    projSC (s.record D x y lbl, c) = (projSC (s, c)).cacheQuery (.inr x) y := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | x'
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
    rfl
  · by_cases h : x' = x
    · subst h
      simp [projSC, mergeCache, SimSt.answer, SimSt.record]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
      simp only [projSC, mergeCache, SimSt.answer, SimSt.record, QueryCache.ofFn_apply]
      rw [List.find?_cons_of_neg (by simpa [eq_comm] using h)]

omit [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W] in
theorem unifFwdImpl_run' {ι : Type} (hs : OracleSpec ι) (k : ℕ) (c : hs.QueryCache) :
    (unifFwdImpl hs k).run c = (·, c) <$> (unifSpec.query k : ProbComp (Fin (k + 1))) := by
  simpa using unifFwdImpl.simulateQ_run (hashSpec := hs) (unifSpec.query k : ProbComp _) c

omit [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp] [Fintype St]
  [Fintype Z] [Fintype W] [SampleableType Dg] in
/-- A uniform challenge and a uniform rest make a uniform answer. -/
theorem uniform_build :
    (do let z ← ($ᵗ Z : ProbComp Z); let w ← ($ᵗ W : ProbComp W); pure (D.build (z, w))) =ᵈ
      ($ᵗ St : ProbComp St) := by
  refine _root_.EvalDistEq.of_forall_prEvent_eq fun p ↦ ?_
  have h := SampleableType.prEvent_uniformSample_pair_of_bijective
    (g := fun z w ↦ D.build (z, w)) (γ := St) (by
      simpa [Function.uncurry_def] using D.build.bijective) p
  simpa [prEvent_norm] using h

/-- The fresh answers of the simulator: the cache changes only in the challenges, and the answer
is uniform when the challenges in the cache are used ones. -/
theorem freshAns_run (s : SimSt Dg St Root n) (x : St) (c : (GSpec Msg Dg Root Z n).QueryCache)
    (hinv : ∀ r j, c (.inr (r, j)) ≠ none → (r, j) ∈ s.used) :
    (fun z ↦ (z.1.1, projSC (s, z.2))) <$>
        (simulateQ (GSpec Msg Dg Root Z n).romImpl (freshAns D gaP s x)).run c =ᵈ
      (fun y ↦ (y, projSC (s, c))) <$> ($ᵗ St : ProbComp St) := by
  unfold freshAns
  split
  · next r j hrj =>
    split_ifs with hu
    · simp [simulateQ_map, OracleSpec.simulateQ_romImpl_liftM_run, Functor.map_map]
    · have hc : c (.inr (r, j)) = none := by
        by_contra h; exact hu (hinv r j h)
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        OracleSpec.simulateQ_romImpl_liftM_run]
      rw [show (simulateQ (GSpec Msg Dg Root Z n).romImpl (gaP r j)).run c =
        roStep (.inr (r, j)) c from run_hq _ _, roStep_of_none hc]
      simp only [bind_assoc, pure_bind, map_bind, bind_map_left, map_pure, projSC_cacheQuery_inr]
      have := (uniform_build D).map (fun y ↦ (y, projSC (s, c)))
      simpa [map_bind] using this
  · simp [simulateQ_map, OracleSpec.simulateQ_romImpl_liftM_run, Functor.map_map]

theorem sim_step (t : (Rom2 Msg Dg St).Domain) (s : SimSt Dg St Root n)
    (c : (GSpec Msg Dg Root Z n).QueryCache)
    (hinv : ∀ r j, c (.inr (r, j)) ≠ none → (r, j) ∈ s.used) :
    Prod.map id projSC <$> ((foldRO (simImpl D hP gaP)) t).run (s, c) =ᵈ
      ((hfSpec Msg Dg St).romImpl t).run (projSC (s, c)) := by
  rw [foldRO_run]
  rcases t with k | m | x
  · simp only [simImpl]
    simp [unifFwdImpl_run', Functor.map_map]
  · simp only [simImpl, StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure]
    rw [show ((hfSpec Msg Dg St).romImpl (.inr (.inl m))).run (projSC (s, c)) =
      roStep (.inl m) (projSC (s, c)) from romImpl_inr_run _ _]
    rw [show (simulateQ (GSpec Msg Dg Root Z n).romImpl (hP m)).run c = roStep (.inl m) c from
      run_hq _ _]
    have hp : projSC (s, c) (.inl m) = c (.inl m) := rfl
    rcases h : c (.inl m) with _ | v
    · rw [roStep_of_none h, roStep_of_none (hp.trans h)]
      simp only [bind_assoc, pure_bind, map_bind, map_pure, Prod.map_apply, id_eq]
      refine (EvalDistEq.bind_right _ fun u ↦ ?_)
      split_ifs <;>
        simp [projSC_cacheQuery_inl]
    · rw [roStep_of_some h, roStep_of_some (hp.trans h)]
      simp only [pure_bind, map_pure, Prod.map_apply, id_eq]
      split_ifs <;> simp
  · simp only [simImpl, StateT.run_mk]
    have hp : projSC (s, c) (.inr x) = s.answer x := rfl
    rw [show ((hfSpec Msg Dg St).romImpl (.inr (.inr x))).run (projSC (s, c)) =
      roStep (.inr x) (projSC (s, c)) from romImpl_inr_run _ _]
    rcases h : s.answer x with _ | y
    · rw [roStep_of_none (hp.trans h)]
      simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure, map_bind,
        map_pure, Prod.map_apply, id_eq, projSC_record]
      have key := (freshAns_run D s x c hinv).map (fun p ↦ (p.1, p.2.cacheQuery (.inr x) p.1))
      simp only [Functor.map_map] at key
      rw [← bind_pure_comp] at key
      simpa [map_eq_bind_pure_comp] using key
    · rw [roStep_of_some (hp.trans h)]
      simp

end Common.SeedDuplex

namespace Common.SeedDuplex

variable {Msg Dg St Root Z W Cp : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq St] [DecidableEq Root] [DecidableEq Cp]
  [SampleableType Dg] [SampleableType St] [SampleableType Z] [SampleableType W]
  [Fintype St] [Fintype Z] [Fintype W]
  (D : DuplexSpec Msg Dg St Root Z W Cp n)

/-- The simulator's invariant: a cached challenge is a used one. -/
def CacheUsed (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) : Prop :=
  ∀ r j, sc.2 (.inr (r, j)) ≠ none → (r, j) ∈ sc.1.used

theorem used_record (s : SimSt Dg St Root n) (x y : St) (lbl : Option (Root × Fin n)) :
    (s.record D x y lbl).used = lbl.toList ++ s.used := by
  cases lbl <;> simp [SimSt.used, SimSt.record]

theorem freshAns_cache (s : SimSt Dg St Root n) (x : St) (c : (GSpec Msg Dg Root Z n).QueryCache)
    {z} (hz : z ∈ support ((simulateQ (GSpec Msg Dg Root Z n).romImpl
      (freshAns D gaP s x)).run c)) (r : Root) (j : Fin n)
    (hrj : z.2 (.inr (r, j)) ≠ none) : c (.inr (r, j)) ≠ none ∨ z.1.2 = some (r, j) := by
  unfold freshAns at hz
  split at hz
  · next r' j' _ =>
    split_ifs at hz
    · simp [simulateQ_map, OracleSpec.simulateQ_romImpl_liftM_run] at hz
      obtain ⟨y, rfl⟩ := hz
      exact Or.inl hrj
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        OracleSpec.simulateQ_romImpl_liftM_run, mem_support_bind_iff, support_map, Set.mem_image,
        support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨v, hv, _, ⟨w, -, rfl⟩, rfl⟩ := hz
      rw [show (simulateQ (GSpec Msg Dg Root Z n).romImpl (gaP r' j')).run c =
        roStep (.inr (r', j')) c from run_hq _ _] at hv
      by_cases he : (r, j) = (r', j')
      · exact Or.inr (by simp [he])
      · left
        rcases hcm : c (.inr (r', j')) with _ | u
        · rw [roStep_of_none hcm] at hv
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
          obtain ⟨u, -, rfl⟩ := hv
          simpa [QueryCache.cacheQuery_of_ne _ _ (show (Sum.inr (r, j) : Msg ⊕ _) ≠
            .inr (r', j') by simpa using he)] using hrj
        · rw [roStep_of_some hcm] at hv
          simp only [support_pure, Set.mem_singleton_iff] at hv
          subst hv; exact hrj
  · simp [simulateQ_map, OracleSpec.simulateQ_romImpl_liftM_run] at hz
    obtain ⟨y, rfl⟩ := hz
    exact Or.inl hrj

theorem cacheUsed_step (t : (Rom2 Msg Dg St).Domain)
    (sc : SimSt Dg St Root n × (GSpec Msg Dg Root Z n).QueryCache) (h : CacheUsed sc)
    {z} (hz : z ∈ support (((foldRO (simImpl D hP gaP)) t).run sc)) : CacheUsed z.2 := by
  obtain ⟨s, c⟩ := sc
  rw [foldRO_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  intro r j hrj
  rcases t with k | m | x
  · simp only [simImpl] at hw
    simp [unifFwdImpl_run'] at hw
    obtain ⟨y, rfl⟩ := hw
    exact h r j hrj
  · simp only [simImpl, StateT.run_mk, simulateQ_bind, StateT.run_bind, simulateQ_pure,
      StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    rw [show (simulateQ (GSpec Msg Dg Root Z n).romImpl (hP m)).run c = roStep (.inl m) c from
      run_hq _ _] at hv
    have hc : v.2 (.inr (r, j)) = c (.inr (r, j)) := by
      rcases hcm : c (.inl m) with _ | u
      · rw [roStep_of_none hcm] at hv
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨u, -, rfl⟩ := hv
        exact QueryCache.cacheQuery_of_ne _ _ (by simp)
      · rw [roStep_of_some hcm] at hv
        simp only [support_pure, Set.mem_singleton_iff] at hv
        subst hv; rfl
    simp only at hrj ⊢
    rw [hc] at hrj
    split_ifs <;> exact h r j hrj
  · simp only [simImpl, StateT.run_mk] at hw
    rcases ha : s.answer x with _ | y
    · simp only [ha, simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
        mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      simp only [used_record]
      rcases freshAns_cache D s x c hv r j hrj with h1 | h1
      · exact List.mem_append_right _ (h r j h1)
      · simp [h1]
    · simp only [ha, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hw
      subst hw
      exact h r j hrj

/-- **The simulator with lazy challenges is the random function `F`**: running a computation of
the two-oracle model with `F` answered by the simulator (challenges `G` a random oracle on
`(r, j)`) is, in distribution, running it in the two-oracle random-oracle model. -/
theorem run'_simImpl_evalDistEq {α : Type} (X : OracleComp (Rom2 Msg Dg St) α) :
    (simulateQ (GSpec Msg Dg Root Z n).romImpl
        ((simulateQ (simImpl D hP gaP) X).run' SimSt.init)).run' ∅ =ᵈ
      (simulateQ (hfSpec Msg Dg St).romImpl X).run' ∅ := by
  rw [run'_simulateQ_foldRO]
  have h0 : projSC ((SimSt.init : SimSt Dg St Root n), (∅ : (GSpec Msg Dg Root Z n).QueryCache)) =
      ∅ := by
    refine QueryCache.ext fun t ↦ ?_
    rcases t with m | x <;> rfl
  rw [← h0]
  exact run'_simulateQ_evalDistEq_of_inv _ _ CacheUsed projSC
    (fun t sc h z hz ↦ cacheUsed_step D t sc h hz)
    (fun t sc h ↦ by obtain ⟨s, c⟩ := sc; exact sim_step D t s c h) X _
    (fun r j h ↦ absurd rfl h)

end Common.SeedDuplex
