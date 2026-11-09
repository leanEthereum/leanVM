module

public import Common.Indiff.Fresh

@[expose] public section

/-!
# Indifferentiability: the simulator over path values is the simulator

The simulator over path values (`idealTImpl`) draws a rooted node's value from the path oracle
`T`; the simulator (`simulator`) draws it uniformly. Since `T` is queried at most once per path
(`VStruct`), the two agree in distribution once the path oracle's cache is forgotten
(`idealTGame_evalDistEq_idealGame`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-- The random oracle part of an intermediate game's cache. -/
def roPart (c : ACache Msg Dg E C) : (roSpec Msg Dg).QueryCache :=
  QueryCache.ofFn fun m ↦ c (.inl m)

@[simp] theorem roPart_apply (c : ACache Msg Dg E C) (m : Msg) : roPart c m = c (.inl m) := rfl

/-- Recording a random-oracle answer commutes with forgetting the path oracle. -/
theorem roPart_cacheQuery_inl (c : ACache Msg Dg E C) (m : Msg) (d : Dg) :
    roPart (c.cacheQuery (.inl m) d) = (roPart c).cacheQuery m d := by
  refine QueryCache.ext fun m' ↦ ?_
  by_cases h : m' = m
  · subst h; simp
  · rw [roPart_apply, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
      QueryCache.cacheQuery_of_ne _ _ h, roPart_apply]

/-- Recording a path-oracle answer is invisible to the random oracle part. -/
theorem roPart_cacheQuery_inr (c : ACache Msg Dg E C) (β : List (Dg × E))
    (t : SpState Dg E C) : roPart (c.cacheQuery (.inr β) t) = roPart c := by
  refine QueryCache.ext fun m' ↦ ?_
  rw [roPart_apply, QueryCache.cacheQuery_of_ne _ _ (by simp), roPart_apply]

/-- A random-oracle step, seen through the random oracle part. -/
theorem roPart_roStep_inl (m : Msg) (c : ACache Msg Dg E C) :
    (fun w ↦ (w.1, roPart w.2)) <$> roStep (hs := aSpec Msg Dg E C) (.inl m) c =
      roStep (hs := roSpec Msg Dg) m (roPart c) := by
  rcases h : c (.inl m) with _ | d
  · rw [roStep_of_none h, roStep_of_none (by simpa using h)]
    simp [roPart_cacheQuery_inl]
  · rw [roStep_of_some h, roStep_of_some (by simpa using h)]
    simp

/-- The rest of the rate and the capacity of a uniform state are uniform. -/
theorem uniform_rest_evalDistEq {β : Type} (f : E × C → ProbComp β) :
    (($ᵗ (SpState Dg E C)) >>= fun t ↦ f (t.1.2, t.2)) =ᵈ (($ᵗ (E × C)) >>= f) := by
  rw [SampleableType.uniformSample_prod_eq_bind, SampleableType.uniformSample_prod_eq_bind,
    SampleableType.uniformSample_prod_eq_bind]
  simp only [bind_assoc, pure_bind]
  exact EvalDistEq.bind_const _ _

/-- A coin of the ideal world. -/
theorem ideal_inl_run (n : ℕ) (σ : SimState Dg E C) (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl ((idealImpl P (.inl n)).run σ)).run c =
      (fun u ↦ ((u, σ), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simp only [idealImpl, StateT.run_monadLift, monadLift_self]
  rw [simulateQ_bind, StateT.run_bind, roSim.run_liftM]
  simp

/-- The run of a random-oracle query of the ideal world. -/
theorem ro_run_hq (m : Msg) (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl
      ((roSpec Msg Dg).query m : OracleComp (unifSpec + roSpec Msg Dg) Dg)).run c =
      roStep (hs := roSpec Msg Dg) m c :=
  run_hq (hs := roSpec Msg Dg) m c

/-- A hash query of the ideal world. -/
theorem ideal_hash_run (m : Msg) (σ : SimState Dg E C) (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl ((idealImpl P (.inr (.inl m))).run σ)).run c =
      (fun w ↦ ((w.1, σ), w.2)) <$> roStep (hs := roSpec Msg Dg) m c := by
  simp only [idealImpl, StateT.run_monadLift, monadLift_self]
  rw [simulateQ_bind, StateT.run_bind, ro_run_hq]
  simp

/-- The simulator's rooted answer for a padded message. -/
theorem rootedAnswer_run_some {β : List (Dg × E)} {m : Msg} (hm : P.unpad β = some m)
    (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl (rootedAnswer (C := C) P β)).run c =
      (roStep (hs := roSpec Msg Dg) m c >>= fun w ↦
        ($ᵗ (E × C)) >>= fun ec ↦ pure (((w.1, ec.1), ec.2), w.2)) := by
  simp only [rootedAnswer, hm]
  rw [simulateQ_bind, StateT.run_bind, ro_run_hq]
  simp [simulateQ_romImpl_liftM_run]

/-- The simulator's rooted answer for a path that pads no message. -/
theorem rootedAnswer_run_none {β : List (Dg × E)} (hm : P.unpad β = none)
    (c : (roSpec Msg Dg).QueryCache) :
    (simulateQ (roSpec Msg Dg).romImpl (rootedAnswer (C := C) P β)).run c =
      (fun y ↦ (y, c)) <$> ($ᵗ (SpState Dg E C)) := by
  simp only [rootedAnswer, hm]
  exact simulateQ_romImpl_liftM_run _ _

/-- The path value of a path whose oracle point is fresh. -/
theorem val_run_fresh_some {β : List (Dg × E)} {m : Msg} (hm : P.unpad β = some m)
    (c : ACache Msg Dg E C) (hβ : c (.inr β) = none) :
    (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c =
      (roStep (hs := aSpec Msg Dg E C) (.inl m) c >>= fun w ↦ ($ᵗ (SpState Dg E C)) >>= fun t ↦
        pure (((w.1, t.1.2), t.2), w.2.cacheQuery (.inr β) t)) := by
  simp only [val, hm, simulateQ_bind, StateT.run_bind, run_hq, simulateQ_pure, StateT.run_pure]
  rcases h : c (.inl m) with _ | d
  · rw [roStep_of_none h]
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun d ↦ ?_
    rw [roStep_of_none (by rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hβ)]
    simp
  · rw [roStep_of_some h]
    simp only [pure_bind]
    rw [roStep_of_none hβ]
    simp

/-- The path value of a path that pads no message, at a fresh oracle point. -/
theorem val_run_fresh_none {β : List (Dg × E)} (hm : P.unpad β = none)
    (c : ACache Msg Dg E C) (hβ : c (.inr β) = none) :
    (simulateQ (aSpec Msg Dg E C).romImpl (val P β)).run c =
      (($ᵗ (SpState Dg E C)) >>= fun t ↦ pure (t, c.cacheQuery (.inr β) t)) := by
  simp only [val, hm, run_hq]
  rw [roStep_of_none hβ]
  rfl

/-- The state projection forgetting the path oracle. -/
def projT (s : SimState Dg E C × ACache Msg Dg E C) :
    SimState Dg E C × (roSpec Msg Dg).QueryCache := (s.1, roPart s.2)

/-- **One step of the simulator over path values is one step of the simulator**, in
distribution, once the path oracle is forgotten. -/
theorem idealT_step_evalDistEq (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (σ : SimState Dg E C) (c : ACache Msg Dg E C) (hV : VStruct P iv σ c) :
    Prod.map id projT <$> ((foldRO (idealTImpl P)) t).run (σ, c) =ᵈ
      ((foldRO (idealImpl P)) t).run (projT (σ, c)) := by
  rw [foldRO_run, foldRO_run]
  rcases t with n | m | x | y
  · rw [idealT_inl_run, ideal_inl_run]
    simp [projT, Functor.map_map]
  · rw [idealT_hash_run, ideal_hash_run, projT, ← roPart_roStep_inl]
    simp [projT, Functor.map_map]
  · rw [idealT_fwd_run]
    simp only [projT, idealImpl, simulator, StateT.run_mk]
    rcases hy : forwardLookup σ.edges x with _ | y
    · rcases hch : chainOf σ.chains x with _ | ⟨s, β⟩
      · -- a fresh unrooted node
        simp only [visFwd, hy, hch]
        rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run]
        simp [Functor.map_map, projT]
      · -- a fresh rooted node: its path value is fresh
        have hfresh : c (.inr (β ++ [blockTo s x])) = none := by
          by_contra h
          exact rootedPath_notMem hV hy hch (hV.tFresh _ h)
        simp only [visFwd, hy, hch, simulateQ_bind, StateT.run_bind, simulateQ_pure,
          StateT.run_pure]
        rcases hm : P.unpad (β ++ [blockTo s x]) with _ | m
        · rw [val_run_fresh_none P hm c hfresh, rootedAnswer_run_none P hm]
          simp only [bind_assoc, pure_bind, map_bind, map_pure]
          refine (EvalDistEq.bind_const _ _).trans ?_
          simp [roPart_cacheQuery_inr, projT]
        · rw [val_run_fresh_some P hm c hfresh, rootedAnswer_run_some P hm, ← roPart_roStep_inl]
          simp only [bind_assoc, pure_bind, map_bind, map_pure, bind_map_left]
          refine (EvalDistEq.bind_const _ _).trans (EvalDistEq.bind_right _ fun w ↦ ?_)
          simp only [Prod.map_apply, id_eq, projT, roPart_cacheQuery_inr]
          exact uniform_rest_evalDistEq (fun ec ↦ pure ((((w.1, ec.1), ec.2),
            (⟨(x, ((w.1, ec.1), ec.2)) :: σ.edges,
              (((w.1, ec.1), ec.2), β ++ [blockTo s x]) :: σ.chains⟩ : SimState Dg E C),
              roPart w.2)))
    · -- a recorded input
      simp only [visFwd, hy, simulateQ_pure, StateT.run_pure]
      simp only [map_bind, map_pure]
      exact EvalDistEq.bind_const _ _
  · rw [idealT_inv_run]
    simp only [projT, idealImpl, simulator, StateT.run_mk, visInv]
    rcases hx : inverseLookup σ.edges y with _ | x
    · rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run]
      simp [Functor.map_map, projT]
    · simp only [simulateQ_pure, StateT.run_pure, Functor.map_map]
      exact EvalDistEq.map_const _ _

/-- **The simulator over path values is the simulator**, on the whole run, once the path
oracle is forgotten. -/
theorem idealT_run_evalDistEq {α : Type} (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    (simulateQ (foldRO (idealTImpl P)) oa).run' (SimState.init iv, ∅) =ᵈ
      (simulateQ (foldRO (idealImpl P)) oa).run' (SimState.init iv, ∅) := by
  have h := run'_simulateQ_evalDistEq_of_inv (foldRO (idealTImpl P)) (foldRO (idealImpl P))
    (fun s ↦ VStruct P iv s.1 s.2) projT
    (fun t s hs z hz ↦ by
      rw [foldRO_run] at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact vStruct_idealT t hs hw)
    (fun t s hs ↦ idealT_step_evalDistEq P iv t s.1 s.2 hs) oa (SimState.init iv, ∅)
    vStruct_init
  have h0 : projT ((SimState.init iv : SimState Dg E C), (∅ : ACache Msg Dg E C)) =
      (SimState.init iv, ∅) := by
    simp only [projT, Prod.mk.injEq, true_and]
    exact QueryCache.ext fun m ↦ rfl
  rwa [h0] at h

/-- **The ideal world, with the simulator over path values.** -/
theorem idealTGame_evalDistEq_idealGame {α : Type}
    (oa : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    (simulateQ (aSpec Msg Dg E C).romImpl
      ((simulateQ (idealTImpl P) oa).run' (SimState.init iv))).run' ∅ =ᵈ idealGame P iv oa := by
  rw [run'_simulateQ_foldRO, idealGame, run'_simulateQ_foldRO]
  exact idealT_run_evalDistEq P iv oa

end Setting

end Common
