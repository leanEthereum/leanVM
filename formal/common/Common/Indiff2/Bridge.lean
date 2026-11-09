module

public import Common.Indiff2.Defs
public import Common.Indiff.Ideal

@[expose] public section

/-!
# The two-oracle model: from the one-oracle ideal world to the simulator with `F`

The real world of the two-oracle model is the real world of the one-oracle model for the game
whose direct calls are permutation queries (`realGame2`). Its one-oracle ideal world answers the
direct calls with the simulator too (`ideal1Impl`). Drawing the simulator's fresh non-final
forward answers from `F` instead of uniformly changes nothing, since `F` is then queried only at
fresh points (`ideal1_evalDistEq_ideal1F`): the simulator becomes `simulator2`, answering both
the adversary's permutation queries and the honest direct calls (`ideal1FImpl`).
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

/-- The duplex discipline after a direct call. -/
theorem duplexOK_query_bind_F (NF : (Dg × E) → Prop) {α : Type} (x : SpState Dg E C)
    (k : SpState Dg E C → OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α)
    (hist : List (SpState Dg E C)) :
    DuplexOK iv NF (liftM ((dSpec2 Msg Dg (SpState Dg E C)).query (.inr (.inr (.inr x)))) >>= k)
      hist ↔ Admissible iv NF hist x ∧ ∀ y, DuplexOK iv NF (k y) (y :: hist) := Iff.rfl

/-- The duplex discipline after any other query. -/
theorem duplexOK_query_bind_other (NF : (Dg × E) → Prop) {α : Type}
    (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (ht : ∀ x, t ≠ .inr (.inr (.inr x)))
    (k : (dSpec2 Msg Dg (SpState Dg E C)).Range t → OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α)
    (hist : List (SpState Dg E C)) :
    DuplexOK iv NF (liftM ((dSpec2 Msg Dg (SpState Dg E C)).query t) >>= k) hist ↔
      ∀ u, DuplexOK iv NF (k u) hist := by
  rcases t with n | m | q | x
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact absurd rfl (ht x)

/-- The cost of the unfolded game is the cost of the two-oracle game. -/
theorem isWeightBound_toOne {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α)
    (q : ℕ) (hD : QueryCostAtMost D (queryCost2 (Dg := Dg) P) q) :
    QueryCostAtMost (simulateQ (toOne (E := E) (C := C)) D) (queryCost (Dg := Dg) P) q := by
  induction D using OracleComp.inductionOn generalizing q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isWeightBound_query_bind_iff] at hD
    obtain ⟨ht, hk⟩ := hD
    rw [simulateQ_query_bind]
    have h1 : QueryCostAtMost (toOne (E := E) (C := C) t) (queryCost (Dg := Dg) P)
        (queryCost2 (Dg := Dg) P t) := by
      rcases t with n | m | q' | x
      · exact isWeightBound_query (spec := dSpec Msg Dg (SpState Dg E C)) _ (.inl n)
      · exact isWeightBound_query (spec := dSpec Msg Dg (SpState Dg E C)) _ (.inr (.inl m))
      · exact isWeightBound_query (spec := dSpec Msg Dg (SpState Dg E C)) _ (.inr (.inr q'))
      · exact isWeightBound_query (spec := dSpec Msg Dg (SpState Dg E C)) _ (.inr (.inr (.forward x)))
    have := h1.bind fun u ↦ ih u (q - queryCost2 (Dg := Dg) P t) (hk u)
    rwa [Nat.add_sub_cancel' ht] at this

/-- The one-oracle ideal world, with the direct calls answered by the simulator. -/
noncomputable def ideal1Impl : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + roSpec Msg Dg))) :=
  (idealImpl P) ∘ₛ toOne (E := E) (C := C)

/-- The one-oracle ideal world of the unfolded game. -/
theorem idealGame_toOne {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    idealGame P iv (simulateQ (toOne (E := E) (C := C)) D) =
      (simulateQ (roSpec Msg Dg).romImpl
        ((simulateQ (ideal1Impl P) D).run' (SimState.init iv))).run' ∅ := by
  rw [idealGame, ideal1Impl, QueryImpl.simulateQ_compose]

/-- The one-oracle ideal world with the simulator drawing from `F`. -/
noncomputable def ideal1FImpl : QueryImpl (dSpec2 Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) _)
  | .inr (.inl m) => liftM (hQuery (Msg := Msg) (Dg := Dg) (E := E) (C := C) m)
  | .inr (.inr (.inl q)) => simulator2 P q
  | .inr (.inr (.inr x)) => simulator2 P (.forward x)

/-- The cache of the two-oracle ROM. -/
abbrev HCache (Msg Dg St : Type) := (hfSpec Msg Dg St).QueryCache

/-- The `H` part of a two-oracle cache. -/
def roPartF (c : HCache Msg Dg (SpState Dg E C)) : (roSpec Msg Dg).QueryCache :=
  QueryCache.ofFn fun m ↦ c (.inl m)

@[simp] theorem roPartF_apply (c : HCache Msg Dg (SpState Dg E C)) (m : Msg) :
    roPartF c m = c (.inl m) := rfl

theorem roPartF_cacheQuery_inl (c : HCache Msg Dg (SpState Dg E C)) (m : Msg) (d : Dg) :
    roPartF (c.cacheQuery (.inl m) d) = (roPartF c).cacheQuery m d := by
  refine QueryCache.ext fun m' ↦ ?_
  by_cases h : m' = m
  · subst h; simp
  · rw [roPartF_apply, QueryCache.cacheQuery_of_ne _ _ (by simpa using h),
      QueryCache.cacheQuery_of_ne _ _ h, roPartF_apply]

theorem roPartF_cacheQuery_inr (c : HCache Msg Dg (SpState Dg E C)) (x : SpState Dg E C)
    (t : SpState Dg E C) : roPartF (c.cacheQuery (.inr x) t) = roPartF c := by
  refine QueryCache.ext fun m' ↦ ?_
  rw [roPartF_apply, QueryCache.cacheQuery_of_ne _ _ (by simp), roPartF_apply]

/-- An `H` step of the two-oracle ROM, seen through the `H` part. -/
theorem roPartF_roStep_inl (m : Msg) (c : HCache Msg Dg (SpState Dg E C)) :
    (fun w ↦ (w.1, roPartF w.2)) <$> roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m) c =
      roStep (hs := roSpec Msg Dg) m (roPartF c) := by
  rcases h : c (.inl m) with _ | d
  · rw [roStep_of_none h, roStep_of_none (by simpa using h)]
    simp [roPartF_cacheQuery_inl]
  · rw [roStep_of_some h, roStep_of_some (by simpa using h)]
    simp

/-- The two-oracle simulator's rooted answer for a padded message. -/
theorem rootedAnswer2_run_some {β : List (Dg × E)} {m : Msg} (hm : P.unpad β = some m)
    (x : SpState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl (rootedAnswer2 P β x)).run c =
      (roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m) c >>= fun w ↦
        ($ᵗ (E × C)) >>= fun ec ↦ pure (((w.1, ec.1), ec.2), w.2)) := by
  simp only [rootedAnswer2, hm]
  rw [simulateQ_bind, StateT.run_bind, hQuery, run_hq]
  simp [simulateQ_romImpl_liftM_run]

/-- The two-oracle simulator's rooted answer for a path that pads no message is `F`. -/
theorem rootedAnswer2_run_none {β : List (Dg × E)} (hm : P.unpad β = none)
    (x : SpState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl (rootedAnswer2 P β x)).run c =
      roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := by
  simp only [rootedAnswer2, hm, fQuery, run_hq]

/-- An `F` query of the two-oracle ROM. -/
theorem fQuery_run (x : SpState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl (fQuery (Msg := Msg) (Dg := Dg) x)).run c =
      roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) c := run_hq _ _

/-- **A forward step of the two-oracle simulator is a forward step of the simulator**, in
distribution, once `F` is forgotten, when `F` has been queried at recorded inputs only. -/
theorem simulator2_fwd_evalDistEq (x : SpState Dg E C) (σ : SimState Dg E C)
    (c : HCache Msg Dg (SpState Dg E C))
    (hF : ∀ x', c (.inr x') ≠ none → x' ∈ σ.edges.map Prod.fst) :
    (fun w ↦ (w.1.1, (w.1.2, roPartF w.2))) <$>
        (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl ((simulator2 P (.forward x)).run σ)).run c
      =ᵈ (fun w ↦ (w.1.1, (w.1.2, w.2))) <$>
        (simulateQ (roSpec Msg Dg).romImpl ((simulator P (.forward x)).run σ)).run (roPartF c) := by
  simp only [simulator2, simulator, StateT.run_mk]
  rcases hy : forwardLookup σ.edges x with _ | y
  · have hfresh : c (.inr x) = none := by
      by_contra h
      exact (fwdLookup_eq_none_iff.mp hy) (hF x h)
    rcases hch : chainOf σ.chains x with _ | ⟨s, β⟩
    · simp only [simulateQ_bind, StateT.run_bind, fQuery_run, roStep_of_none hfresh,
        simulateQ_romImpl_liftM_run, simulateQ_pure, StateT.run_pure]
      simp [roPartF_cacheQuery_inr, Functor.map_map]
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rcases hm : P.unpad (β ++ [blockTo s x]) with _ | m
      · rw [rootedAnswer2_run_none P hm, roStep_of_none hfresh, rootedAnswer_run_none P hm]
        simp [roPartF_cacheQuery_inr, Functor.map_map]
      · rw [rootedAnswer2_run_some P hm, rootedAnswer_run_some P hm, ← roPartF_roStep_inl]
        simp [Functor.map_map, map_bind]
  · simp

/-! ## The folded steps -/

/-- The state of a folded two-oracle world: the simulator's bookkeeping and the cache. -/
abbrev FState (Msg Dg E C : Type) := SimState Dg E C × HCache Msg Dg (SpState Dg E C)

/-- A direct call `F x`, recording the edge as the simulator would. -/
noncomputable def fStep (x : SpState Dg E C) (s : FState Msg Dg E C) :
    ProbComp (SpState Dg E C × FState Msg Dg E C) :=
  (fun w ↦ (w.1, (replayStep s.1 (.forward x, w.1), w.2))) <$>
    roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inr x) s.2

/-- A forward step of the two-oracle simulator. -/
noncomputable def fwdStep2 (x : SpState Dg E C) (s : FState Msg Dg E C) :
    ProbComp (SpState Dg E C × FState Msg Dg E C) :=
  match forwardLookup s.1.edges x with
  | some y => pure (y, s)
  | none =>
    match chainOf s.1.chains x with
    | some (r, β) =>
      match P.unpad (β ++ [blockTo r x]) with
      | some m => roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m) s.2 >>= fun w ↦
          ($ᵗ (E × C)) >>= fun ec ↦
            pure (((w.1, ec.1), ec.2), (replayStep s.1 (.forward x, ((w.1, ec.1), ec.2)), w.2))
      | none => fStep x s
    | none => fStep x s

/-- An inverse step of the two-oracle simulator. -/
noncomputable def invStep2 (y : SpState Dg E C) (s : FState Msg Dg E C) :
    ProbComp (SpState Dg E C × FState Msg Dg E C) :=
  match inverseLookup s.1.edges y with
  | some x => pure (x, s)
  | none => (fun x ↦ (x, (replayStep s.1 (.inverse y, x), s.2))) <$> ($ᵗ (SpState Dg E C))

theorem simulator2_fwd_run (x : SpState Dg E C) (s : FState Msg Dg E C) :
    (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
      ((simulator2 P (.forward x)).run s.1)).run s.2 = fwdStep2 P x s := by
  obtain ⟨σ, c⟩ := s
  simp only [simulator2, StateT.run_mk, fwdStep2, fStep]
  rcases hy : forwardLookup σ.edges x with _ | y
  · rcases hch : chainOf σ.chains x with _ | ⟨r, β⟩
    · simp only [simulateQ_bind, StateT.run_bind, fQuery_run, simulateQ_pure, StateT.run_pure]
      simp [replayStep, hy, hch]
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure]
      rcases hm : P.unpad (β ++ [blockTo r x]) with _ | m
      · rw [rootedAnswer2_run_none P hm]
        simp [replayStep, hy, hch]
      · rw [rootedAnswer2_run_some P hm]
        simp [replayStep, hy, hch]
  · simp

theorem simulator2_inv_run (y : SpState Dg E C) (s : FState Msg Dg E C) :
    (fun y ↦ (y.1.1, (y.1.2, y.2))) <$> (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
      ((simulator2 P (.inverse y)).run s.1)).run s.2 = invStep2 y s := by
  obtain ⟨σ, c⟩ := s
  simp only [simulator2, StateT.run_mk, invStep2]
  rcases hx : inverseLookup σ.edges y with _ | x
  · rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run]
    simp [replayStep, hx, Functor.map_map]
  · simp

/-- A coin of the folded worlds. -/
theorem ideal1F_inl_run (n : ℕ) (σ : SimState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl ((ideal1FImpl P (.inl n)).run σ)).run c =
      (fun u ↦ ((u, σ), c)) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  have h := unifFwdImpl.simulateQ_run (hashSpec := hfSpec Msg Dg (SpState Dg E C))
    (unifSpec.query n : ProbComp (Fin (n + 1))) c
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map] at h
  simp only [ideal1FImpl, StateT.run_monadLift, monadLift_self]
  rw [simulateQ_bind, StateT.run_bind]
  simp [h]

/-- An `H` query of the folded worlds. -/
theorem ideal1F_hash_run (m : Msg) (σ : SimState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) :
    (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
      ((ideal1FImpl P (.inr (.inl m))).run σ)).run c =
      (fun w ↦ ((w.1, σ), w.2)) <$> roStep (hs := hfSpec Msg Dg (SpState Dg E C)) (.inl m) c := by
  simp only [ideal1FImpl, StateT.run_monadLift, monadLift_self]
  rw [simulateQ_bind, StateT.run_bind, hQuery, run_hq]
  simp

/-! ## The one-oracle ideal world is the world with `F` -/

theorem ideal1Impl_fwd (q : PermutationQuery (SpState Dg E C)) :
    ideal1Impl P (.inr (.inr (.inl q))) = idealImpl P (.inr (.inr q)) := by
  simp [ideal1Impl, toOne]

theorem ideal1Impl_F (x : SpState Dg E C) :
    ideal1Impl P (.inr (.inr (.inr x))) = idealImpl P (.inr (.inr (.forward x))) := by
  simp [ideal1Impl, toOne]

theorem ideal1Impl_inl (n : ℕ) : ideal1Impl (Msg := Msg) (Dg := Dg) (E := E) (C := C) P (.inl n) =
    idealImpl P (.inl n) := by
  simp [ideal1Impl, toOne]

theorem ideal1Impl_hash (m : Msg) : ideal1Impl (E := E) (C := C) P (.inr (.inl m)) =
    idealImpl P (.inr (.inl m)) := by
  simp [ideal1Impl, toOne]

/-- `F` has been queried at recorded inputs only. -/
def FDom (σ : SimState Dg E C) (c : HCache Msg Dg (SpState Dg E C)) : Prop :=
  ∀ x, c (.inr x) ≠ none → x ∈ σ.edges.map Prod.fst

theorem mem_replayStep_edges {σ : SimState Dg E C}
    (r : PermutationQuery (SpState Dg E C) × SpState Dg E C) {e : SpState Dg E C × SpState Dg E C}
    (he : e ∈ σ.edges) : e ∈ (replayStep σ r).edges := by
  obtain ⟨q, a⟩ := r
  cases q with
  | forward x =>
    simp only [replayStep]
    split
    · exact he
    · split <;> exact List.mem_cons_of_mem _ he
  | inverse y =>
    simp only [replayStep]
    split
    · exact he
    · exact List.mem_cons_of_mem _ he

theorem fst_mem_replayStep_fwd (σ : SimState Dg E C) (x y : SpState Dg E C) :
    x ∈ (replayStep σ (.forward x, y)).edges.map Prod.fst := by
  simp only [replayStep]
  split
  · next y' hy => exact List.mem_map.mpr ⟨_, mem_of_fwdLookup_eq_some hy, rfl⟩
  · split <;> simp

theorem fDom_replayStep {σ : SimState Dg E C} {c c' : HCache Msg Dg (SpState Dg E C)}
    (hF : FDom σ c) (r : PermutationQuery (SpState Dg E C) × SpState Dg E C)
    (hc : ∀ x', c' (.inr x') ≠ none → c (.inr x') ≠ none ∨ r.1 = .forward x') :
    FDom (replayStep σ r) c' := by
  intro x' hx'
  rcases hc x' hx' with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp (hF x' h)
    exact List.mem_map.mpr ⟨e, mem_replayStep_edges r he, rfl⟩
  · obtain ⟨q, a⟩ := r
    simp only at h
    subst h
    exact fst_mem_replayStep_fwd σ x' a

theorem fDom_fwdStep2 (x : SpState Dg E C) (s : FState Msg Dg E C) (hF : FDom s.1 s.2) {z}
    (hz : z ∈ support (fwdStep2 P x s)) : FDom z.2.1 z.2.2 := by
  obtain ⟨σ, c⟩ := s
  have hf : ∀ {z}, z ∈ support (fStep x (σ, c)) → FDom z.2.1 z.2.2 := by
    intro z hz
    simp only [fStep, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨-, -, hother⟩ := roStep_support _ _ hw
    refine fDom_replayStep hF _ fun x' hx' ↦ ?_
    by_cases h : x' = x
    · exact Or.inr (by rw [h])
    · exact Or.inl (by rwa [← hother (.inr x') (by simpa using h)])
  simp only [fwdStep2] at hz
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hF
  · split at hz
    · split at hz
      · simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
          support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨w, hw, ec, rfl⟩ := hz
        obtain ⟨-, -, hother⟩ := roStep_support _ _ hw
        exact fDom_replayStep hF _ fun x' hx' ↦
          Or.inl (by rwa [← hother (.inr x') (by simp)])
      · exact hf hz
    · exact hf hz

theorem fDom_invStep2 (y : SpState Dg E C) (s : FState Msg Dg E C) (hF : FDom s.1 s.2) {z}
    (hz : z ∈ support (invStep2 y s)) : FDom z.2.1 z.2.2 := by
  simp only [invStep2] at hz
  split at hz
  · simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hF
  · simp only [support_map, Set.mem_image] at hz
    obtain ⟨x, -, rfl⟩ := hz
    exact fDom_replayStep hF _ fun x' hx' ↦ Or.inl hx'

theorem ideal1F_fwd_run (q : PermutationQuery (SpState Dg E C)) (s : FState Msg Dg E C) :
    ((foldRO (ideal1FImpl P)) (.inr (.inr (.inl q)))).run s =
      match q with
      | .forward x => fwdStep2 P x s
      | .inverse y => invStep2 y s := by
  rw [foldRO_run]
  cases q with
  | forward x => exact simulator2_fwd_run P x s
  | inverse y => exact simulator2_inv_run P y s

theorem ideal1F_F_run (x : SpState Dg E C) (s : FState Msg Dg E C) :
    ((foldRO (ideal1FImpl P)) (.inr (.inr (.inr x)))).run s = fwdStep2 P x s := by
  rw [foldRO_run]
  exact simulator2_fwd_run P x s

/-- Every step of the world with `F` keeps `F` at recorded inputs. -/
theorem fDom_ideal1F (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain) (s : FState Msg Dg E C)
    (hF : FDom s.1 s.2) {z} (hz : z ∈ support (((foldRO (ideal1FImpl P)) t).run s)) :
    FDom z.2.1 z.2.2 := by
  rcases t with n | m | q | x
  · rw [foldRO_run, ideal1F_inl_run] at hz
    simp only [Functor.map_map, support_map, Set.mem_image] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hF
  · rw [foldRO_run, ideal1F_hash_run] at hz
    simp only [Functor.map_map, support_map, Set.mem_image] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨-, -, hother⟩ := roStep_support _ _ hw
    intro x' hx'
    exact hF x' (by rwa [← hother (.inr x') (by simp)])
  · rw [ideal1F_fwd_run] at hz
    cases q with
    | forward x => exact fDom_fwdStep2 P x s hF hz
    | inverse y => exact fDom_invStep2 y s hF hz
  · rw [ideal1F_F_run] at hz
    exact fDom_fwdStep2 P x s hF hz

/-- The projection forgetting `F`. -/
def projF (s : FState Msg Dg E C) : SimState Dg E C × (roSpec Msg Dg).QueryCache :=
  (s.1, roPartF s.2)

/-- **One step of the world with `F` is one step of the one-oracle ideal world**, in
distribution, once `F` is forgotten. -/
theorem ideal1F_step_evalDistEq (t : (dSpec2 Msg Dg (SpState Dg E C)).Domain)
    (s : FState Msg Dg E C) (hF : FDom s.1 s.2) :
    Prod.map id projF <$> ((foldRO (ideal1FImpl P)) t).run s =ᵈ
      ((foldRO (ideal1Impl P)) t).run (projF s) := by
  obtain ⟨σ, c⟩ := s
  rw [foldRO_run, foldRO_run]
  rcases t with n | m | q | x
  · rw [ideal1F_inl_run, ideal1Impl_inl, ideal_inl_run]
    simp [projF, Functor.map_map]
  · rw [ideal1F_hash_run, ideal1Impl_hash, ideal_hash_run, projF, ← roPartF_roStep_inl]
    simp [projF, Functor.map_map]
  · rw [ideal1Impl_fwd]
    cases q with
    | forward x =>
      simpa [Functor.map_map, projF, idealImpl, ideal1FImpl] using
        simulator2_fwd_evalDistEq P x σ c hF
    | inverse y =>
      simp only [ideal1FImpl, idealImpl, simulator2, simulator, StateT.run_mk, projF]
      rcases hx : inverseLookup σ.edges y with _ | x
      · rw [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, simulateQ_bind,
          StateT.run_bind, simulateQ_romImpl_liftM_run]
        simp [Functor.map_map, projF]
      · simp [projF]
  · rw [ideal1Impl_F]
    simpa [Functor.map_map, projF, idealImpl, ideal1FImpl] using
      simulator2_fwd_evalDistEq P x σ c hF

/-- **The one-oracle ideal world is the world with `F`.** -/
theorem ideal1_evalDistEq_ideal1F {α : Type} (D : OracleComp (dSpec2 Msg Dg (SpState Dg E C)) α) :
    (simulateQ (foldRO (ideal1FImpl P)) D).run' (SimState.init iv, ∅) =ᵈ
      idealGame P iv (simulateQ (toOne (E := E) (C := C)) D) := by
  rw [idealGame_toOne, run'_simulateQ_foldRO]
  have h := run'_simulateQ_evalDistEq_of_inv (foldRO (ideal1FImpl P)) (foldRO (ideal1Impl P))
    (fun s ↦ FDom s.1 s.2) projF (fun t s hs z hz ↦ fDom_ideal1F P t s hs hz)
    (fun t s hs ↦ ideal1F_step_evalDistEq P t s hs) D (SimState.init iv, ∅)
    (fun x hx ↦ absurd rfl hx)
  have h0 : projF ((SimState.init iv : SimState Dg E C), (∅ : HCache Msg Dg (SpState Dg E C))) =
      (SimState.init iv, ∅) := by
    simp only [projF, Prod.mk.injEq, true_and]
    exact QueryCache.ext fun m ↦ rfl
  rwa [h0] at h

end Setting

end Common
