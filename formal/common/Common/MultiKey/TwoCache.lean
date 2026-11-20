module

public import Common.MultiKey.Transfer
public import Common.RomComm
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.SimSemantics.StateT.StateProjection

@[expose] public section

/-!
# One random oracle or two: identical until a point is asked of both

A computation whose hash queries carry a tag (`TagSpec`: `false`, the real oracle; `true`, a
private one) runs in two worlds:

* **one oracle** (`untag`, then the random oracle `H`): the tag is forgotten, every query asks the
  one lazily sampled random oracle;
* **two oracles** (`TagSpec.romImpl`): the tagged queries ask two independent lazily sampled random
  oracles, a cache entry per tag and input.

They agree until some input is asked under both tags (`Bad`, of the two-oracle cache): an event of
the output has, in the first world, at most its probability in the second plus that of `Bad`
(`prEvent_untag_le`). The proof runs the first world on the second's state (`implU`: an input
cached under either tag answers both), which agrees with the second until `Bad`
(`agreeUntilBad`), and whose run, read through the union of the two caches, is the one-oracle run
(`map_run_implU`).

`flatten`: the two-oracle world is the one-oracle world of the computation whose private oracle
is sampled by the computation itself, lazily, with coins (`inner`): the private oracle is
uncharged randomness.
-/

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common.SufCma.MultiKey

/-- Tagged hash queries: `(false, x)` asks the real oracle at `x`, `(true, x)` the private one. -/
abbrev TagSpec := (Bool × List UInt8) →ₒ BitVec 256

/-- Coins and tagged hash queries. -/
abbrev TSpec := unifSpec + TagSpec

/-- **Forget the tag**: both oracles become the hash `H`. -/
def untag : QueryImpl TSpec (OracleComp World)
  | .inl n => liftM (World.query (.inl n))
  | .inr t => liftM (World.query (.inr t.2))

/-- The two caches as one: the entry of `(b, x)` is `cF x` for `b = false`, `cG x` for `true`. -/
def join (cF cG : SchemeHashSpec.QueryCache) : TagSpec.QueryCache :=
  QueryCache.ofFn fun t ↦ if t.1 then cG t.2 else cF t.2

/-- The union of the two caches, the real one first. -/
def union (c : TagSpec.QueryCache) : SchemeHashSpec.QueryCache :=
  QueryCache.ofFn fun x ↦ match c (false, x) with
    | some u => some u
    | none => c (true, x)

/-- The two caches agree where both answer. -/
def Consistent (c : TagSpec.QueryCache) : Prop :=
  ∀ x u v, c (false, x) = some u → c (true, x) = some v → u = v

/-- **Bad**: some input answered under both tags. -/
def Bad (c : TagSpec.QueryCache) : Prop :=
  ∃ x, (c (false, x)).isSome ∧ (c (true, x)).isSome

/-- The step of the union world on a tagged query: the cached answer of `t`, else that of the
same input under the other tag (now cached at `t` too), else a fresh uniform answer. -/
noncomputable def unionStep (t : Bool × List UInt8) (c : TagSpec.QueryCache) :
    ProbComp (TagSpec.Range t × TagSpec.QueryCache) :=
  match c t with
  | some u => pure (u, c)
  | none => match c (!t.1, t.2) with
    | some u => pure (u, c.cacheQuery t u)
    | none => ($ᵗ TagSpec.Range t) >>= fun u ↦ pure (u, c.cacheQuery t u)

/-- **The union world** on the two-oracle state. -/
noncomputable def implU : QueryImpl TSpec (StateT TagSpec.QueryCache ProbComp) :=
  unifFwdImpl TagSpec + fun t ↦ StateT.mk (unionStep t)

/-! ## Agreement until bad -/

theorem bad_cacheQuery_other {c : TagSpec.QueryCache} {t : Bool × List UInt8} {u v : BitVec 256}
    (h : c (!t.1, t.2) = some v) : Bad (c.cacheQuery t u) := by
  obtain ⟨b, x⟩ := t
  cases b
  · have h' : c (true, x) = some v := h
    exact ⟨x, by simp, by rw [QueryCache.cacheQuery_of_ne _ _ (by simp), h']; rfl⟩
  · have h' : c (false, x) = some v := h
    exact ⟨x, by rw [QueryCache.cacheQuery_of_ne _ _ (by simp), h']; rfl, by simp⟩

/-- **The union world and the two-oracle world agree until `Bad`.** -/
theorem agreeUntilBad : QueryImpl.AgreeUntilBad implU TagSpec.romImpl Bad := by
  refine QueryImpl.AgreeUntilBad.of_run_eq_or_bad fun t c _ ↦ ?_
  rcases t with n | t
  · exact .inl rfl
  · have e1 : (implU (.inr t)).run c = unionStep t c := rfl
    have e2 : (TagSpec.romImpl (.inr t)).run c = roStep t c := romImpl_inr_run t c
    rw [e1, e2, roStep]
    rcases h : c t with _ | u
    · rcases h' : c (!t.1, t.2) with _ | v
      · left
        simp only [unionStep, h, h']
      · right
        refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
        · simp only [unionStep, h, h', support_pure, Set.mem_singleton_iff] at hz
          subst hz
          exact bad_cacheQuery_other h'
        · simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
          obtain ⟨u, -, rfl⟩ := hz
          exact bad_cacheQuery_other h'
    · left
      simp only [unionStep, h]

/-- `Bad` stays: the two-oracle world's caches only grow. -/
theorem romImpl_preservesBad : QueryImpl.PreservesInv TagSpec.romImpl Bad := by
  intro t c hc z hz
  obtain ⟨x, h1, h2⟩ := hc
  have hle : c ≤ z.2 := by
    rcases t with n | t
    · rw [unifFwdImpl.snd_eq_of_mem_support_run n c (by simpa using hz)]
    · exact (le_of_mem_support_roStep (hs := TagSpec) t c (by
        rw [← romImpl_inr_run]; exact hz)).1
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp h1
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨x, by rw [hle hu]; rfl, by rw [hle hv]; rfl⟩

/-! ## The union world is the one-oracle world -/

/-- The one-oracle world's step on a tagged query. -/
noncomputable def oneImpl : QueryImpl TSpec (StateT SchemeHashSpec.QueryCache ProbComp) :=
  SchemeHashSpec.romImpl ∘ₛ untag

theorem union_apply (c : TagSpec.QueryCache) (x : List UInt8) :
    union c x = match c (false, x) with
      | some u => some u
      | none => c (true, x) := rfl

theorem consistent_cacheQuery {c : TagSpec.QueryCache} (hc : Consistent c) (t : Bool × List UInt8)
    (u : BitVec 256) (hu : ∀ v, c (!t.1, t.2) = some v → v = u) : Consistent (c.cacheQuery t u) := by
  intro x a b ha hb
  obtain ⟨tb, tx⟩ := t
  by_cases hx : x = tx
  · subst hx
    cases tb
    · rw [QueryCache.cacheQuery_self] at ha
      rw [QueryCache.cacheQuery_of_ne _ _ (by simp)] at hb
      cases ha
      exact (hu b hb).symm
    · rw [QueryCache.cacheQuery_self] at hb
      rw [QueryCache.cacheQuery_of_ne _ _ (by simp)] at ha
      cases hb
      exact hu a ha
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp [hx])] at ha hb
    exact hc x a b ha hb

theorem union_cacheQuery_of_none {c : TagSpec.QueryCache} (t : Bool × List UInt8) (u : BitVec 256)
    (h : union c t.2 = none) : union (c.cacheQuery t u) = (union c).cacheQuery t.2 u := by
  obtain ⟨b, x⟩ := t
  have h0 : c (false, x) = none ∧ c (true, x) = none := by
    rw [union_apply] at h
    rcases h' : c (false, x) with _ | v
    · rw [h'] at h; exact ⟨rfl, h⟩
    · rw [h'] at h; cases h
  refine QueryCache.ext fun y ↦ ?_
  by_cases hy : y = x
  · subst hy
    rw [QueryCache.cacheQuery_self, union_apply]
    cases b
    · rw [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), h0.1, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ hy, union_apply, union_apply,
      QueryCache.cacheQuery_of_ne _ _ (by simp [hy]), QueryCache.cacheQuery_of_ne _ _ (by simp [hy])]

theorem union_cacheQuery_of_some {c : TagSpec.QueryCache}
    (t : Bool × List UInt8) (u : BitVec 256) (h : union c t.2 = some u) :
    union (c.cacheQuery t u) = union c := by
  obtain ⟨b, x⟩ := t
  refine QueryCache.ext fun y ↦ ?_
  by_cases hy : y = x
  · subst hy
    rw [h, union_apply]
    rw [union_apply] at h
    cases b
    · rw [QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simp)]
      rcases h' : c (false, y) with _ | v
      · rw [h'] at h; rw [QueryCache.cacheQuery_self]
      · rw [h'] at h; exact h
  · rw [union_apply, union_apply, QueryCache.cacheQuery_of_ne _ _ (by simp [hy]),
      QueryCache.cacheQuery_of_ne _ _ (by simp [hy])]

/-- In a consistent state, the union answers `x` with the cached answer of either tag. -/
theorem union_eq_of_some {c : TagSpec.QueryCache} (hc : Consistent c) {t : Bool × List UInt8}
    {u : BitVec 256} (h : c t = some u) : union c t.2 = some u := by
  obtain ⟨b, x⟩ := t
  rw [union_apply]
  cases b
  · rw [h]
  · rcases h' : c (false, x) with _ | v
    · exact h
    · rw [hc x v u h' h]

theorem union_eq_none {c : TagSpec.QueryCache} {t : Bool × List UInt8} (h : c t = none)
    (h' : c (!t.1, t.2) = none) : union c t.2 = none := by
  obtain ⟨b, x⟩ := t
  rw [union_apply]
  cases b
  · have h'' : c (true, x) = none := h'
    simp only [h, h'']
  · have h'' : c (false, x) = none := h'
    simp only [h, h'']

theorem union_eq_other {c : TagSpec.QueryCache} {t : Bool × List UInt8} {u : BitVec 256}
    (h : c t = none) (h' : c (!t.1, t.2) = some u) : union c t.2 = some u := by
  obtain ⟨b, x⟩ := t
  rw [union_apply]
  cases b
  · have h'' : c (true, x) = some u := h'
    simp only [h, h'']
  · have h'' : c (false, x) = some u := h'
    simp only [h'']

theorem consistent_empty : Consistent ∅ := fun _ _ _ h _ ↦ by simp at h

theorem implU_consistent (t : TSpec.Domain) (c : TagSpec.QueryCache) (hc : Consistent c) :
    ∀ z ∈ support ((implU t).run c), Consistent z.2 := by
  intro z hz
  rcases t with n | t
  · rw [unifFwdImpl.snd_eq_of_mem_support_run n c hz]
    exact hc
  · change z ∈ support (unionStep t c) at hz
    unfold unionStep at hz
    rcases h : c t with _ | u
    · rw [h] at hz
      rcases h' : c (!t.1, t.2) with _ | v
      · rw [h'] at hz
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
        obtain ⟨u, -, rfl⟩ := hz
        exact consistent_cacheQuery hc t u fun v hv ↦ by rw [h'] at hv; cases hv
      · rw [h'] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        exact consistent_cacheQuery hc t v fun w hw ↦ by rw [h'] at hw; cases hw; rfl
    · rw [h] at hz
      simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact hc

theorem implU_step (t : TSpec.Domain) (c : TagSpec.QueryCache) (hc : Consistent c) :
    Prod.map id union <$> (implU t).run c = (oneImpl t).run (union c) := by
  rcases t with n | t
  · have e1 : (implU (.inl n)).run c = ((unifFwdImpl TagSpec +
        fun t ↦ StateT.mk (unionStep t)) (.inl n)).run c := rfl
    have e2 : (oneImpl (.inl n)).run (union c) =
        (simulateQ SchemeHashSpec.romImpl (liftM (World.query (.inl n)))).run (union c) := rfl
    rw [e1, e2, simulateQ_spec_query, roSim.run_apply_inl, roSim.run_apply_inl, Functor.map_map]
    rfl
  · have e1 : (implU (.inr t)).run c = unionStep t c := rfl
    have e2 : (oneImpl (.inr t)).run (union c) =
        (simulateQ SchemeHashSpec.romImpl (liftM (World.query (.inr t.2)))).run (union c) := rfl
    rw [e1, e2, simulateQ_spec_query, romImpl_inr_run (hs := SchemeHashSpec), roStep]
    rcases h : c t with _ | u
    · rcases h' : c (!t.1, t.2) with _ | v
      · rw [union_eq_none h h']
        simp only [unionStep, h, h', map_bind, map_pure, Prod.map_apply, id_eq]
        refine bind_congr fun u ↦ ?_
        rw [union_cacheQuery_of_none t u (union_eq_none h h')]
      · rw [union_eq_other h h']
        simp only [unionStep, h, h', map_pure, Prod.map_apply, id_eq]
        rw [union_cacheQuery_of_some t v (union_eq_other h h')]
    · rw [union_eq_of_some hc h]
      simp [unionStep, h]

/-- **The union world, read through the union of its caches, is the one-oracle world.** -/
theorem map_run_implU {α : Type} (X : OracleComp TSpec α) (c : TagSpec.QueryCache)
    (hc : Consistent c) :
    Prod.map id union <$> (simulateQ implU X).run c =
      (simulateQ SchemeHashSpec.romImpl (simulateQ untag X)).run (union c) := by
  rw [← QueryImpl.simulateQ_compose]
  exact map_run_simulateQ_eq_of_query_map_eq_inv' implU oneImpl Consistent union
    (fun t c hc ↦ implU_consistent t c hc) (fun t c hc ↦ implU_step t c hc) X c hc

theorem union_empty : union ∅ = ∅ := QueryCache.ext fun x ↦ by simp [union_apply]

/-- **One oracle against two**: an event of the output in the one-oracle world has at most its
probability in the two-oracle world plus that of an input asked under both tags. -/
theorem prEvent_untag_le {α : Type} (X : OracleComp TSpec α) (P : α → Prop) :
    Pr{let z ← (simulateQ SchemeHashSpec.romImpl (simulateQ untag X)).run ∅}[P z.1] ≤
      Pr{let z ← (simulateQ TagSpec.romImpl X).run ∅}[P z.1] +
        Pr{let z ← (simulateQ TagSpec.romImpl X).run ∅}[Bad z.2] := by
  have h := map_run_implU X ∅ consistent_empty
  rw [union_empty] at h
  rw [← h, prEvent_map]
  exact agreeUntilBad.prEvent_simulateQ_run_le_add_bad_right romImpl_preservesBad X ∅
    fun z ↦ P z.1

/-! ## The private oracle, sampled by the computation itself -/

/-- **The private oracle inside the computation**: coins and real queries forwarded, a private
query answered by a lazily sampled random oracle whose cache is the state, its fresh answers drawn
with coins. -/
noncomputable def inner : QueryImpl TSpec (StateT SchemeHashSpec.QueryCache (OracleComp World))
  | .inl n => StateT.lift (liftM (World.query (.inl n)))
  | .inr t => if t.1 then StateT.mk fun c ↦
        (liftM ((SchemeHashSpec.randomOracle t.2).run c) : OracleComp World _)
      else StateT.lift (liftM (World.query (.inr t.2)))

theorem join_apply (cF cG : SchemeHashSpec.QueryCache) (t : Bool × List UInt8) :
    join cF cG t = if t.1 then cG t.2 else cF t.2 := rfl

theorem join_cacheQuery_false (cF cG : SchemeHashSpec.QueryCache) (x : List UInt8)
    (u : BitVec 256) : (join cF cG).cacheQuery (false, x) u = join (cF.cacheQuery x u) cG := by
  refine QueryCache.ext fun t ↦ ?_
  obtain ⟨b, y⟩ := t
  by_cases h : y = x
  · subst h; cases b <;> simp [join_apply]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp [h])]
    cases b <;> simp [join_apply, h]

theorem join_cacheQuery_true (cF cG : SchemeHashSpec.QueryCache) (x : List UInt8)
    (u : BitVec 256) : (join cF cG).cacheQuery (true, x) u = join cF (cG.cacheQuery x u) := by
  refine QueryCache.ext fun t ↦ ?_
  obtain ⟨b, y⟩ := t
  by_cases h : y = x
  · subst h; cases b <;> simp [join_apply]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp [h])]
    cases b <;> simp [join_apply, h]

/-- The rearrangement of the nested run's output and caches. -/
def flat {α : Type} (z : (α × SchemeHashSpec.QueryCache) × SchemeHashSpec.QueryCache) :
    α × TagSpec.QueryCache :=
  (z.1.1, join z.2 z.1.2)

theorem inner_step (t : TSpec.Domain) (cF cG : SchemeHashSpec.QueryCache) :
    flat <$> (simulateQ SchemeHashSpec.romImpl ((inner t).run cG)).run cF =
      (TagSpec.romImpl t).run (join cF cG) := by
  rcases t with n | ⟨b, x⟩
  · simp only [inner, StateT.run_lift, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      StateT.run_bind, roSim.run_apply_inl, bind_map_left, StateT.run_pure, map_bind, map_pure]
    rw [map_eq_bind_pure_comp]
    rfl
  · cases b
    · simp only [inner, Bool.false_eq_true, ↓reduceIte, StateT.run_lift, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
      rw [romImpl_inr_run (hs := SchemeHashSpec), romImpl_inr_run (hs := TagSpec), roStep, roStep]
      rw [show (join cF cG) (false, x) = cF x from rfl]
      rcases h : cF x with _ | u
      · simp only [bind_assoc, pure_bind, flat]
        refine bind_congr fun u ↦ ?_
        rw [join_cacheQuery_false]
      · simp [flat]
    · simp only [inner, ↓reduceIte, StateT.run_mk]
      have e : (SchemeHashSpec.randomOracle x).run cG = roStep x cG := romImpl_inr_run x cG
      rw [roSim.run_liftM, romImpl_inr_run (hs := TagSpec), roStep, e, roStep, Functor.map_map]
      rw [show (join cF cG) (true, x) = cG x from rfl]
      rcases h : cG x with _ | u
      · simp only [map_bind, map_pure, flat]
        refine bind_congr fun u ↦ ?_
        rw [join_cacheQuery_true]
      · simp [flat]

/-- **The private oracle sampled inside is a second random oracle**: the one-oracle run of the
computation that samples its private oracle itself is, rearranged, the two-oracle run. -/
theorem flatten {α : Type} (X : OracleComp TSpec α) (cF cG : SchemeHashSpec.QueryCache) :
    flat <$> (simulateQ SchemeHashSpec.romImpl ((simulateQ inner X).run cG)).run cF =
      (simulateQ TagSpec.romImpl X).run (join cF cG) := by
  induction X using OracleComp.inductionOn generalizing cF cG with
  | pure a => simp [flat]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, StateT.run_bind, map_bind]
    rw [← inner_step t cF cG, bind_map_left]
    refine bind_congr fun z ↦ ?_
    exact ih z.1.1 z.2 z.1.2

end Common.SufCma.MultiKey
