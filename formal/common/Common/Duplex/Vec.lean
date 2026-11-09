module

public import Common.Duplex.Main
public import Common.Rerun
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Common.Defs

@[expose] public section

/-!
# The challenges as one random oracle of vectors

The duplex lemma (`duplex_le`) gives the challenges of a root `r` as the components `G (r, j)` of
a random oracle on `Root × Fin n`. Running a computation with such a `G` is, in distribution,
running it with a random oracle `V` from roots to vectors, `G (r, j)` read as `V r j`
(`run'_romImpl_evalDistEq_vec`): sampled in advance, the tables `g (r, j)` and `v r j` are the
same uniform table up to currying. The order of the random oracles of a sum does not matter
(`run'_romImpl_evalDistEq_swap`).
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec
open Common
open Common.Duplex (GSpec hP gaP VSpec toV)
open scoped ENNReal

namespace Common

section Swap

variable {ι₁ ι₂ : Type} [DecidableEq ι₁] [DecidableEq ι₂] {hs₁ : OracleSpec.{0, 0} ι₁}
  {hs₂ : OracleSpec.{0, 0} ι₂} [∀ t : hs₁.Domain, SampleableType (hs₁.Range t)]
  [∀ t : hs₂.Domain, SampleableType (hs₂.Range t)]

/-- A cache of a sum, in the other order. -/
def swapCache (c : (hs₁ + hs₂).QueryCache) : (hs₂ + hs₁).QueryCache :=
  QueryCache.ofFn fun t ↦ match t with
    | .inl t => c (.inr t)
    | .inr t => c (.inl t)

theorem swapCache_cacheQuery_inl (c : (hs₁ + hs₂).QueryCache) (t : ι₁) (u : hs₁.Range t) :
    swapCache (c.cacheQuery (.inl t) u) = (swapCache c).cacheQuery (.inr t) u := by
  ext s
  rcases s with s | s
  · simp [swapCache]
  · by_cases h : s = t
    · subst h; simp [swapCache]
    · simp [swapCache, h]

theorem swapCache_cacheQuery_inr (c : (hs₁ + hs₂).QueryCache) (t : ι₂) (u : hs₂.Range t) :
    swapCache (c.cacheQuery (.inr t) u) = (swapCache c).cacheQuery (.inl t) u := by
  ext s
  rcases s with s | s
  · by_cases h : s = t
    · subst h; simp [swapCache]
    · simp [swapCache, h]
  · simp [swapCache]

/-- **The order of the random oracles does not matter.** -/
theorem run'_romImpl_evalDistEq_swap {α : Type} (X : OracleComp (unifSpec + (hs₁ + hs₂)) α)
    (c : (hs₁ + hs₂).QueryCache) :
    (simulateQ (hs₁ + hs₂).romImpl X).run' c =ᵈ
      (simulateQ (hs₂ + hs₁).romImpl (simulateQ swapImpl X)).run' (swapCache c) := by
  rw [← QueryImpl.simulateQ_compose]
  refine run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) swapCache (fun _ _ _ _ _ ↦ trivial)
    (fun t c _ ↦ ?_) X c trivial
  rcases t with k | t | t
  · simp only [QueryImpl.apply_compose, swapImpl, simulateQ_spec_query]
    rw [show ((hs₁ + hs₂).romImpl (.inl k)).run c = (·, c) <$> (unifSpec.query k : ProbComp _) from
      unifFwdImpl.simulateQ_run (hashSpec := hs₁ + hs₂) (unifSpec.query k : ProbComp _) c,
      show ((hs₂ + hs₁).romImpl (.inl k)).run (swapCache c) =
        (·, swapCache c) <$> (unifSpec.query k : ProbComp _) from
      unifFwdImpl.simulateQ_run (hashSpec := hs₂ + hs₁) (unifSpec.query k : ProbComp _) _]
    rw [Functor.map_map]
    exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, swapImpl, simulateQ_spec_query, romImpl_apply_inr,
      randomOracle.run_eq]
    have hsw : (swapCache c) (.inr t) = c (.inl t) := rfl
    rw [hsw]
    rcases h : c (.inl t) with _ | u
    · simp only [map_bind, map_pure, Prod.map_apply, id_eq, swapCache_cacheQuery_inl]
      exact EvalDistEq.rfl
    · simp only [map_pure, Prod.map_apply, id_eq]
      exact EvalDistEq.rfl
  · simp only [QueryImpl.apply_compose, swapImpl, simulateQ_spec_query, romImpl_apply_inr,
      randomOracle.run_eq]
    have hsw : (swapCache c) (.inl t) = c (.inr t) := rfl
    rw [hsw]
    rcases h : c (.inr t) with _ | u
    · simp only [map_bind, map_pure, Prod.map_apply, id_eq, swapCache_cacheQuery_inr]
      exact EvalDistEq.rfl
    · simp only [map_pure, Prod.map_apply, id_eq]
      exact EvalDistEq.rfl

theorem swapCache_empty : swapCache (∅ : (hs₁ + hs₂).QueryCache) = ∅ := by
  ext s; rcases s with s | s <;> rfl

end Swap

end Common

namespace Common.SeedDuplex

variable {Msg Dg Root Z : Type} {n : ℕ}
  [DecidableEq Msg] [DecidableEq Root] [SampleableType Dg] [SampleableType Z]
  [Fintype Z] [Fintype Root] [Nonempty Z]

/-- The table of challenges of a table of vectors. -/
def tabOfV (v : Subtype (fun _ : Root ↦ True) → (Fin n → Z)) : Tab Root Z n :=
  fun rj ↦ v ⟨rj.1.1, trivial⟩ rj.1.2

theorem tabOfV_bijective : Function.Bijective (tabOfV (Root := Root) (Z := Z) (n := n)) := by
  refine ⟨fun v v' h ↦ funext fun r ↦ funext fun j ↦ ?_, fun g ↦ ⟨fun r j ↦ g ⟨(r.1, j), trivial⟩,
    funext fun _ ↦ rfl⟩⟩
  exact congrFun h ⟨(r.1, j), trivial⟩

/-- The `H` part of a cache. -/
def projV (c : (GSpec Msg Dg Root Z n).QueryCache) : (VSpec Msg Dg Root Z n).QueryCache :=
  QueryCache.ofFn fun t ↦ match t with
    | .inl m => c (.inl m)
    | .inr _ => none

theorem projV_cacheQuery (c : (GSpec Msg Dg Root Z n).QueryCache) (m : Msg) (u : Dg) :
    projV (c.cacheQuery (.inl m) u) = (projV c).cacheQuery (.inl m) u := by
  ext s
  rcases s with s | s
  · by_cases h : s = m
    · subst h; simp [projV]
    · simp [projV, h]
  · simp [projV]

theorem projV_empty : projV (∅ : (GSpec Msg Dg Root Z n).QueryCache) = ∅ := by
  ext s; rcases s with s | s <;> rfl

/-- With the tables sampled in advance, the vector oracle is the per-challenge one. -/
theorem run'_eagerImpl_toV {α : Type} (v : Subtype (fun _ : Root ↦ True) → (Fin n → Z))
    (X : OracleComp (unifSpec + GSpec Msg Dg Root Z n) α) :
    (simulateQ (tabOuter (Msg := Msg) (Dg := Dg) (tabOfV v)) X).run' ∅ =ᵈ
      (simulateQ (eagerImpl (hs := roSpec Msg Dg) (fun _ : Root ↦ True) v)
        (simulateQ toV X)).run' ∅ := by
  rw [← QueryImpl.simulateQ_compose]
  have h := run'_simulateQ_evalDistEq_of_inv (tabOuter (Msg := Msg) (Dg := Dg) (tabOfV v))
    (eagerImpl (hs := roSpec Msg Dg) (fun _ : Root ↦ True) v ∘ₛ toV) GFree projV ?_ ?_ X ∅
    (fun _ ↦ rfl)
  · rwa [projV_empty] at h
  · intro t c hc z hz
    rcases t with k | m | rj
    · change z ∈ support ((unifFwdImpl _ k).run c) at hz
      rw [unifFwd_run, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hc
    · rcases mem_support_randomOracle_run hz with h | ⟨u, h⟩
      · rw [h]; exact hc
      · intro d; rw [h, QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hc d
    · simp only [eagerImpl, ↓reduceDIte, StateT.run_mk, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz; exact hc
  · intro t c hc
    rcases t with k | m | rj
    · simp only [QueryImpl.apply_compose, toV, simulateQ_spec_query]
      change _ <$> (unifFwdImpl _ k).run c =ᵈ (unifFwdImpl _ k).run _
      rw [unifFwd_run, unifFwd_run, Functor.map_map]
      exact EvalDistEq.rfl
    · simp only [QueryImpl.apply_compose, toV, simulateQ_spec_query]
      change _ <$> ((GSpec Msg Dg Root Z n).randomOracle (.inl m)).run c =ᵈ
        ((VSpec Msg Dg Root Z n).randomOracle (.inl m)).run (projV c)
      rw [randomOracle.run_eq, randomOracle.run_eq]
      have hp : (projV c) (.inl m) = c (.inl m) := rfl
      rw [hp]
      rcases h : c (.inl m) with _ | u
      · simp only [map_bind, map_pure, Prod.map_apply, id_eq, projV_cacheQuery]
        exact EvalDistEq.rfl
      · simp only [map_pure, Prod.map_apply, id_eq]
        exact EvalDistEq.rfl
    · obtain ⟨r, j⟩ := rj
      simp only [QueryImpl.apply_compose, toV, simulateQ_map, simulateQ_spec_query]
      simp [eagerImpl, hc (r, j), tabOfV, projV]

/-- **The challenges as one random oracle of vectors.** -/
theorem run'_romImpl_evalDistEq_vec {α : Type} (X : OracleComp (unifSpec + GSpec Msg Dg Root Z n) α) :
    (simulateQ (GSpec Msg Dg Root Z n).romImpl X).run' ∅ =ᵈ
      (simulateQ (VSpec Msg Dg Root Z n).romImpl (simulateQ toV X)).run' ∅ := by
  refine (run'_romImpl_evalDistEq_eager (fun _ : Root × Fin n ↦ True) X ∅).trans ?_
  refine EvalDistEq.trans ?_ (run'_romImpl_evalDistEq_eager (fun _ : Root ↦ True)
    (simulateQ toV X) ∅).symm
  refine (EvalDistEq.bind_left (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (tabOfV_bijective (Root := Root) (Z := Z) (n := n))).symm _).trans ?_
  rw [bind_map_left]
  exact EvalDistEq.bind_right _ fun v ↦ run'_eagerImpl_toV v X

/-! ## Coins and weights -/

section Weights

variable {St W Cp : Type} [DecidableEq St] [DecidableEq Cp] [SampleableType St]
  [SampleableType W] [Fintype St] [Fintype W]
  {D : DuplexSpec Msg Dg St Root Z W Cp n}

theorem noCoins_chainP (k : ℕ) (y : St) :
    NoCoins (hs := hfSpec Msg Dg St) (chainP (Msg := Msg) (Dg := Dg) D k y) := by
  induction k generalizing y with
  | zero => trivial
  | succ k ih =>
    unfold chainP
    exact (noCoins_hq_bind (hs := hfSpec Msg Dg St) (.inr (D.next y)) _).mpr fun y' ↦
      noCoins_bind (ih y') fun _ ↦ trivial

/-- **The challenges flip no coins.** -/
theorem noCoins_chalP (r : Root) : NoCoins (hs := hfSpec Msg Dg St) (chalP D r) := by
  unfold chalP
  exact (noCoins_hq_bind (hs := hfSpec Msg Dg St) (.inl D.label) _).mpr fun iv ↦
    (noCoins_hq_bind (hs := hfSpec Msg Dg St) (.inr (D.first r iv)) _).mpr fun (y₁ : St) ↦
      noCoins_bind (noCoins_chainP (n - 1) y₁) fun _ ↦ trivial

/-- Queries of the challenges `G`, one each. -/
def gCalls : (unifSpec + GSpec Msg Dg Root Z n).Domain → ℕ
  | .inr (.inr _) => 1
  | _ => 0

/-- **Each step of the simulator makes at most one query of `G`**, and only for a call of `F`. -/
theorem isWeightBound_simImpl (t : (Rom2 Msg Dg St).Domain) (s : SimSt Dg St Root n) :
    QueryCostAtMost ((simImpl D hP gaP t).run s) (gCalls (Msg := Msg) (Dg := Dg) (Root := Root)
      (Z := Z) (n := n)) (fCalls (Msg := Msg) (Dg := Dg) (St := St) t) := by
  have hu : ∀ {β : Type} (p : ProbComp β),
      QueryCostAtMost (liftM p : OracleComp (unifSpec + GSpec Msg Dg Root Z n) β) gCalls 0 :=
    fun p ↦ isWeightBound_liftM_probComp gCalls (fun _ ↦ rfl) p
  rcases t with k | m | x
  · simp only [simImpl, StateT.run_monadLift, monadLift_self]
    exact (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0
  · simp only [simImpl, StateT.run_mk]
    exact ((isWeightBound_query gCalls (.inr (.inl m))).bind fun _ ↦
      isWeightBound_pure _ _ 0)
  · simp only [simImpl, StateT.run_mk]
    split
    · trivial
    · refine (QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ isWeightBound_pure _ _ 0)
      unfold freshAns
      split
      · split
        · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)
        · exact ((isWeightBound_query gCalls (.inr (.inr _))).bind fun _ ↦
            (hu _).bind fun _ ↦ isWeightBound_pure _ _ 0)
      · exact (isWeightBound_map _ (hu _)).mono (Nat.zero_le _)

end Weights

end Common.SeedDuplex
