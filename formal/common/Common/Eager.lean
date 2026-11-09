module

public import Common.RomComm
public import Common.Fold
public import VCVio.EvalDist.Monad.UniformTable

@[expose] public section

/-!
# Eager sampling of part of a random oracle

For a random oracle `D → R` next to other random oracles `hs`, the answers on a finite part
`{d // P d}` of `D` may be sampled in advance as a uniform table `g`: running a computation in
the random oracle model is, in distribution, sampling `g` and then running it with the `P`-part of
`D` answered by `g` (cached answers first) and the rest lazily (`run'_romImpl_evalDistEq_eager`).
This is the lazy/eager sampling principle, restricted to a finite subdomain of a possibly infinite
one.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Eager

variable {ι : Type} [DecidableEq ι] {hs : OracleSpec.{0, 0} ι}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]
  {D R : Type} [DecidableEq D] [SampleableType R] [Fintype R] [Nonempty R]
  (P : D → Prop) [DecidablePred P] [Fintype {d // P d}]

/-- The oracles: coins, the random oracles `hs`, and the random oracle `D → R`. -/
abbrev EagerSpec (hs : OracleSpec.{0, 0} ι) (D R : Type) := unifSpec + (hs + (D →ₒ R))

/-- **The random oracle with its `P`-part a table `g`**: a `P`-point is answered from the cache if
cached, else by `g`, and never cached; every other query is the lazy random oracle. -/
noncomputable def eagerImpl (g : {d // P d} → R) :
    QueryImpl (EagerSpec hs D R) (StateT (hs + (D →ₒ R)).QueryCache ProbComp)
  | .inl n => unifFwdImpl _ n
  | .inr (.inl t) => (hs + (D →ₒ R)).randomOracle (.inl t)
  | .inr (.inr d) =>
      if h : P d then StateT.mk fun c ↦ pure (((c (.inr d)).getD (g ⟨d, h⟩)), c)
      else (hs + (D →ₒ R)).randomOracle (.inr d)

omit [SampleableType R] [Fintype R] [Nonempty R] [Fintype {d // P d}] in
theorem randomOracle_run_comm (t : ι ⊕ D) (d : D) (ht : t ≠ .inr d)
    (c : (hs + (D →ₒ R)).QueryCache) (u : R) [SampleableType R] :
    Prod.map id (fun c' ↦ c'.cacheQuery (.inr d) u) <$>
        ((hs + (D →ₒ R)).randomOracle t).run c =
      ((hs + (D →ₒ R)).randomOracle t).run (c.cacheQuery (.inr d) u) := by
  rw [randomOracle.run_eq, randomOracle.run_eq, QueryCache.cacheQuery_of_ne _ _ ht]
  rcases h : c t with _ | v
  · simp only [map_bind, map_pure, Prod.map_apply, id_eq]
    refine bind_congr fun w ↦ ?_
    rw [QueryCache.cacheQuery_comm _ (Ne.symm ht)]
  · simp

omit [Fintype R] [Nonempty R] [Fintype {d // P d}] in
theorem mem_support_randomOracle_run {t : ι ⊕ D} {c : (hs + (D →ₒ R)).QueryCache} {z}
    (hz : z ∈ support (((hs + (D →ₒ R)).randomOracle t).run c)) :
    z.2 = c ∨ ∃ v, z.2 = c.cacheQuery t v := by
  rw [randomOracle.run_eq] at hz
  rcases h : c t with _ | v
  · simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inr ⟨w, rfl⟩
  · simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl rfl

omit [Fintype R] [Nonempty R] [Fintype {d // P d}] in
theorem unifFwd_run (n : ℕ) (c : (hs + (D →ₒ R)).QueryCache) :
    (unifFwdImpl (hs + (D →ₒ R)) n).run c =
      (·, c) <$> (unifSpec.query n : ProbComp (Fin (n + 1))) := by
  simpa using unifFwdImpl.simulateQ_run (hashSpec := hs + (D →ₒ R))
    (unifSpec.query n : ProbComp (Fin (n + 1))) c

omit [Fintype R] [Nonempty R] [Fintype {d // P d}] in
/-- Coins leave the cache unchanged. -/
theorem simulateQ_eagerImpl_liftM (g : {d // P d} → R) {α : Type} (p : ProbComp α)
    (c : (hs + (D →ₒ R)).QueryCache) :
    (simulateQ (eagerImpl P g) (liftM p : OracleComp (EagerSpec hs D R) α)).run c =
      (·, c) <$> p := by
  change (simulateQ (eagerImpl P g) (OracleComp.liftComp p _)).run c = _
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (eagerImpl P g) (unifFwdImpl _)
    (fun _ ↦ rfl)]
  exact unifFwdImpl.simulateQ_run p c

/-- Moving a cached `P`-answer into the table. -/
theorem run'_eagerImpl_cacheQuery (g : {d // P d} → R) (d : D) (hd : P d) (u : R)
    {α : Type} (Y : OracleComp (EagerSpec hs D R) α) (c : (hs + (D →ₒ R)).QueryCache)
    (hc : c (.inr d) = none) :
    (simulateQ (eagerImpl P g) Y).run' (c.cacheQuery (.inr d) u) =ᵈ
      (simulateQ (eagerImpl P (Function.update g ⟨d, hd⟩ u)) Y).run' c := by
  refine (run'_simulateQ_evalDistEq_of_inv (eagerImpl P (Function.update g ⟨d, hd⟩ u))
    (eagerImpl P g) (fun c ↦ c (.inr d) = none) (fun c ↦ c.cacheQuery (.inr d) u)
    ?_ ?_ Y c hc).symm
  · intro t s hsd z hz
    rcases t with n | t | d'
    · change z ∈ support ((unifFwdImpl _ n).run s) at hz
      rw [unifFwd_run, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hsd
    · rcases mem_support_randomOracle_run hz with h | ⟨v, h⟩
      · rw [h]; exact hsd
      · rw [h, QueryCache.cacheQuery_of_ne _ _ (by simp)]; exact hsd
    · simp only [eagerImpl] at hz
      split at hz
      · simp only [StateT.run_mk, support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact hsd
      · next hd' =>
        rcases mem_support_randomOracle_run hz with h | ⟨v, h⟩
        · rw [h]; exact hsd
        · rw [h, QueryCache.cacheQuery_of_ne _ _ (by rintro ⟨⟩; exact hd' hd)]; exact hsd
  · intro t s hsd
    rcases t with n | t | d'
    · change _ <$> (unifFwdImpl _ n).run s =ᵈ (unifFwdImpl _ n).run _
      rw [unifFwd_run, unifFwd_run, Functor.map_map]
      exact EvalDistEq.rfl
    · exact (randomOracle_run_comm (.inl t) d (by simp) s u) ▸ EvalDistEq.rfl
    · simp only [eagerImpl]
      split
      · next hd' =>
        simp only [StateT.run_mk, map_pure, Prod.map_apply, id_eq]
        by_cases hdd : d' = d
        · subst hdd
          simp [hsd]
        · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using hdd)]
          have : (⟨d', hd'⟩ : {d // P d}) ≠ ⟨d, hd⟩ := fun h ↦ hdd (congrArg Subtype.val h)
          simp [Function.update_of_ne this]
      · next hd' =>
        exact (randomOracle_run_comm (.inr d') d (by rintro ⟨⟩; exact hd' hd) s u) ▸ EvalDistEq.rfl

/-- Resampling one cell of a uniform table, in distribution. -/
theorem uniform_update_evalDistEq {α : Type} (d : {d // P d})
    (ψ : ({d // P d} → R) → ProbComp α) :
    (($ᵗ R : ProbComp R) >>= fun u ↦ ($ᵗ ({d // P d} → R) : ProbComp _) >>= fun g ↦
        ψ (Function.update g d u)) =ᵈ (($ᵗ ({d // P d} → R) : ProbComp _) >>= ψ) := by
  let : MeasurableSpace R := ⊤
  let : MeasurableSpace α := ⊤
  exact _root_.EvalDistEq.of_evalDist_eq (evalDist_bind_bind_update _ _
    SampleableType.evalDist_uniformSample SampleableType.evalDist_uniformSample d ψ)

theorem common_step_evalDistEq {β γ : Type} (step : ProbComp β) (f : β → ProbComp γ)
    (f' : ({d // P d} → R) → β → ProbComp γ)
    (h : ∀ b, f b =ᵈ (($ᵗ ({d // P d} → R) : ProbComp _) >>= fun g ↦ f' g b)) :
    (step >>= f) =ᵈ (($ᵗ ({d // P d} → R) : ProbComp _) >>= fun g ↦ step >>= f' g) :=
  (EvalDistEq.bind_right _ h).trans (EvalDistEq.bind_bind_swap _ _ _)

/-- **Eager sampling of the `P`-part of a random oracle.** -/
theorem run'_romImpl_evalDistEq_eager {α : Type} (X : OracleComp (EagerSpec hs D R) α)
    (c : (hs + (D →ₒ R)).QueryCache) :
    (simulateQ (hs + (D →ₒ R)).romImpl X).run' c =ᵈ
      (($ᵗ ({d // P d} → R) : ProbComp _) >>= fun g ↦ (simulateQ (eagerImpl P g) X).run' c) := by
  induction X using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run'_eq, StateT.run_bind, map_bind]
    simp only [← StateT.run'_eq]
    rcases t with n | t | d
    · exact common_step_evalDistEq P ((unifFwdImpl _ n).run c) _ _ fun a ↦ ih a.1 a.2
    · exact common_step_evalDistEq P (((hs + (D →ₒ R)).randomOracle (.inl t)).run c) _ _
        fun a ↦ ih a.1 a.2
    · by_cases hd : P d
      · have h1 : ∀ g, (eagerImpl P g (.inr (.inr d))).run c =
            pure ((c (.inr d)).getD (g ⟨d, hd⟩), c) := fun g ↦ by simp [eagerImpl, hd]
        simp only [h1, pure_bind]
        change ((((hs + (D →ₒ R)).randomOracle (.inr d)).run c) >>= _) =ᵈ _
        rw [randomOracle.run_eq]
        rcases hc : c (.inr d) with _ | v
        · simp only [bind_assoc, pure_bind, Option.getD_none]
          let ψ : ({d // P d} → R) → ProbComp α := fun g ↦
            (simulateQ (eagerImpl P g) (k (g ⟨d, hd⟩))).run' c
          refine (EvalDistEq.bind_right _ fun u ↦ (ih u _).trans (EvalDistEq.bind_right _
            fun g ↦ run'_eagerImpl_cacheQuery P g d hd u (k u) c hc)).trans ?_
          have h2 : ∀ (u : R) (g : {d // P d} → R),
              (simulateQ (eagerImpl P (Function.update g ⟨d, hd⟩ u)) (k u)).run' c =
                ψ (Function.update g ⟨d, hd⟩ u) := fun u g ↦ by simp [ψ]
          simp only [h2]
          exact uniform_update_evalDistEq P ⟨d, hd⟩ ψ
        · simp only [pure_bind, Option.getD_some]
          exact ih v c
      · have h1 : ∀ g, eagerImpl P g (.inr (.inr d)) = (hs + (D →ₒ R)).randomOracle (.inr d) :=
          fun g ↦ by simp [eagerImpl, hd]
        simp only [h1]
        exact common_step_evalDistEq P (((hs + (D →ₒ R)).randomOracle (.inr d)).run c) _ _
          fun a ↦ ih a.1 a.2

end Eager

end Common
