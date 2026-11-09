/-
  LeanVM.Protocol.Rpm.RomRelabel

  The random oracles of `common` (on bytes) against those of
  `LeanVM/Protocol/Rom/Statement.lean` (on lanes): a computation read through the bijections of
  `common`'s `Common/Lanes.lean` has the same distribution, the caches related by `cmap`; and the
  query count of the transfer's random-oracle adversary.
-/

import LeanVM.Protocol.Rpm.Game
import Common.Lemmas
import Common.RomComm
import LeanVM.Protocol.WithHash

/-!
# Relabelling the random oracles

* `run'_toRHF`: the verifier's queries read on bytes, against `common`'s two random oracles,
  give the verifier's outputs against the two random oracles of `Rom/Statement.lean`, the starting
  caches related by `cmap`.
* `run_ofRHF`: a computation on `common`'s oracles, its queries read on lanes, against the
  random oracles of `Rom/Statement.lean` (with coins), is the computation against `common`'s, its
  final cache read through `cmap`.
* `isWeightBound_romAdv`: the random-oracle adversary of the transfer (`romAdv`) makes at most
  one oracle query per query of the adversary to `π` or `π⁻¹`.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-! ## Caches -/

theorem cmap_empty : cmap ∅ = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s <;> rfl

@[simp] theorem cmap_inl (c : HFS.QueryCache) (m : Bytes) :
    cmap c (.inl m) = (c (.inl m)).map Digest.ofRpm := rfl

@[simp] theorem cmap_inr (c : HFS.QueryCache) (s : KeccakState) :
    cmap c (.inr s) = (c (.inr (KState.toRpm s))).map KState.ofRpm := rfl

theorem cmap_cacheQuery_inl (c : HFS.QueryCache) (m : Bytes) (u : Common.DigestBytes) :
    cmap (c.cacheQuery (.inl m) u) = (cmap c).cacheQuery (.inl m) (Digest.ofRpm u) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m' | s
  · by_cases h : m' = m
    · subst h; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmap_inl, cmap_inl,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h)]
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmap_inr, cmap_inr,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]

theorem cmap_cacheQuery_inr (c : HFS.QueryCache) (x u : Common.KState) :
    cmap (c.cacheQuery (.inr x) u) =
      (cmap c).cacheQuery (.inr (KState.ofRpm x)) (KState.ofRpm u) := by
  refine QueryCache.ext fun t ↦ ?_
  rcases t with m | s
  · rw [QueryCache.cacheQuery_of_ne _ _ (by simp), cmap_inl, cmap_inl,
      QueryCache.cacheQuery_of_ne _ _ (by simp)]
  · by_cases h : s = KState.ofRpm x
    · subst h
      rw [cmap_inr, toRpm_ofRpm, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
      rfl
    · have h' : KState.toRpm s ≠ x := fun e ↦ h (by rw [← e, ofRpm_toRpm])
      rw [QueryCache.cacheQuery_of_ne _ _ (by simpa using h), cmap_inr, cmap_inr,
        QueryCache.cacheQuery_of_ne _ _ (by simpa using h')]

theorem cmap_cacheQuery_inr' (c : HFS.QueryCache) (x : KeccakState) (u : Common.KState) :
    cmap (c.cacheQuery (.inr (KState.toRpm x)) u) =
      (cmap c).cacheQuery (.inr x) (KState.ofRpm u) := by
  have h := cmap_cacheQuery_inr c (KState.toRpm x) u
  rwa [ofRpm_toRpm] at h

/-! ## The verifier's queries read on bytes -/

theorem step_toRHF (t : KeccakCalls.Domain) (c : HFS.QueryCache) :
    Prod.map id cmap <$> ((HFS.romImpl ∘ₛ toRHF) t).run c =ᵈ
      (KeccakCalls.randomOracle t).run (cmap c) := by
  rcases t with m | x
  · rw [QueryImpl.apply_compose]
    simp only [toRHF, simulateQ_map, StateT.run_map, Common.run_hq, Functor.map_map]
    rw [randomOracle.run_eq, cmap_inl]
    rcases h : c (.inl m) with _ | u
    · simp only [Common.roStep_of_none h, Option.map_none, map_bind, map_pure, Prod.map,
        id, cmap_cacheQuery_inl]
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective digestEquiv.symm.bijective)
        (fun d ↦ (pure (d, (cmap c).cacheQuery (.inl m) d) : ProbComp _)))
      rw [bind_map_left]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, Option.map_some, map_pure]
      exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [toRHF, simulateQ_map, StateT.run_map, Common.run_hq, Functor.map_map]
    rw [randomOracle.run_eq, cmap_inr]
    rcases h : c (.inr (KState.toRpm x)) with _ | u
    · simp only [Common.roStep_of_none h, Option.map_none, map_bind, map_pure, Prod.map,
        id, cmap_cacheQuery_inr']
      refine EvalDistEq.trans ?_ (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective stateEquiv.symm.bijective)
        (fun d ↦ (pure (d, (cmap c).cacheQuery (.inr x) d) : ProbComp _)))
      rw [bind_map_left]
      exact EvalDistEq.rfl
    · simp only [Common.roStep_of_some h, Option.map_some, map_pure]
      exact EvalDistEq.rfl

/-- **(a) The verifier's queries read on bytes**: against `common`'s two random oracles, the
outputs are those against the two random oracles of `Rom/Statement.lean`, the caches related by
`cmap`. -/
theorem run'_toRHF {β : Type} (V : OracleComp KeccakCalls β) (c : HFS.QueryCache) :
    (simulateQ HFS.romImpl (simulateQ toRHF V)).run' c =ᵈ
      (simulateQ KeccakCalls.randomOracle V).run' (cmap c) := by
  rw [← QueryImpl.simulateQ_compose]
  exact Common.run'_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) cmap
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ step_toRHF t c) V c trivial

/-! ## Byte-oracle computations read on lanes -/

theorem cmap_inr_ofRpm (c : HFS.QueryCache) (x : Common.KState) :
    cmap c (.inr (KState.ofRpm x)) = (c (.inr x)).map KState.ofRpm := by
  rw [cmap_inr, toRpm_ofRpm]

theorem step_ofRHF (t : HFSpec.Domain) (c : HFS.QueryCache) :
    Prod.map id cmap <$> (HFS.romImpl t).run c =ᵈ
      ((KeccakCalls.romImpl ∘ₛ ofRHF) t).run (cmap c) := by
  rcases t with n | m | x
  · rw [QueryImpl.apply_compose]
    simp only [ofRHF, simulateQ_spec_query, roSim.run_apply_inl, Functor.map_map]
    exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [ofRHF, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      OracleSpec.romImpl_apply_inr, randomOracle.run_eq, cmap_inl]
    rcases h : c (.inl m) with _ | u
    · simp only [Option.map_none, map_bind, map_pure, Prod.map, id, cmap_cacheQuery_inl]
      refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective digestEquiv.symm.bijective).symm
        (fun d ↦ (pure (Digest.toRpm d, (cmap c).cacheQuery (.inl m) d) : ProbComp _))) ?_)
      rw [bind_map_left]
      simp only [digestEquiv_symm_apply, digestToRpm_ofRpm]
      exact EvalDistEq.rfl
    · simp only [Option.map_some, map_pure, Prod.map, id, digestToRpm_ofRpm]
      exact EvalDistEq.rfl
  · rw [QueryImpl.apply_compose]
    simp only [ofRHF, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      OracleSpec.romImpl_apply_inr, randomOracle.run_eq, cmap_inr_ofRpm]
    rcases h : c (.inr x) with _ | u
    · simp only [Option.map_none, map_bind, map_pure, Prod.map, id, cmap_cacheQuery_inr]
      refine EvalDistEq.symm (EvalDistEq.trans (EvalDistEq.bind_left
        (SampleableType.map_uniformSample_evalDistEq_of_bijective stateEquiv.symm.bijective).symm
        (fun d ↦ (pure (KState.toRpm d, (cmap c).cacheQuery (.inr (KState.ofRpm x)) d) :
          ProbComp _))) ?_)
      rw [bind_map_left]
      simp only [stateEquiv_symm_apply, toRpm_ofRpm]
      exact EvalDistEq.rfl
    · simp only [Option.map_some, map_pure, Prod.map, id, toRpm_ofRpm]
      exact EvalDistEq.rfl

/-- **(b) A computation on the byte oracles, read on lanes**: against the random oracles of
`Rom/Statement.lean` (with coins), it is the computation against `common`'s two random oracles, the
final cache read through `cmap`. -/
theorem run_ofRHF {α : Type} (X : OracleComp HFSpec α) (c : HFS.QueryCache) :
    (simulateQ KeccakCalls.romImpl (simulateQ ofRHF X)).run (cmap c) =ᵈ
      Prod.map id cmap <$> (simulateQ HFS.romImpl X).run c := by
  rw [← QueryImpl.simulateQ_compose]
  exact (Common.map_run_simulateQ_evalDistEq_of_inv _ _ (fun _ ↦ True) cmap
    (fun _ _ _ _ _ ↦ trivial) (fun t c _ ↦ step_ofRHF t c) X c trivial).symm

/-! ## The query count of the random-oracle adversary -/

/-- Oracle calls of the adversary on bytes: a hash or permutation query one, a coin nothing. -/
def wR : RSpec.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Oracle calls on the byte random oracles: a hash or permutation call one, a coin nothing. -/
def wHF : HFSpec.Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem isWeightBound_one_of_total {ι : Type} {spec : OracleSpec ι} {α : Type}
    {oa : OracleComp spec α} {Q : ℕ} (h : oa.IsTotalQueryBound Q) :
    Common.QueryCostAtMost oa (fun _ ↦ 1) Q := by
  induction oa using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    rw [Common.isWeightBound_query_bind_iff]
    exact ⟨h.1, fun u ↦ ih u (h.2 u)⟩

theorem isWeightBound_advR {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (advR A) wR Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) wR (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query wR (.inr (.inr (permQueryToRpm q)))))

theorem isWeightBound_liftM_probComp_hf {β : Type} (p : ProbComp β) :
    Common.QueryCostAtMost (liftM p : OracleComp HFSpec β) wHF 0 :=
  Common.isWeightBound_liftM_probComp wHF (fun _ ↦ rfl) p

/-- Each step of the adversary with the simulator makes at most one call of the byte random
oracles, none for a coin. -/
theorem isWeightBound_advImpl2 (t : RSpec.Domain)
    (s : Common.SimState Common.DigestBytes Common.KRest Common.KCap) :
    Common.QueryCostAtMost ((Common.advImpl2 Common.keccakPadding t).run s) wHF (wR t) := by
  rcases t with n | m | q
  · simp only [Common.advImpl2, StateT.run_monadLift, monadLift_self]
    exact (isWeightBound_liftM_probComp_hf _).bind fun _ ↦ Common.isWeightBound_pure _ _ 0
  · simp only [Common.advImpl2, StateT.run_monadLift, monadLift_self]
    exact (Common.isWeightBound_query wHF (.inr (.inl m))).bind fun _ ↦
      Common.isWeightBound_pure _ _ 0
  · cases q with
    | forward x =>
      simp only [Common.advImpl2, Common.simulator2, StateT.run_mk]
      split
      · trivial
      · split
        · refine (Common.QueryCostAtMost.bind (b := 0) ?_ fun _ ↦ Common.isWeightBound_pure _ _ 0)
          unfold Common.rootedAnswer2
          split
          · exact ((Common.isWeightBound_query wHF (.inr (.inl _))).bind fun _ ↦
              (isWeightBound_liftM_probComp_hf _).bind fun _ ↦ Common.isWeightBound_pure _ _ 0)
          · exact Common.isWeightBound_query wHF (.inr (.inr _))
        · exact (Common.isWeightBound_query wHF (.inr (.inr _))).bind fun _ ↦
            Common.isWeightBound_pure _ _ 0
    | inverse y =>
      simp only [Common.advImpl2, Common.simulator2, StateT.run_mk]
      split
      · trivial
      · exact ((isWeightBound_liftM_probComp_hf _).bind fun _ ↦
          Common.isWeightBound_pure _ _ 0).mono (Nat.zero_le _)

theorem isWeightBound_simulateQ_ofRHF {β : Type} {Y : OracleComp HFSpec β} {Q : ℕ}
    (h : Common.QueryCostAtMost Y wHF Q) :
    Common.QueryCostAtMost (simulateQ ofRHF Y) hashCalls Q := by
  induction Y using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    have hstep : Common.QueryCostAtMost (ofRHF t) hashCalls (wHF t) := by
      rcases t with n | m | x
      · exact Common.isWeightBound_query hashCalls (.inl n)
      · exact Common.isWeightBound_map _ (Common.isWeightBound_query hashCalls (.inr (.inl m)))
      · exact Common.isWeightBound_map _
          (Common.isWeightBound_query hashCalls (.inr (.inr (KState.ofRpm x))))
    exact (hstep.bind fun u ↦ ih u (h.2 u)).mono (by omega)

/-- **(c) The random-oracle adversary of the transfer makes at most one oracle query per query
of the adversary to `π` or `π⁻¹`.** -/
theorem isWeightBound_romAdv {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (romAdv A) hashCalls Q := by
  refine Common.isWeightBound_map _ (isWeightBound_simulateQ_ofRHF ?_)
  rw [Common.advS2, StateT.run'_eq]
  exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ wR wHF
    isWeightBound_advImpl2 (isWeightBound_advR hA) _)

end LeanVM.Rpm
