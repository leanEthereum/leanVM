/-
  LeanVM.Protocol.Rpm.ExtractF

  In the transfer's random-oracle world, every `F` answer the adversary's simulator cached is the
  answer of the first forward query of its transcript at that input.
-/

module

public import LeanVM.Protocol.Rpm.Extract

@[expose] public section

/-!
# The transcript's forward answers hold the adversary's `F` answers

The two-oracle simulator (`Common.simulator2`) queries `F x` only to answer a forward query at an
input `x` no edge holds yet, and books the edge `(x, F x)`; an inverse query samples its answer
and touches no oracle. So, along the adversary's run, every forward query of the log has an edge,
and every cached `F` answer is the answer of the log's first forward query at its input
(`FInv`, `fInv_step`, `fInv_run`). Read on lanes: `cacheF_firstForward`. The agreement-set
extractor in the random-permutation model reads the permutation's answers there
(`firstForward`), where the extractor of the random-oracle model reads the cache.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- The answer of the first forward query of a byte log at `x`. -/
def firstFwdB (log : RLog) (x : Common.KState) : Option Common.KState :=
  (log.find? fun e ↦ decide (e.1 = .forward x)).map (·.2)

/-- **The answer of the first forward query of a transcript at `x`.** -/
def firstForward (T : PermutationTranscript) (x : KeccakState) : Option KeccakState :=
  (T.find? fun e ↦ decide (e.1 = .forward x)).map (·.2)

theorem firstFwdB_append_of_some {log : RLog} {x y : Common.KState} (h : firstFwdB log x = some y)
    (e : Common.PermutationQuery Common.KState × Common.KState) :
    firstFwdB (log ++ [e]) x = some y := by
  unfold firstFwdB at h ⊢
  obtain ⟨e', he', rfl⟩ := Option.map_eq_some_iff.mp h
  rw [List.find?_append, he']
  rfl

theorem firstFwdB_append_self {log : RLog} {x y : Common.KState}
    (h : ∀ y', (Common.PermutationQuery.forward x, y') ∉ log) :
    firstFwdB (log ++ [(.forward x, y)]) x = some y := by
  unfold firstFwdB
  have hn : log.find? (fun e ↦ decide (e.1 = .forward x)) = none := by
    refine List.find?_eq_none.mpr fun e he hex ↦ ?_
    simp only [decide_eq_true_eq] at hex
    obtain ⟨q, y'⟩ := e
    simp only at hex
    subst hex
    exact h y' he
  rw [List.find?_append, hn]
  simp

theorem not_mem_of_firstFwdB_none {log : RLog} {x : Common.KState} (h : firstFwdB log x = none)
    (y : Common.KState) : (Common.PermutationQuery.forward x, y) ∉ log := by
  intro hm
  unfold firstFwdB at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  exact h _ hm (by simp)

theorem isSome_forwardLookup_cons {E : Common.PermutationEdges Common.KState} {x : Common.KState}
    (h : (Common.forwardLookup E x).isSome) (a b : Common.KState) :
    (Common.forwardLookup ((a, b) :: E) x).isSome := by
  simp only [Common.forwardLookup]
  split <;> simp_all

theorem Common.forwardLookup_cons_self (E : Common.PermutationEdges Common.KState) (x y : Common.KState) :
    Common.forwardLookup ((x, y) :: E) x = some y := by
  simp [Common.forwardLookup]

/-- **The invariant**: every forward query of the log has an edge, and every cached `F` answer is
the answer of the log's first forward query at its input. -/
def FInv (σ : KSim) (log : RLog) (c : HFS.QueryCache) : Prop :=
  (∀ x y, (Common.PermutationQuery.forward x, y) ∈ log → (Common.forwardLookup σ.edges x).isSome) ∧
    ∀ x y, c (.inr x) = some y → firstFwdB log x = some y

/-- At an input no edge holds, the log has no forward query and the cache no `F` answer. -/
theorem FInv.fresh {σ : KSim} {log : RLog} {c : HFS.QueryCache} (h : FInv σ log c)
    {x : Common.KState} (hx : Common.forwardLookup σ.edges x = none) :
    (∀ y, (Common.PermutationQuery.forward x, y) ∉ log) ∧ c (.inr x) = none := by
  have hlog : ∀ y, (Common.PermutationQuery.forward x, y) ∉ log := fun y hy ↦ by
    have := h.1 x y hy
    rw [hx] at this
    cases this
  refine ⟨hlog, ?_⟩
  rcases hc : c (.inr x) with _ | y
  · rfl
  · have hf := h.2 x y hc
    unfold firstFwdB at hf
    obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.mp hf
    have hp := List.find?_some he
    simp only [decide_eq_true_eq] at hp
    obtain ⟨q, y'⟩ := e
    simp only at hp
    subst hp
    exact absurd (List.mem_of_find?_eq_some he) (hlog y')

/-- Appending a query keeps the invariant when the edges grow and the cache's `F` part stays. -/
theorem FInv.append_keep {σ σ' : KSim} {log : RLog} {c c' : HFS.QueryCache} (h : FInv σ log c)
    (q : Common.PermutationQuery Common.KState) (y : Common.KState)
    (hE : ∀ x, (Common.forwardLookup σ.edges x).isSome → (Common.forwardLookup σ'.edges x).isSome)
    (hq : ∀ x, q = .forward x → (Common.forwardLookup σ'.edges x).isSome)
    (hc : ∀ x, c' (.inr x) = c (.inr x)) :
    FInv σ' (log ++ [(q, y)]) c' := by
  refine ⟨fun x y' hm ↦ ?_, fun x y' hy' ↦ ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact hE x (h.1 x y' hm)
    · rw [List.mem_singleton, Prod.mk.injEq] at hm
      exact hq x hm.1.symm
  · rw [hc] at hy'
    exact firstFwdB_append_of_some (h.2 x y' hy') _

/-- **One step of the simulator keeps the invariant.** -/
theorem fInv_step (q : Common.PermutationQuery Common.KState) (σ : KSim) (log : RLog)
    (c : HFS.QueryCache) (h : FInv σ log c) {v : (Common.KState × KSim) × HFS.QueryCache}
    (hv : v ∈ support ((simulateQ HFS.romImpl
      ((Common.simulator2 (Msg := Bytes) Common.keccakPadding q).run σ)).run c)) :
    FInv v.1.2 (log ++ [(q, v.1.1)]) v.2 := by
  cases q with
  | inverse y =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv
      subst hv
      exact h.append_keep _ _ (fun _ hx ↦ hx) (fun _ hq ↦ by cases hq) (fun _ ↦ rfl)
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, simulateQ_pure,
        StateT.run_pure, bind_map_left, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hv
      obtain ⟨x, -, rfl⟩ := hv
      exact h.append_keep _ _ (fun x' hx ↦ isSome_forwardLookup_cons hx _ _)
        (fun _ hq ↦ by cases hq) (fun _ ↦ rfl)
  | forward x =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · rename_i y hy
      simp at hv
      subst hv
      exact h.append_keep _ _ (fun _ hx ↦ hx) (fun x' hq ↦ by
        cases hq
        rw [hy]
        rfl) (fun _ ↦ rfl)
    · rename_i hx
      obtain ⟨hlog, hcx⟩ := h.fresh hx
      have hnew : ∀ y (σ' : KSim), σ'.edges = (x, y) :: σ.edges →
          ∀ c' : HFS.QueryCache, (∀ x', x' ≠ x → c' (.inr x') = c (.inr x')) →
          (c' (.inr x) = none ∨ c' (.inr x) = some y) →
          FInv σ' (log ++ [(.forward x, y)]) c' := by
        intro y σ' hσ' c' hc' hcx'
        refine ⟨fun x' y' hm ↦ ?_, fun x' y' hy' ↦ ?_⟩
        · rw [hσ']
          rcases List.mem_append.mp hm with hm | hm
          · exact isSome_forwardLookup_cons (h.1 x' y' hm) _ _
          · rw [List.mem_singleton, Prod.mk.injEq, Common.PermutationQuery.forward.injEq] at hm
            rw [hm.1, Common.forwardLookup_cons_self]
            rfl
        · by_cases hxx : x' = x
          · subst hxx
            rcases hcx' with hcx' | hcx'
            · rw [hcx'] at hy'
              cases hy'
            · rw [hcx', Option.some.injEq] at hy'
              subst hy'
              exact firstFwdB_append_self hlog
          · rw [hc' x' hxx] at hy'
            exact firstFwdB_append_of_some (h.2 x' y' hy') _
      split at hv
      · rename_i s β hch
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rcases hm : Common.keccakPadding.unpad (β ++ [Common.blockTo s x]) with _ | m
        · rw [Common.rootedAnswer2_run_none _ hm] at hw
          obtain ⟨-, hself, hc⟩ := Common.roStep_support _ c hw
          exact hnew w.1 _ rfl w.2 (fun x' hx' ↦ hc _ (by simpa using hx')) (Or.inr hself)
        · rw [Common.rootedAnswer2_run_some _ hm] at hw
          simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨w', hw', ec, rfl⟩ := hw
          obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw'
          exact hnew _ _ rfl w'.2 (fun x' _ ↦ hc _ (by simp))
            (Or.inl (by rw [hc _ (by simp)]; exact hcx))
      · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          Common.fQuery_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        obtain ⟨-, hself, hc⟩ := Common.roStep_support _ c hw
        exact hnew w.1 _ rfl w.2 (fun x' hx' ↦ hc _ (by simpa using hx')) (Or.inr hself)

/-- **The invariant along the adversary's run.** -/
theorem fInv_run {α : Type} (A : OracleComp (Common.permutationOracleSpec KeccakState) α)
    (s : (KSim × RLog) × HFS.QueryCache) (hs : FInv s.1.1 s.1.2 s.2) :
    ∀ w ∈ support ((simulateQ (Common.foldRO
        (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)) (simulateQ relP A)).run s),
      FInv w.2.1.1 w.2.1.2 w.2.2 := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure a =>
    intro w hw
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact hs
  | query_bind q k ih =>
    intro w hw
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
      id_map, relP, bind_map_left, StateT.run_bind, mem_support_bind_iff] at hw
    obtain ⟨v, hv, hw⟩ := hw
    refine ih _ v.2 ?_ w hw
    rw [Common.foldRO_run] at hv
    simp only [support_map, Set.mem_image] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    have e : (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding
        (.inr (.inr (permQueryToRpm q)))).run s.1 =
        (fun z ↦ (z.1, (z.2, s.1.2 ++ [(permQueryToRpm q, z.1)]))) <$>
          (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run
            s.1.1 := rfl
    rw [e, simulateQ_map, StateT.run_map, support_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    exact fInv_step _ _ _ _ hs hu

theorem permQueryOfRpm_eq_forward {q : Common.PermutationQuery Common.KState} {s : KeccakState} :
    permQueryOfRpm q = .forward s ↔ q = .forward (KState.toRpm s) := by
  cases q with
  | forward x =>
    simp only [permQueryOfRpm, Common.PermutationQuery.forward.injEq]
    constructor
    · rintro rfl; rw [toRpm_ofRpm]
    · rintro rfl; rw [ofRpm_toRpm]
  | inverse y => simp [permQueryOfRpm]

/-- **Every `F` answer the adversary's simulator cached is the transcript's first forward answer
at its input**, on every reachable state of the transfer's random-oracle adversary. -/
theorem cacheF_firstForward (A : DetAdversary)
    {z : ((ProgramAndInput × Proof) × PermutationTranscript) ×
      (Common.hfSpec Bytes Common.DigestBytes Common.KState).QueryCache}
    (hz : z ∈ support ((simulateQ (Common.hfSpec Bytes Common.DigestBytes Common.KState).romImpl
      (Common.advS2 Common.keccakPadding Common.KState.zero (advR A))).run ∅))
    (s y : KeccakState) (h : cmap z.2 (.inr s) = some y) : firstForward z.1.2 s = some y := by
  rw [advS2_advR, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hinv := fInv_run A _ ⟨fun x y hm ↦ by simp at hm, fun x y hc ↦ by simp at hc⟩ w hw
  simp only [cmap, QueryCache.ofFn_apply, Option.map_eq_some_iff] at h
  obtain ⟨y0, hy0, rfl⟩ := h
  have hf := hinv.2 _ _ hy0
  unfold firstFwdB at hf
  unfold firstForward
  rw [List.find?_map]
  have hp : ((fun e ↦ decide (e.1 = Common.PermutationQuery.forward s)) ∘ entryOfRpm) =
      fun e ↦ decide (e.1 = Common.PermutationQuery.forward (KState.toRpm s)) := by
    funext e
    simp only [Function.comp, entryOfRpm, permQueryOfRpm_eq_forward]
  rw [hp, Option.map_map]
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hf
  rw [he]
  rfl

end LeanVM.Rpm

end
