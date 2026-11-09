/-
  LeanVM.Protocol.Rpm.Extract

  The Keccak-256 evaluations of the adversary's transcript are, in the transfer's random-oracle
  world, exactly the random oracle's answers to the simulator's hash queries.
-/

import LeanVM.Protocol.Rpm.Game
import Common.Keccak
import LeanVM.Protocol.WithHash

/-!
# The transcript's hashes are the adversary's cache

In the transfer's random-oracle world the adversary of `Statement/LeanVm.lean` runs with the
two-oracle simulator of `common` (`Common.advS2`). It makes no hash query itself: the
simulator queries `H m` only when a fresh forward query completes a rooted sponge path that pads
`m`, and books the path. So the hash answers in the cache when the adversary returns are exactly
the Keccak-256 evaluations of its transcript (`lookupEvaluation (keccakEvaluationsOfTranscript T)`, which are those of
`Common.pathsOf` on the transcript's bytes, `hashesOf_transcriptPaths`):

* `advS2_advR`: the transcript the adversary records on lanes is the byte transcript `common`
  logs in the simulator's state (`Common.advImplLog2`), read on lanes;
* `Common.pathsOf_ideal2`: every evaluation of the transcript is cached;
* `cacheInv_run`: every cached hash answer is an evaluation of the simulator's rooted paths;
* `transcriptHashes_eq_of_mem_support`: hence the two agree.
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

/-- The simulator's bookkeeping on Keccak states. -/
abbrev KSim := Common.SimState Common.DigestBytes Common.KRest Common.KCap

/-- A byte transcript. -/
abbrev RLog := List (Common.PermutationQuery Common.KState × Common.KState)

/-- A transcript entry, on bytes. -/
def entryToRpm (e : Common.PermutationQuery KeccakState × KeccakState) :
    Common.PermutationQuery Common.KState × Common.KState :=
  (permQueryToRpm e.1, KState.toRpm e.2)

/-- A byte transcript entry, on lanes. -/
def entryOfRpm (e : Common.PermutationQuery Common.KState × Common.KState) :
    Common.PermutationQuery KeccakState × KeccakState :=
  (permQueryOfRpm e.1, KState.ofRpm e.2)

theorem permQueryToRpm_ofRpm (q : Common.PermutationQuery Common.KState) :
    permQueryToRpm (permQueryOfRpm q) = q := by
  cases q <;> simp [permQueryToRpm, permQueryOfRpm, toRpm_ofRpm]

theorem permQueryOfRpm_toRpm (q : Common.PermutationQuery KeccakState) :
    permQueryOfRpm (permQueryToRpm q) = q := by
  cases q <;> simp [permQueryToRpm, permQueryOfRpm, ofRpm_toRpm]

theorem entryToRpm_ofRpm (e : Common.PermutationQuery Common.KState × Common.KState) :
    entryToRpm (entryOfRpm e) = e := by
  simp [entryToRpm, entryOfRpm, permQueryToRpm_ofRpm, toRpm_ofRpm]

theorem entryOfRpm_toRpm (e : Common.PermutationQuery KeccakState × KeccakState) :
    entryOfRpm (entryToRpm e) = e := by
  simp [entryToRpm, entryOfRpm, permQueryOfRpm_toRpm, ofRpm_toRpm]

/-! ## The two logs -/

/-- **The lane transcript is the byte log**: the adversary recording its transcript on lanes,
with the simulator, is the adversary with the simulator logging the byte queries in its state. -/
theorem advImpl2_logRel {α : Type} (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (T : PermutationTranscript) (σ : KSim) :
    (fun x ↦ (x.1.1, (x.2, x.1.2.map entryToRpm))) <$>
        (simulateQ (Common.advImpl2 Common.keccakPadding) ((simulateQ logRel A).run T)).run σ =
      (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relP A)).run
        (σ, T.map entryToRpm) := by
  induction A using OracleComp.inductionOn generalizing T σ with
  | pure a => simp
  | query_bind q k ih =>
    simp only [StateT.run_bind, OracleQuery.input_query, relP, logRel,
      StateT.run_mk, bind_map_left, simulateQ_bind, simulateQ_query,
      OracleQuery.cont_query, id_map, map_bind]
    have h1 : (Common.advImpl2 Common.keccakPadding (.inr (.inr (permQueryToRpm q)))).run σ =
        (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run σ := rfl
    have h2 : (Common.advImplLog2 Common.keccakPadding (.inr (.inr (permQueryToRpm q)))).run
        (σ, T.map entryToRpm) = (fun z ↦ (z.1, (z.2, T.map entryToRpm ++ [(permQueryToRpm q, z.1)])))
          <$> (Common.simulator2 (Msg := Bytes) Common.keccakPadding (permQueryToRpm q)).run σ :=
      rfl
    rw [h1, h2, bind_map_left]
    refine bind_congr fun z ↦ ?_
    have e : T.map entryToRpm ++ [(permQueryToRpm q, z.1)] =
        (T ++ [(q, KState.ofRpm z.1)]).map entryToRpm := by
      simp [entryToRpm, toRpm_ofRpm]
    rw [e, ← ih]

/-- The transfer's adversary is the adversary with the simulator logging the byte queries, its
log read on lanes. -/
theorem advS2_advR (A : DetAdversary) :
    Common.advS2 Common.keccakPadding Common.KState.zero (advR A) =
      (fun y ↦ (y.1, y.2.2.map entryOfRpm)) <$>
        (simulateQ (Common.advImplLog2 Common.keccakPadding) (simulateQ relP A)).run
          (Common.SimState.init Common.KState.zero, []) := by
  have h := advImpl2_logRel A [] (Common.SimState.init Common.KState.zero)
  rw [List.map_nil] at h
  rw [← h, Functor.map_map, Common.advS2, advR, StateT.run'_eq]
  congr 1
  funext x
  simp only [List.map_map]
  have e : entryOfRpm ∘ entryToRpm = id := funext entryOfRpm_toRpm
  rw [e, List.map_id]

/-! ## The cache holds only the transcript's hashes -/

/-- Every cached hash answer is an evaluation of the simulator's rooted paths. -/
def CacheInv (σ : KSim) (c : HFS.QueryCache) : Prop :=
  ∀ m d, c (.inl m) = some d → (m, d) ∈ Common.simPaths Common.keccakPadding σ

/-- A new chain keeps the old rooted paths' evaluations. -/
theorem mem_simPaths_cons {σ : KSim} {e : Common.PermutationEdges Common.KState}
    {p : Common.KState × List Common.KBlock} {md : Bytes × Common.DigestBytes}
    (h : md ∈ Common.simPaths Common.keccakPadding σ) :
    md ∈ Common.simPaths Common.keccakPadding (⟨e, p :: σ.chains⟩ : KSim) := by
  simp only [Common.simPaths, List.filterMap_cons] at h ⊢
  split <;> simp_all

/-- **One step of the simulator keeps the invariant**: it queries `H m` only to answer a fresh
forward query completing a rooted path that pads `m`, which it books. -/
theorem cacheInv_step (q : Common.PermutationQuery Common.KState) (σ : KSim) (c : HFS.QueryCache)
    (h : CacheInv σ c) {v : (Common.KState × KSim) × HFS.QueryCache}
    (hv : v ∈ support ((simulateQ HFS.romImpl
      ((Common.simulator2 (Msg := Bytes) Common.keccakPadding q).run σ)).run c)) :
    CacheInv v.1.2 v.2 := by
  cases q with
  | inverse y =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_romImpl_liftM_run, simulateQ_pure,
        StateT.run_pure, bind_map_left, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hv
      obtain ⟨_, -, rfl⟩ := hv
      exact h
  | forward x =>
    simp only [Common.simulator2, StateT.run_mk] at hv
    split at hv
    · simp at hv; subst hv; exact h
    · split at hv
      · next s β hch =>
        simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        rcases hm : Common.keccakPadding.unpad (β ++ [Common.blockTo s x]) with _ | m
        · rw [Common.rootedAnswer2_run_none _ hm] at hw
          obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
          intro m' d hd
          rw [hc _ (by simp)] at hd
          exact mem_simPaths_cons (h m' d hd)
        · rw [Common.rootedAnswer2_run_some _ hm] at hw
          simp only [mem_support_bind_iff, support_uniformSample, Set.mem_univ, true_and,
            support_pure, Set.mem_singleton_iff] at hw
          obtain ⟨w', hw', ec, rfl⟩ := hw
          obtain ⟨-, hself, hc⟩ := Common.roStep_support _ c hw'
          intro m' d hd
          by_cases hmm : m' = m
          · subst hmm
            rw [hself, Option.some_inj] at hd
            subst hd
            simp [Common.simPaths, hm]
          · rw [hc _ (by simpa using hmm)] at hd
            exact mem_simPaths_cons (h m' d hd)
      · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
          Common.fQuery_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hv
        obtain ⟨w, hw, rfl⟩ := hv
        obtain ⟨-, -, hc⟩ := Common.roStep_support _ c hw
        intro m' d hd
        rw [hc _ (by simp)] at hd
        exact h m' d hd

/-- **The invariant along the adversary's run**: the adversary makes permutation queries only, so
every cached hash answer is an evaluation of the simulator's rooted paths. -/
theorem cacheInv_run {α : Type} (A : OracleComp (Common.permutationOracleSpec KeccakState) α)
    (s : (KSim × RLog) × HFS.QueryCache) (hs : CacheInv s.1.1 s.2) :
    ∀ w ∈ support ((simulateQ (Common.foldRO
        (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)) (simulateQ relP A)).run s),
      CacheInv w.2.1.1 w.2.2 := by
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
    exact cacheInv_step _ _ _ hs hu

/-! ## The transcript's hashes -/

/-- On every reachable state of the transfer's ROM adversary (from the empty cache), the
Keccak-256 evaluations of the adversary's transcript are the random oracle's cached hash answers. -/
theorem transcriptHashes_eq_of_mem_support (A : DetAdversary)
    {z : ((ProgramAndInput × Proof) × PermutationTranscript) ×
      (Common.hfSpec Bytes Common.DigestBytes Common.KState).QueryCache}
    (hz : z ∈ support ((simulateQ (Common.hfSpec Bytes Common.DigestBytes Common.KState).romImpl
      (Common.advS2 Common.keccakPadding Common.KState.zero (advR A))).run ∅)) :
    lookupEvaluation (keccakEvaluationsOfTranscript z.1.2) = fun m ↦ (z.2 (.inl m)).map Digest.ofRpm := by
  rw [advS2_advR, simulateQ_map, StateT.run_map, Common.run_simulateQ_foldRO, Functor.map_map,
    support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hfwd := Common.pathsOf_ideal2 Common.keccakPadding Common.KState.zero
    (simulateQ relP A) hw
  have hinv := cacheInv_run A _ (fun m d hd ↦ by simp at hd) w hw
  have hrep : w.2.1.1 = Common.replay Common.KState.zero w.2.1.2 := by
    have h1 := Common.run_simulateQ_foldRO
      (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding) (simulateQ relP A)
      (Common.SimState.init Common.KState.zero, []) (∅ : HFS.QueryCache)
    have hz' : ((w.1, w.2.1), w.2.2) ∈ support ((simulateQ HFS.romImpl
        ((simulateQ (Common.advImplLog2 (Msg := Bytes) Common.keccakPadding)
          (simulateQ relP A)).run (Common.SimState.init Common.KState.zero, []))).run ∅) := by
      rw [h1, support_map]
      exact ⟨w, hw, rfl⟩
    exact Common.simulator2_state_eq_replay _ _ _
      (Common.fst_mem_support_of_mem_support_ro2 hz')
  have hrev : ∀ m d, w.2.2 (.inl m) = some d →
      (m, d) ∈ Common.pathsOf Common.keccakPadding Common.KState.zero w.2.1.2 := by
    intro m d hd
    rw [Common.pathsOf, ← hrep]
    exact hinv m d hd
  have eT : (w.2.1.2.map entryOfRpm).map (fun e ↦ (permQueryToRpm e.1, KState.toRpm e.2)) =
      w.2.1.2 := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id w.2.1.2]
    exact List.map_congr_left fun e _ ↦ entryToRpm_ofRpm e
  rw [hashesOf_transcriptPaths]
  funext m
  simp only [hashesOfB, transcriptPathsB, eT]
  rcases hc : w.2.2 (.inl m) with _ | d
  · have hn : (Common.pathsOf Common.keccakPadding Common.KState.zero w.2.1.2).find?
        (·.1 = m) = none := by
      refine List.find?_eq_none.mpr fun p hp hpm ↦ ?_
      have h' := hfwd p hp
      simp only [decide_eq_true_eq] at hpm
      rw [hpm, hc] at h'
      cases h'
    rw [hn]
    rfl
  · obtain ⟨p, hp⟩ : ∃ p, (Common.pathsOf Common.keccakPadding Common.KState.zero
        w.2.1.2).find? (·.1 = m) = some p :=
      Option.isSome_iff_exists.mp (List.find?_isSome.mpr ⟨(m, d), hrev m d hc, by simp⟩)
    have hp1 := List.find?_some hp
    have h' := hfwd p (List.mem_of_find?_eq_some hp)
    simp only [decide_eq_true_eq] at hp1
    rw [hp1, hc, Option.some_inj] at h'
    rw [hp, h']
    rfl

end LeanVM.Rpm
