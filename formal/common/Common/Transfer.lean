module

public import Common.Indiff.Main
public import Common.Defs

@[expose] public section

/-!
# Transfer: from the random-oracle model to the random-permutation model

Security games of the other projects are stated in the random oracle model (ROM): every party
hashes through a random oracle `H : Msg → Dg`. In the random-permutation model (RPM) `H` is the
sponge over a random permutation `π` that every party may also query directly, forward and
inverse. Indifferentiability (`indifferentiability`) moves any such game across:

* `transfer`: for a game made of an honest part using `H` only (`pre`, `post`) and an adversary `A`
  using `H`, `π` and `π⁻¹`, the RPM game and the ROM game against the ROM adversary `advS A`
  (`A` with its permutation queries answered by the simulator, which queries `H`) give every event
  probabilities within `indiffBound`; so every ROM bound for ROM adversaries transfers to the RPM
  with the additive cost `indiffBound`;
* `pathsOf`: from a transcript of permutation queries and answers, the hash queries `(m, H m)`
  whose whole sponge paths the transcript contains, replaying the simulator's bookkeeping.
  In the RPM the pairs are correct hashes for the permutation (`pathsOf_sound`); in the ROM the
  simulator's state is the replay of the adversary's transcript (`simulator_state_eq_replay`), and
  the pairs are exactly the simulator's random-oracle queries on the adversary's behalf, with the
  oracle's answers (`pathsOf_ideal`). So an extractor reading the ROM adversary's hash queries runs
  in the RPM on the adversary's own hash queries together with `pathsOf` of its permutation
  transcript.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## Games with an honest part and an adversary -/

/-- Embed a ROM computation (coins and `H`) into the distinguisher's oracles. -/
def hEmbed : QueryImpl (unifSpec + roSpec Msg Dg)
    (OracleComp (dSpec Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr m => liftM ((dSpec Msg Dg (SpState Dg E C)).query (.inr (.inl m)))

/-- A ROM computation as a distinguisher computation that never queries `π`. -/
def liftH {α : Type} (X : OracleComp (unifSpec + roSpec Msg Dg) α) :
    OracleComp (dSpec Msg Dg (SpState Dg E C)) α :=
  simulateQ (hEmbed (E := E) (C := C)) X

/-- Running a lifted ROM computation in the ideal world runs it and keeps the simulator. -/
theorem run_idealImpl_liftH {α : Type} (X : OracleComp (unifSpec + roSpec Msg Dg) α)
    (σ : SimState Dg E C) :
    (simulateQ (idealImpl P) (liftH (E := E) (C := C) X)).run σ = (·, σ) <$> X := by
  unfold liftH
  induction X using OracleComp.inductionOn generalizing σ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind]
    rcases t with n | m
    · simp only [hEmbed, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, idealImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, ih]
      simp [map_eq_bind_pure_comp]
      rfl
    · simp only [hEmbed, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, idealImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, ih]
      simp [map_eq_bind_pure_comp]
      rfl

/-- **The ROM adversary of an RPM adversary**: `A` with its permutation queries answered by the
simulator, from its initial state, which queries the random oracle. -/
noncomputable def advS {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) :
    OracleComp (unifSpec + roSpec Msg Dg) α :=
  (simulateQ (idealImpl P) A).run' (SimState.init iv)

/-- The random-oracle-model run of a ROM computation. -/
noncomputable def romRun {α : Type} (X : OracleComp (unifSpec + roSpec Msg Dg) α) : ProbComp α :=
  (simulateQ (roSpec Msg Dg).romImpl X).run' ∅

/-- The RPM game: an honest part using `H`, the adversary using `H`, `π`, `π⁻¹`, an honest part
using `H`. -/
def rpmGame {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + roSpec Msg Dg) δ) :
    OracleComp (dSpec Msg Dg (SpState Dg E C)) δ :=
  liftH (E := E) (C := C) pre >>= fun x ↦ A x >>= fun a ↦ liftH (E := E) (C := C) (post x a)

/-- The ideal world of an RPM game is the ROM game against the simulated adversary. -/
theorem idealGame_rpmGame {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + roSpec Msg Dg) δ) :
    idealGame P iv (rpmGame pre A post) =
      romRun (pre >>= fun x ↦ advS P iv (A x) >>= fun a ↦ post x a) := by
  simp only [idealGame, romRun, rpmGame, advS]
  congr 2
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, run_idealImpl_liftH,
    bind_map_left, map_bind, Functor.map_map]
  refine bind_congr fun x ↦ ?_
  simp

/-- **Transfer.** For an RPM game made of honest parts using `H` only and an adversary `A` with
`H`, `π` and `π⁻¹`, whose hash and permutation calls cost at most `q` in all (`queryCost`: a hash
call costs its padded length in blocks), every event has probabilities in the RPM and in the ROM
against the ROM adversary `advS P iv A` within `indiffBound |S| |C| q`. -/
theorem transfer {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + roSpec Msg Dg) δ) (q : ℕ)
    (hq : QueryCostAtMost (rpmGame pre A post) (queryCost (Dg := Dg) P) q) (p : δ → Prop) :
    Pr{let a ← realGame P iv (rpmGame pre A post)}[p a] ≤
        Pr{let a ← romRun (pre >>= fun x ↦ advS P iv (A x) >>= fun a ↦ post x a)}[p a] +
          indiffBound (Fintype.card (SpState Dg E C)) (Fintype.card C) q ∧
      Pr{let a ← romRun (pre >>= fun x ↦ advS P iv (A x) >>= fun a ↦ post x a)}[p a] ≤
        Pr{let a ← realGame P iv (rpmGame pre A post)}[p a] +
          indiffBound (Fintype.card (SpState Dg E C)) (Fintype.card C) q := by
  rw [← idealGame_rpmGame]
  exact indifferentiability P iv _ q hq p

/-! ## Hash queries from permutation transcripts -/

/-- A transcript consistent with a function `π`: forward answers are `π`'s values, inverse answers
are `π`'s preimages. -/
def Consistent (π : SpState Dg E C → SpState Dg E C)
    (log : List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) : Prop :=
  ∀ e ∈ log, match e with
    | (.forward x, y) => π x = y
    | (.inverse y, x) => π x = y

/-- The replayed bookkeeping of a consistent transcript: its edges are `π`'s, and its rooted
states are the sponge's states along their paths. -/
theorem replay_sound (π : SpState Dg E C → SpState Dg E C)
    (log : List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) (h : Consistent π log) :
    (∀ e ∈ (replay iv log).edges, π e.1 = e.2) ∧
      ∀ p ∈ (replay iv log).chains, absorbAll (m := Id) (fun x ↦ pure (π x)) iv p.2 = p.1 := by
  unfold replay
  induction log using List.reverseRecOn with
  | nil => simp [SimState.init, absorbAll]; rfl
  | append_singleton log e ih =>
    have hlog : Consistent π log := fun e he ↦ h e (List.mem_append_left _ he)
    have he : Consistent π [e] := fun e' he' ↦ h e' (List.mem_append_right _ he')
    obtain ⟨hE, hC⟩ := ih hlog
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set σ := log.foldl replayStep (SimState.init iv)
    obtain ⟨q, a⟩ := e
    have he' := he (q, a) (List.mem_singleton_self _)
    cases q with
    | forward x =>
      simp only at he'
      simp only [replayStep]
      split
      · exact ⟨hE, hC⟩
      · split
        · next s β hch =>
          obtain ⟨hsβ, hsx⟩ := chainOf_some hch
          refine ⟨fun e he ↦ ?_, fun p hp ↦ ?_⟩
          · rcases List.mem_cons.mp he with rfl | he
            · exact he'
            · exact hE e he
          · rcases List.mem_cons.mp hp with rfl | hp
            · simp only
              rw [absorbAll_append, hC _ hsβ]
              simp only [absorbAll]
              change π (absorb s (blockTo s x)) = a
              rw [absorb_blockTo hsx, he']
            · exact hC p hp
        · refine ⟨fun e he ↦ ?_, hC⟩
          rcases List.mem_cons.mp he with rfl | he
          · exact he'
          · exact hE e he
    | inverse y =>
      simp only at he'
      simp only [replayStep]
      split
      · exact ⟨hE, hC⟩
      · refine ⟨fun e he ↦ ?_, hC⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact he'
        · exact hE e he

/-- **The hash queries of a transcript are correct hashes**: for a transcript consistent with a
function `π`, every pair `(m, d)` of `pathsOf` has `d = H^π m`, the sponge over `π`. -/
theorem pathsOf_sound (π : SpState Dg E C → SpState Dg E C)
    (log : List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) (h : Consistent π log)
    {m : Msg} {d : Dg} (hmd : (m, d) ∈ pathsOf P iv log) :
    spongeWith (m := Id) P iv (fun x ↦ pure (π x)) m = d := by
  simp only [pathsOf, simPaths, List.mem_filterMap, Option.map_eq_some_iff,
    Prod.mk.injEq] at hmd
  obtain ⟨p, hp, m', hm, rfl, rfl⟩ := hmd
  have := (replay_sound iv π log h).2 p hp
  have hpad := (P.unpad_eq_some_iff _ _).mp hm
  simp only [spongeWith, hpad, this]
  rfl

/-! ## The simulator's bookkeeping is the replay of the adversary's transcript -/

/-- A simulator step moves its state by the replayed bookkeeping of the query and answer. -/
theorem simulator_step_replay (q : PermutationQuery (SpState Dg E C)) (σ : SimState Dg E C) {z}
    (hz : z ∈ support ((simulator P q).run σ)) : z.2 = replayStep σ (q, z.1) := by
  cases q with
  | forward x =>
    simp only [simulator, StateT.run_mk] at hz
    simp only [replayStep]
    split at hz
    · next y hy =>
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [hy]
    · next hy =>
      split at hz
      · next s β hch =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨y, -, rfl⟩ := hz
        simp [hy, hch]
      · next hch =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
        obtain ⟨y, -, rfl⟩ := hz
        simp [hy, hch]
  | inverse y =>
    simp only [simulator, StateT.run_mk] at hz
    simp only [replayStep]
    split at hz
    · next x hx =>
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [hx]
    · next hx =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨x, -, rfl⟩ := hz
      simp [hx]

/-- The ideal world with the adversary's permutation transcript logged, oldest first. -/
noncomputable def idealImplLog : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C))
      (OracleComp (unifSpec + roSpec Msg Dg)))
  | .inr (.inr q) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2 ++ [(q, z.1)]))) <$> (simulator P q).run s.1
  | t => StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2))) <$> (idealImpl P t).run s.1

/-- Forgetting the transcript gives the ideal world. -/
theorem idealImplLog_proj {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (s : SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) :
    Prod.map id Prod.fst <$> (simulateQ (idealImplLog P) D).run s =
      (simulateQ (idealImpl P) D).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t s ↦ by
    rcases t with n | m | q <;> simp [idealImplLog, idealImpl, Functor.map_map]) D s

/-- **The simulator's state is the replay of the transcript**, on every reachable state of the
logged ideal world. -/
theorem simulator_state_eq_replay {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    {z} (hz : z ∈ support ((simulateQ (idealImplLog P) D).run (SimState.init iv, []))) :
    z.2.1 = replay iv z.2.2 := by
  refine inv_of_mem_support_run (spec' := unifSpec + roSpec Msg Dg) (idealImplLog P)
    (fun s ↦ s.1 = replay iv s.2) (fun t s hs w hw ↦ ?_) D rfl z hz
  rcases t with n | m | q
  · simp only [idealImplLog, idealImpl, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hw
    obtain ⟨_, ⟨u, -, rfl⟩, rfl⟩ := hw
    exact hs
  · simp only [idealImplLog, idealImpl, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hw
    obtain ⟨_, ⟨u, -, rfl⟩, rfl⟩ := hw
    exact hs
  · simp only [idealImplLog, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [simulator_step_replay P q s.1 hw', hs]
    rfl

/-- An output reachable in the random oracle model is reachable with arbitrary answers. -/
theorem fst_mem_support_of_mem_support_ro {β : Type}
    {X : OracleComp (unifSpec + roSpec Msg Dg) β} {c : (roSpec Msg Dg).QueryCache}
    {z : β × (roSpec Msg Dg).QueryCache}
    (hz : z ∈ support ((simulateQ (roSpec Msg Dg).romImpl X).run c)) : z.1 ∈ support X :=
  support_simulateQ_run'_subset (roSpec Msg Dg).romImpl X c (by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)

/-- The digests of the simulator's rooted paths are cached random-oracle answers, and stay. -/
theorem roOK_step (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : (SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) ×
      (roSpec Msg Dg).QueryCache)
    (hs : ∀ md ∈ simPaths P s.1.1, s.2 md.1 = some md.2) {z}
    (hz : z ∈ support (((foldRO (idealImplLog P)) t).run s)) :
    ∀ md ∈ simPaths P z.2.1.1, z.2.2 md.1 = some md.2 := by
  rw [foldRO_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hle := le_of_mem_support_run _ s.2 hw
  have hold : ∀ md ∈ simPaths P s.1.1, w.2 md.1 = some md.2 := fun md hmd ↦ hle (hs md hmd)
  rcases t with n | m | q
  · have := fst_mem_support_of_mem_support_ro hw
    simp only [idealImplLog, idealImpl, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at this
    obtain ⟨_, ⟨u, -, rfl⟩, h⟩ := this
    rw [← h]; exact hold
  · have := fst_mem_support_of_mem_support_ro hw
    simp only [idealImplLog, idealImpl, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at this
    obtain ⟨_, ⟨u, -, rfl⟩, h⟩ := this
    rw [← h]; exact hold
  · simp only [idealImplLog, StateT.run_mk, simulateQ_map, StateT.run_map, support_map,
      Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simp only at hold ⊢
    cases q with
    | inverse y =>
      have := simulator_step_replay P _ _ (fst_mem_support_of_mem_support_ro hw')
      rw [this]
      simp only [replayStep]
      split
      · exact hold
      · exact hold
    | forward x =>
      simp only [simulator, StateT.run_mk] at hw'
      split at hw'
      · simp only [simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hw'
        subst hw'; exact hold
      · split at hw'
        · next s β hch =>
          simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw'
          obtain ⟨⟨y, c₁⟩, hy, rfl⟩ := hw'
          intro md hmd
          simp only [simPaths, List.mem_filterMap, List.mem_cons] at hmd
          obtain ⟨p, hp | hp, hpm⟩ := hmd
          · subst hp
            obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.mp hpm
            rw [rootedAnswer_run_some P hm'] at hy
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
              support_uniformSample, Set.mem_univ, true_and] at hy
            obtain ⟨⟨d, c₂⟩, hd, ec, hec⟩ := hy
            simp only [Prod.mk.injEq] at hec
            obtain ⟨rfl, rfl⟩ := hec
            exact (roStep_support _ _ hd).2.1
          · exact hold md (List.mem_filterMap.mpr ⟨p, hp, hpm⟩)
        · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
            simulateQ_romImpl_liftM_run, mem_support_bind_iff, support_map, Set.mem_image,
            support_pure, Set.mem_singleton_iff] at hw'
          obtain ⟨_, ⟨y, -, rfl⟩, rfl⟩ := hw'
          exact hold

/-- **The hash queries of the adversary's transcript, in the ideal world**: on every reachable
state of the logged ideal world, every pair `(m, d)` of `pathsOf` of the adversary's
permutation transcript is the random oracle's cached answer `H m = d`. These are exactly the
random-oracle queries the simulator made for the adversary (`rootedAnswer`): an extractor that
reads the ROM adversary's hash queries reads, in the RPM, the adversary's own hash queries and
`pathsOf` of its permutation transcript. -/
theorem pathsOf_ideal {α : Type} (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) {z}
    (hz : z ∈ support ((simulateQ (foldRO (idealImplLog P)) D).run
      (((SimState.init iv : SimState Dg E C), []), ∅))) :
    ∀ md ∈ pathsOf P iv z.2.1.2, z.2.2 md.1 = some md.2 := by
  have hRO := inv_of_mem_support_run (spec' := unifSpec) (foldRO (idealImplLog P))
    (fun s ↦ ∀ md ∈ simPaths P s.1.1, s.2 md.1 = some md.2)
    (fun t s hs w hw ↦ roOK_step P t s hs hw) D
    (s := (((SimState.init iv : SimState Dg E C), []), ∅)) (by
      simp only [simPaths, SimState.init, List.filterMap_cons, List.filterMap_nil]
      rcases h : P.unpad [] with _ | a
      · simp
      · exact absurd ((P.unpad_eq_some_iff _ _).mp h) (P.pad_ne_nil a))
    z hz
  have h1 := run_simulateQ_foldRO (idealImplLog P) D ((SimState.init iv : SimState Dg E C), [])
    (∅ : (roSpec Msg Dg).QueryCache)
  have hz' : ((z.1, z.2.1), z.2.2) ∈ support ((simulateQ (roSpec Msg Dg).romImpl
      ((simulateQ (idealImplLog P) D).run (SimState.init iv, []))).run ∅) := by
    rw [h1, support_map]; exact ⟨z, hz, rfl⟩
  have hrep := simulator_state_eq_replay P iv D (fst_mem_support_of_mem_support_ro hz')
  intro md hmd
  rw [pathsOf, ← hrep] at hmd
  exact hRO md hmd

end Setting

end Common
