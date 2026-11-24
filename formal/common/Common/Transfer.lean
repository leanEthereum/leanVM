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
* `logImpl_reachable`: for a simulator that moves its state by the bookkeeping replayed from the
  adversary's transcript of permutation queries and answers (`replay`), run in the ROM, the
  simulator's state is that replay, and any invariant of its state and the random oracle's cache
  that it keeps holds; the two-oracle model's `pathsOf_ideal2` reads the simulator's hash queries
  off the transcript so.
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

/-! ## A logged simulator -/

section Logged

variable {ι' : Type} [DecidableEq ι'] {hs : OracleSpec.{0, 0} ι'}
  [∀ t : hs.Domain, SampleableType (hs.Range t)]
  (sim : QueryImpl (permutationOracleSpec (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hs))))
  (base : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C) (OracleComp (unifSpec + hs))))

/-- `base` with its permutation queries answered by the simulator `sim` and logged with their
answers, oldest first. -/
noncomputable def logImpl : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C))
      (OracleComp (unifSpec + hs)))
  | .inr (.inr q) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2 ++ [(q, z.1)]))) <$> (sim q).run s.1
  | t => StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2))) <$> (base t).run s.1

/-- An output reachable in the random oracle model is reachable with arbitrary answers. -/
theorem fst_mem_support_of_mem_support_rom {β : Type} {X : OracleComp (unifSpec + hs) β}
    {c : hs.QueryCache} {z : β × hs.QueryCache}
    (hz : z ∈ support ((simulateQ hs.romImpl X).run c)) : z.1 ∈ support X :=
  support_simulateQ_run'_subset hs.romImpl X c (by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)

/-- A lifted computation keeps the simulator's state. -/
theorem snd_eq_of_mem_support_liftM {β : Type} (x : OracleComp (unifSpec + hs) β)
    (σ : SimState Dg E C) {z : β × SimState Dg E C}
    (hz : z ∈ support ((liftM x : StateT (SimState Dg E C) (OracleComp (unifSpec + hs)) β).run σ)) :
    z.2 = σ := by
  simp only [liftM, StateT.run_monadLift, monadLift_self, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨_, -, rfl⟩ := hz
  rfl

/-- **The simulator's state is the replay of the transcript** on every reachable state of the
logged simulator, when `sim` moves its state by the replayed bookkeeping and `base` keeps it off
permutation queries. -/
theorem logImpl_state_eq_replay
    (hreplay : ∀ q σ z, z ∈ support ((sim q).run σ) → z.2 = replayStep σ (q, z.1))
    (hcoin : ∀ n σ z, z ∈ support ((base (.inl n)).run σ) → z.2 = σ)
    (hhash : ∀ m σ z, z ∈ support ((base (.inr (.inl m))).run σ) → z.2 = σ) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) {z}
    (hz : z ∈ support ((simulateQ (logImpl sim base) D).run (SimState.init iv, []))) :
    z.2.1 = replay iv z.2.2 := by
  refine inv_of_mem_support_run (spec' := unifSpec + hs) (logImpl sim base)
    (fun s ↦ s.1 = replay iv s.2) (fun t s hinv w hw ↦ ?_) D rfl z hz
  have hkeep (h : ∀ u ∈ support ((base t).run s.1), u.2 = s.1)
      (hw : w ∈ support ((fun z ↦ (z.1, (z.2, s.2))) <$> (base t).run s.1)) :
      w.2.1 = replay iv w.2.2 := by
    rw [support_map] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact (h u hu).trans hinv
  rcases t with n | m | q
  · exact hkeep (hcoin n _) hw
  · exact hkeep (hhash m _) hw
  · simp only [logImpl, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hreplay q _ _ hu, hinv]
    rfl

/-- **The logged simulator, run in the random oracle model**: on every reachable state, the
simulator's state is the replay of the transcript, and an invariant `Good` of the simulator's
state and the cache holds, when `sim` moves its state by the replayed bookkeeping
(`replayStep`) and keeps `Good`, and `base` keeps the simulator's state off permutation
queries. -/
theorem logImpl_reachable (Good : SimState Dg E C → hs.QueryCache → Prop)
    (hreplay : ∀ q σ z, z ∈ support ((sim q).run σ) → z.2 = replayStep σ (q, z.1))
    (hcoin : ∀ n σ z, z ∈ support ((base (.inl n)).run σ) → z.2 = σ)
    (hhash : ∀ m σ z, z ∈ support ((base (.inr (.inl m))).run σ) → z.2 = σ)
    (hmono : ∀ σ c c', Good σ c → c ≤ c' → Good σ c')
    (hsim : ∀ q σ c, Good σ c → ∀ w ∈ support ((simulateQ hs.romImpl ((sim q).run σ)).run c),
      Good w.1.2 w.2)
    (hinit : Good (SimState.init iv) ∅) {α : Type}
    (D : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) {z}
    (hz : z ∈ support ((simulateQ (foldRO (logImpl sim base)) D).run
      (((SimState.init iv : SimState Dg E C), []), ∅))) :
    z.2.1.1 = replay iv z.2.1.2 ∧ Good z.2.1.1 z.2.2 := by
  refine inv_of_mem_support_run (spec' := unifSpec) (foldRO (logImpl sim base))
    (fun s ↦ s.1.1 = replay iv s.1.2 ∧ Good s.1.1 s.2) (fun t s hinv w hw ↦ ?_) D ⟨rfl, hinit⟩ z hz
  rw [foldRO_run] at hw
  simp only [support_map, Set.mem_image] at hw
  obtain ⟨y, hy, rfl⟩ := hw
  have hkeep (h : ∀ u ∈ support ((simulateQ hs.romImpl ((base t).run s.1.1)).run s.2),
      u.1.2 = s.1.1) (hy : y ∈ support ((simulateQ hs.romImpl
        ((fun z ↦ (z.1, (z.2, s.1.2))) <$> (base t).run s.1.1)).run s.2)) :
      y.1.2.1 = replay iv y.1.2.2 ∧ Good y.1.2.1 y.2 := by
    rw [simulateQ_map, StateT.run_map, support_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hu' := h u hu
    exact ⟨hu'.trans hinv.1,
      hmono u.1.2 s.2 u.2 (hu' ▸ hinv.2) (le_of_mem_support_run ((base t).run s.1.1) s.2 hu)⟩
  rcases t with n | m | q
  · exact hkeep (fun u hu ↦ hcoin n _ _ (fst_mem_support_of_mem_support_rom hu)) hy
  · exact hkeep (fun u hu ↦ hhash m _ _ (fst_mem_support_of_mem_support_rom hu)) hy
  · simp only [logImpl, StateT.run_mk, simulateQ_map, StateT.run_map, support_map,
      Set.mem_image] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    refine ⟨?_, hsim q _ _ hinv.2 u hu⟩
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hreplay q _ _ (fst_mem_support_of_mem_support_rom hu), hinv.1]
    rfl

end Logged

end Setting

end Common
