module

public import Common.Indiff2.Bound
public import Common.Defs

@[expose] public section

/-!
# Transfer in the two-oracle model: a hash `H` and direct permutation calls `F`

A protocol such as leanVM calls the permutation `π` in two ways: through the sponge hash (`H`),
and directly, in a Fiat–Shamir duplex (`F`). Its random-oracle-model (ROM) proofs use two
independent oracles: a random oracle `H` and a random function `F` on states, both queried by the
honest parties and by the adversary. In the random-permutation model (RPM) `H` is the sponge over
`π`, `F` is `π`, and the adversary queries `π` and `π⁻¹`.

* `transfer2`: for a game made of an honest part using `H` (`pre`), an adversary `A` using `H`,
  `π`, `π⁻¹` (in the RPM), and an honest part using `H` and `F` (`post`) whose direct calls follow
  the duplex discipline (`Duplex`), the RPM game (`realGame2`) and the ROM game against the ROM
  adversary `advS2 A` (`A` with its permutation queries answered by the simulator `simulator2`,
  which queries `H` and `F`) give every event probabilities within `indiffBound2`.
* `pathsOf_ideal2`: as in the one-oracle model, the hash queries the simulator makes for the
  adversary are `pathsOf` of the adversary's permutation transcript, so an extractor reading the
  ROM adversary's `H` queries runs in the RPM on the adversary's own hash queries and `pathsOf`
  of its permutation transcript (whose pairs are correct sponge hashes, `pathsOf_sound`).

The duplex discipline: every direct call `F x` absorbs a non-final block (`NF`, a block that no
padding ends with) into the initial state of the sponge or into the answer of an earlier direct
call, keeping the capacity. leanVM's duplex (`crates/verifier/src/transcript.rs`) does: its
initial state is the zero state with lanes `0..8` overwritten, and each duplexing overwrites
lanes `0..16` of the previous answer, so the absorbed block is zero in lane 16, the lane of the
padding's last byte `0x80`.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

namespace Common

/-- The two-oracle bound: the sponge's indifferentiability bound plus `q² / |C|` for the direct
calls. -/
noncomputable def indiffBound2 (nS nC q : ℕ) : ℝ≥0∞ :=
  indiffBound nS nC q + q * (q / (nC : ℝ≥0∞))

theorem add_chain_le {a i b f ε δ : ℝ≥0∞} (h1 : a ≤ i + ε) (h2 : i ≤ b + f) (h3 : f ≤ δ) :
    a ≤ b + (ε + δ) :=
  calc a ≤ i + ε := h1
    _ ≤ (b + δ) + ε := add_le_add (h2.trans (add_le_add le_rfl h3)) le_rfl
    _ = b + (ε + δ) := by ring

theorem add_chain_le' {a i b f ε δ : ℝ≥0∞} (h1 : i ≤ a + ε) (h2 : b ≤ i + f) (h3 : f ≤ δ) :
    b ≤ a + (ε + δ) :=
  calc b ≤ i + f := h2
    _ ≤ (a + ε) + δ := add_le_add h1 h3
    _ = a + (ε + δ) := by ring

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]
  (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)

/-! ## Games -/

/-- A ROM computation with `H` only as a two-oracle ROM computation. -/
def hInF : QueryImpl (unifSpec + roSpec Msg Dg)
    (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)))
  | .inl n => liftM ((unifSpec + hfSpec Msg Dg (SpState Dg E C)).query (.inl n))
  | .inr m => liftM ((unifSpec + hfSpec Msg Dg (SpState Dg E C)).query (.inr (.inl m)))

/-- The two-oracle ROM run: `H` and `F` independent random oracles. -/
noncomputable def romRun2 {α : Type}
    (X : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α) :
    ProbComp α :=
  (simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl X).run' ∅

/-- **The duplex discipline** of an honest computation: along every run, every direct call
`F x` is admissible after the answers of the earlier direct calls (`hist`, newest first). -/
def Duplex (NF : (Dg × E) → Prop) {α : Type} :
    OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α → List (SpState Dg E C) → Prop
  | .pure _, _ => True
  | .liftBind (.inr (.inr x)) k, hist =>
      Admissible iv NF hist x ∧ ∀ y, Duplex NF (k y) (y :: hist)
  | .liftBind _ k, hist => ∀ u, Duplex NF (k u) hist

/-! ## The shadow world of a game is the ROM game -/

theorem run_shadow_hEmbed2 {α : Type} (X : OracleComp (unifSpec + roSpec Msg Dg) α)
    (σ : SimState Dg E C) :
    (simulateQ (shadowImpl P) (simulateQ (hEmbed2 (E := E) (C := C)) X)).run σ =
      (·, σ) <$> simulateQ (hInF (E := E) (C := C)) X := by
  induction X using OracleComp.inductionOn generalizing σ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run_bind, simulateQ_query_bind]
    rcases t with n | m
    · simp only [hEmbed2, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, shadowImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, ih, hInF]
      simp [map_eq_bind_pure_comp]
      rfl
    · simp only [hEmbed2, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, shadowImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, ih, hInF]
      simp [map_eq_bind_pure_comp]
      rfl

theorem shadow_comp_advEmbed :
    (shadowImpl (Msg := Msg) P) ∘ₛ (advEmbed (Msg := Msg) (Dg := Dg) (E := E) (C := C)) =
      advImpl2 P := by
  funext t
  rcases t with n | m | q <;> simp [advEmbed, shadowImpl, advImpl2]

theorem run'_shadow_hfEmbed {α : Type}
    (X : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α) (σ : SimState Dg E C) :
    (simulateQ (shadowImpl P) (simulateQ (hfEmbed (Msg := Msg)) X)).run' σ = X := by
  induction X using OracleComp.inductionOn generalizing σ with
  | pure a => simp
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind]
    rcases t with n | m | x
    · simp only [hfEmbed, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, shadowImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        map_bind]
      simp only [← StateT.run'_eq, ih]
      rfl
    · simp only [hfEmbed, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
        id_map, shadowImpl, StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind,
        map_bind]
      simp only [← StateT.run'_eq, ih]
      rfl
    · simp only [hfEmbed, OracleQuery.input_query, OracleQuery.cont_query, map_bind]
      simp only [← StateT.run'_eq, ih]
      rfl

/-- **The shadow world of a two-oracle game is the ROM game against the simulated adversary.** -/
theorem shadow_rpmGame2 {β γ δ : Type} (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) δ) :
    (simulateQ (shadowImpl P) (rpmGame2 pre A post)).run' (SimState.init iv) =
      simulateQ (hInF (E := E) (C := C)) pre >>= fun x ↦
        advS2 P iv (A x) >>= fun a ↦ post x a := by
  simp only [rpmGame2, advS2, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    run_shadow_hEmbed2, bind_map_left, map_bind]
  refine bind_congr fun x ↦ ?_
  rw [← QueryImpl.simulateQ_compose, shadow_comp_advEmbed]
  refine bind_congr fun z ↦ ?_
  rw [← StateT.run'_eq, run'_shadow_hfEmbed]

/-! ## The duplex discipline of a game -/

theorem duplexOK_bind_hEmbed2 (NF : (Dg × E) → Prop) {α δ : Type}
    (X : OracleComp (unifSpec + roSpec Msg Dg) α)
    (f : α → OracleComp (dSpec2 Msg Dg (SpState Dg E C)) δ) (hist : List (SpState Dg E C))
    (hf : ∀ a, DuplexOK iv NF (f a) hist) :
    DuplexOK iv NF (simulateQ (hEmbed2 (E := E) (C := C)) X >>= f) hist := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [simulateQ_query_bind, bind_assoc]
    rcases t with n | m
    · exact (duplexOK_query_bind_other iv NF (.inl n) (by simp) _ hist).mpr ih
    · exact (duplexOK_query_bind_other iv NF (.inr (.inl m)) (by simp) _ hist).mpr ih

theorem duplexOK_bind_advEmbed (NF : (Dg × E) → Prop) {α δ : Type}
    (X : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (f : α → OracleComp (dSpec2 Msg Dg (SpState Dg E C)) δ) (hist : List (SpState Dg E C))
    (hf : ∀ a, DuplexOK iv NF (f a) hist) :
    DuplexOK iv NF (simulateQ (advEmbed (Msg := Msg)) X >>= f) hist := by
  induction X using OracleComp.inductionOn with
  | pure a => simpa using hf a
  | query_bind t k ih =>
    rw [simulateQ_query_bind, bind_assoc]
    rcases t with n | m | q
    · exact (duplexOK_query_bind_other iv NF (.inl n) (by simp) _ hist).mpr ih
    · exact (duplexOK_query_bind_other iv NF (.inr (.inl m)) (by simp) _ hist).mpr ih
    · exact (duplexOK_query_bind_other iv NF (.inr (.inr (.inl q))) (by simp) _ hist).mpr ih

theorem duplexOK_hfEmbed (NF : (Dg × E) → Prop) {α : Type}
    (X : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) α)
    (hist : List (SpState Dg E C)) (hX : Duplex iv NF X hist) :
    DuplexOK iv NF (simulateQ (hfEmbed (Msg := Msg)) X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_query_bind]
    rcases t with n | m | x
    · exact (duplexOK_query_bind_other iv NF (.inl n) (by simp) _ hist).mpr
        fun u ↦ ih u hist (hX u)
    · exact (duplexOK_query_bind_other iv NF (.inr (.inl m)) (by simp) _ hist).mpr
        fun u ↦ ih u hist (hX u)
    · exact (duplexOK_query_bind_F iv NF x _ hist).mpr ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

theorem duplexOK_rpmGame2 (NF : (Dg × E) → Prop) {β γ δ : Type}
    (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) δ)
    (hpost : ∀ x a, Duplex iv NF (post x a) []) :
    DuplexOK iv NF (rpmGame2 pre A post) [] :=
  duplexOK_bind_hEmbed2 iv NF pre _ [] fun x ↦
    duplexOK_bind_advEmbed iv NF (A x) _ [] fun a ↦ duplexOK_hfEmbed iv NF _ [] (hpost x a)

/-! ## Transfer -/

/-- **Transfer in the two-oracle model.** For a game made of an honest part with `H` (`pre`), an
RPM adversary `A` with `H`, `π`, `π⁻¹`, and an honest part with `H` and direct calls `F`
(`post`) following the duplex discipline for a block predicate `NF` that no padding ends with,
of total cost at most `q` (`queryCost2`: a hash call costs its padded length in blocks, a
permutation query or direct call one), every event has probabilities in the RPM (`realGame2`:
`H` the sponge over `π`, `F = π`) and in the two-oracle ROM against the ROM adversary
`advS2 P iv A` within `indiffBound2 |S| |C| q`. -/
theorem transfer2 (NF : (Dg × E) → Prop) [DecidablePred NF]
    (hNF : ∀ m β B, P.pad m = β ++ [B] → ¬ NF B) {β γ δ : Type}
    (pre : OracleComp (unifSpec + roSpec Msg Dg) β)
    (A : β → OracleComp (dSpec Msg Dg (SpState Dg E C)) γ)
    (post : β → γ → OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) δ)
    (hpost : ∀ x a, Duplex iv NF (post x a) []) (q : ℕ)
    (hq : QueryCostAtMost (rpmGame2 pre A post) (queryCost2 (Dg := Dg) P) q) (p : δ → Prop) :
    Pr{let a ← realGame2 P iv (rpmGame2 pre A post)}[p a] ≤
        Pr{let a ← romRun2 (simulateQ (hInF (E := E) (C := C)) pre >>= fun x ↦
          advS2 P iv (A x) >>= fun a ↦ post x a)}[p a] +
          indiffBound2 (Fintype.card (SpState Dg E C)) (Fintype.card C) q ∧
      Pr{let a ← romRun2 (simulateQ (hInF (E := E) (C := C)) pre >>= fun x ↦
          advS2 P iv (A x) >>= fun a ↦ post x a)}[p a] ≤
        Pr{let a ← realGame2 P iv (rpmGame2 pre A post)}[p a] +
          indiffBound2 (Fintype.card (SpState Dg E C)) (Fintype.card C) q := by
  set G := rpmGame2 pre A post
  obtain ⟨h1, h1'⟩ := indifferentiability P iv (simulateQ (toOne (E := E) (C := C)) G) q
    (isWeightBound_toOne P G q hq) p
  have h2 := (ideal1_evalDistEq_ideal1F P iv G).prEvent_eq p
  obtain ⟨h3, h3'⟩ := ideal1F_le_shadow P iv NF G p
  have h4 := prEvent_disagree_le P iv NF hNF G (duplexOK_rpmGame2 iv NF pre A post hpost) q hq
  have h5 : (simulateQ (foldRO (shadowImpl P)) G).run' (SimState.init iv, ∅) =
      romRun2 (simulateQ (hInF (E := E) (C := C)) pre >>= fun x ↦
        advS2 P iv (A x) >>= fun a ↦ post x a) := by
    rw [← run'_simulateQ_foldRO, shadow_rpmGame2]
    rfl
  rw [h5] at h3 h3'
  rw [h2] at h3 h3'
  exact ⟨add_chain_le h1 h3 h4, add_chain_le' h1' h3' h4⟩

/-! ## Hash queries from permutation transcripts -/

/-- A step of the two-oracle simulator moves its state by the replayed bookkeeping. -/
theorem simulator2_step_replay (q : PermutationQuery (SpState Dg E C)) (σ : SimState Dg E C) {z}
    (hz : z ∈ support ((simulator2 (Msg := Msg) P q).run σ)) : z.2 = replayStep σ (q, z.1) := by
  cases q with
  | forward x =>
    simp only [simulator2, StateT.run_mk] at hz
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
    simp only [simulator2, StateT.run_mk] at hz
    simp only [replayStep]
    split at hz
    · next x hx =>
      simp only [support_pure, Set.mem_singleton_iff] at hz; subst hz; simp [hx]
    · next hx =>
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨x, -, rfl⟩ := hz
      simp [hx]

/-- The two-oracle ROM adversary with its permutation transcript logged, oldest first. -/
noncomputable def advImplLog2 : QueryImpl (dSpec Msg Dg (SpState Dg E C))
    (StateT (SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C))
      (OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C))))
  | .inr (.inr q) => StateT.mk fun s ↦
      (fun z ↦ (z.1, (z.2, s.2 ++ [(q, z.1)]))) <$> (simulator2 P q).run s.1
  | t => StateT.mk fun s ↦ (fun z ↦ (z.1, (z.2, s.2))) <$> (advImpl2 P t).run s.1

/-- Forgetting the transcript gives the two-oracle ROM adversary. -/
theorem advImplLog2_proj {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    (s : SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) :
    Prod.map id Prod.fst <$> (simulateQ (advImplLog2 P) A).run s =
      (simulateQ (advImpl2 P) A).run s.1 :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ _ (fun t s ↦ by
    rcases t with n | m | q <;> simp [advImplLog2, advImpl2, Functor.map_map]) A s

/-- **The simulator's state is the replay of the transcript**, in the two-oracle model. -/
theorem simulator2_state_eq_replay {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α)
    {z} (hz : z ∈ support ((simulateQ (advImplLog2 P) A).run (SimState.init iv, []))) :
    z.2.1 = replay iv z.2.2 := by
  refine inv_of_mem_support_run (spec' := unifSpec + hfSpec Msg Dg (SpState Dg E C))
    (advImplLog2 P) (fun s ↦ s.1 = replay iv s.2) (fun t s hs w hw ↦ ?_) A rfl z hz
  rcases t with n | m | q
  · simp only [advImplLog2, advImpl2, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hw
    obtain ⟨_, ⟨u, -, rfl⟩, rfl⟩ := hw
    exact hs
  · simp only [advImplLog2, advImpl2, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hw
    obtain ⟨_, ⟨u, -, rfl⟩, rfl⟩ := hw
    exact hs
  · simp only [advImplLog2, StateT.run_mk, support_map, Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [simulator2_step_replay P q s.1 hw', hs]
    rfl

/-- An output reachable in the two-oracle ROM is reachable with arbitrary answers. -/
theorem fst_mem_support_of_mem_support_ro2 {β : Type}
    {X : OracleComp (unifSpec + hfSpec Msg Dg (SpState Dg E C)) β}
    {c : HCache Msg Dg (SpState Dg E C)} {z : β × HCache Msg Dg (SpState Dg E C)}
    (hz : z ∈ support ((simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl X).run c)) :
    z.1 ∈ support X :=
  support_simulateQ_run'_subset (hfSpec Msg Dg (SpState Dg E C)).romImpl X c (by
    rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)

/-- The digests of the simulator's rooted paths are cached `H` answers, and stay. -/
theorem roOK2_step (t : (dSpec Msg Dg (SpState Dg E C)).Domain)
    (s : (SimState Dg E C × List (PermutationQuery (SpState Dg E C) × SpState Dg E C)) ×
      HCache Msg Dg (SpState Dg E C))
    (hs : ∀ md ∈ simPaths P s.1.1, s.2 (.inl md.1) = some md.2) {z}
    (hz : z ∈ support (((foldRO (advImplLog2 P)) t).run s)) :
    ∀ md ∈ simPaths P z.2.1.1, z.2.2 (.inl md.1) = some md.2 := by
  rw [foldRO_run] at hz
  simp only [support_map, Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hle := le_of_mem_support_run _ s.2 hw
  have hold : ∀ md ∈ simPaths P s.1.1, w.2 (.inl md.1) = some md.2 := fun md hmd ↦
    hle (hs md hmd)
  rcases t with n | m | q
  · have := fst_mem_support_of_mem_support_ro2 hw
    simp only [advImplLog2, advImpl2, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at this
    obtain ⟨_, ⟨u, -, rfl⟩, h⟩ := this
    rw [← h]; exact hold
  · have := fst_mem_support_of_mem_support_ro2 hw
    simp only [advImplLog2, advImpl2, StateT.run_mk, StateT.run_monadLift, monadLift_self,
      support_map, Set.mem_image, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at this
    obtain ⟨_, ⟨u, -, rfl⟩, h⟩ := this
    rw [← h]; exact hold
  · simp only [advImplLog2, StateT.run_mk, simulateQ_map, StateT.run_map, support_map,
      Set.mem_image] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    simp only at hold ⊢
    cases q with
    | inverse y =>
      have := simulator2_step_replay P _ _ (fst_mem_support_of_mem_support_ro2 hw')
      rw [this]
      simp only [replayStep]
      split
      · exact hold
      · exact hold
    | forward x =>
      simp only [simulator2, StateT.run_mk] at hw'
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
            rw [rootedAnswer2_run_some P hm'] at hy
            simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff,
              support_uniformSample, Set.mem_univ, true_and] at hy
            obtain ⟨⟨d, c₂⟩, hd, ec, hec⟩ := hy
            simp only [Prod.mk.injEq] at hec
            obtain ⟨rfl, rfl⟩ := hec
            exact (roStep_support _ _ hd).2.1
          · exact hold md (List.mem_filterMap.mpr ⟨p, hp, hpm⟩)
        · simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
            fQuery_run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hw'
          obtain ⟨w₁, -, rfl⟩ := hw'
          exact hold

/-- **The hash queries of the adversary's transcript, in the two-oracle ROM**: on every reachable
state of the logged two-oracle ROM adversary, every pair `(m, d)` of `pathsOf` of the
adversary's permutation transcript is the random oracle's cached answer `H m = d`. These are
exactly the `H` queries the simulator made for the adversary (`rootedAnswer2`). -/
theorem pathsOf_ideal2 {α : Type} (A : OracleComp (dSpec Msg Dg (SpState Dg E C)) α) {z}
    (hz : z ∈ support ((simulateQ (foldRO (advImplLog2 P)) A).run
      (((SimState.init iv : SimState Dg E C), []), ∅))) :
    ∀ md ∈ pathsOf P iv z.2.1.2, z.2.2 (.inl md.1) = some md.2 := by
  have hRO := inv_of_mem_support_run (spec' := unifSpec) (foldRO (advImplLog2 P))
    (fun s ↦ ∀ md ∈ simPaths P s.1.1, s.2 (.inl md.1) = some md.2)
    (fun t s hs w hw ↦ roOK2_step P t s hs hw) A
    (s := (((SimState.init iv : SimState Dg E C), []), ∅)) (by
      simp only [simPaths, SimState.init, List.filterMap_cons, List.filterMap_nil]
      rcases h : P.unpad [] with _ | a
      · simp
      · exact absurd ((P.unpad_eq_some_iff _ _).mp h) (P.pad_ne_nil a))
    z hz
  have h1 := run_simulateQ_foldRO (advImplLog2 P) A ((SimState.init iv : SimState Dg E C), [])
    (∅ : HCache Msg Dg (SpState Dg E C))
  have hz' : ((z.1, z.2.1), z.2.2) ∈ support ((simulateQ (hfSpec Msg Dg (SpState Dg E C)).romImpl
      ((simulateQ (advImplLog2 P) A).run (SimState.init iv, []))).run ∅) := by
    rw [h1, support_map]; exact ⟨z, hz, rfl⟩
  have hrep := simulator2_state_eq_replay P iv A (fst_mem_support_of_mem_support_ro2 hz')
  intro md hmd
  rw [pathsOf, ← hrep] at hmd
  exact hRO md hmd

end Setting

end Common
