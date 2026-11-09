/-
  LeanVM.Protocol.Rpm.Coins

  Private coins do not help an adversary against lazily sampled oracles: in the two-oracle
  random-oracle model (`LeanVM/Protocol/Rom/Statement.lean`) and in the random-permutation
  experiments of `Statement/LeanVm.lean`.
-/

import LeanVM.Protocol.LeanVMSound
import Statement.LeanVm
import Common.Prob
import LeanVM.Protocol.WithHash

/-!
# Adversaries with coins

Against an oracle that answers a coin uniformly, its state unchanged, and a query with a state
that the old state, the query and the answer determine, an adversary with coins does no better
than some deterministic adversary of as many oracle queries, coins not counted (`exists_det_of`):
at a coin, the best of the finitely many continuations; at an oracle query, the query followed by
the best continuation at each answer. Two instances:

* **the random oracles** (`exists_det`): `KnowledgeSoundnessRom`
  (`LeanVM/Protocol/Rom/Statement.lean`) quantifies over adversaries querying the two random
  oracles only, and the random-oracle adversary that the random-permutation transfer produces
  (`Common.advS2`: the adversary with the indifferentiability simulator) also flips coins; so the
  bound of `knowledgeSoundnessRom_holds` holds for it (`knowledgeSoundness_coins`);
* **the random permutation** (`exists_det_rpm`): the end statements of `Statement/LeanVm.lean`
  quantify over adversaries with coins against `loggedRandomPermutationOracles`, the state the permutation's edges
  and the transcript the extractor reads. Each experiment is bounded by the experiment of a
  deterministic adversary (`DetAdversary`; `rpmExperiment_le_det`, `rpmRun_le_det`), against
  which the proofs run (`detExperiment`, `detRun`).
-/

open OracleComp OracleSpec
open scoped ENNReal

namespace LeanVM.Rpm

open LeanVM.Semantics LeanVM.Protocol.Compile

/-- Oracle calls, coins free. -/
def hashCalls : (unifSpec + KeccakCalls).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem romImpl_inl_run (n : ℕ) (c : KeccakCalls.QueryCache) :
    (KeccakCalls.romImpl (.inl n)).run c = (fun x => (x, c)) <$> (unifSpec.query n : ProbComp _) := by
  simp [unifFwdImpl]

/-- The cache after a random-oracle step answering `u` at `t` from `c`. -/
def stepCache (c : KeccakCalls.QueryCache) (t : KeccakCalls.Domain) (u : KeccakCalls.Range t) :
    KeccakCalls.QueryCache :=
  match c t with
  | some _ => c
  | none => c.cacheQuery t u

theorem snd_eq_stepCache {c : KeccakCalls.QueryCache} {t : KeccakCalls.Domain}
    {z : KeccakCalls.Range t × KeccakCalls.QueryCache} (hz : z ∈ support ((KeccakCalls.randomOracle t).run c)) :
    z.2 = stepCache c t z.1 := by
  rw [randomOracle.run_eq] at hz
  unfold stepCache
  cases h : c t with
  | some u =>
    simp only [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz; rfl
  | none =>
    simp only [h, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    rfl

/-- **Derandomization**, for a stateful oracle that answers a coin uniformly, the state unchanged,
and a query with a new state that the old state, the query and the answer determine (`next`): an
adversary with coins does no better than some deterministic adversary of the same query budget,
coins not counted, for any continuation and any event. At a coin, the best of the finitely many
continuations; at an oracle query, the query followed by the best continuation at each answer. -/
theorem exists_det_of {ι σ α γ : Type} {spec : OracleSpec.{0, 0} ι}
    (impl : QueryImpl (unifSpec + spec) (StateT σ ProbComp)) (next : σ → (t : ι) → spec t → σ)
    (hcoin : ∀ n s, ∀ z ∈ support ((impl (.inl n)).run s), z.2 = s)
    (hnext : ∀ t s, ∀ z ∈ support ((impl (.inr t)).run s), z.2 = next s t z.1)
    (w : (unifSpec + spec).Domain → ℕ) (hw0 : ∀ n, w (.inl n) = 0) (hw1 : ∀ t, w (.inr t) = 1)
    (g : α × σ → ProbComp γ) (E : γ → Prop) (X : OracleComp (unifSpec + spec) α) :
    ∀ (Q : ℕ), Common.QueryCostAtMost X w Q → ∀ s : σ,
      ∃ A : OracleComp spec α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ impl X).run s >>= g}[E y] ≤
          Pr{let y ← (simulateQ (fun t ↦ impl (.inr t)) A).run s >>= g}[E y] := by
  induction X using OracleComp.inductionOn with
  | pure a =>
    intro Q _ s
    exact ⟨pure a, trivial, by simp⟩
  | query_bind t k ih =>
    intro Q hX s
    rw [Common.isWeightBound_query_bind_iff] at hX
    obtain ⟨ht, hk⟩ := hX
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
    rcases t with n | t
    · -- a coin: average below the best continuation
      have hk' : ∀ u, Common.QueryCostAtMost (k u) w Q := fun u ↦ by
        simpa [hw0] using hk u
      choose A hA hle using fun u ↦ ih u Q (hk' u) s
      let f : Fin (n + 1) → ℝ≥0∞ := fun u ↦
        Pr{let y ← (simulateQ (fun t ↦ impl (.inr t)) (A u)).run s >>= g}[E y]
      obtain ⟨u₀, hu₀⟩ := Finite.exists_max f
      refine ⟨A u₀, hA u₀, ?_⟩
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz ↦ ?_
      rw [hcoin n s z hz]
      exact (hle z.1).trans (hu₀ z.1)
    · -- an oracle query: query it, then follow the best continuation at each answer
      have hQ : 1 ≤ Q := hw1 t ▸ ht
      have hk' : ∀ u, Common.QueryCostAtMost (k u) w (Q - 1) := fun u ↦ hw1 t ▸ hk u
      choose A hA hle using fun u ↦ ih u (Q - 1) (hk' u) (next s t u)
      refine ⟨liftM (spec.query t) >>= A, ?_, ?_⟩
      · exact isTotalQueryBound_query_bind_iff.mpr ⟨by omega, hA⟩
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
          OracleQuery.cont_query, id_map, StateT.run_bind, bind_assoc]
        refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun z hz ↦ ?_
        rw [hnext t s z hz]
        exact hle z.1

/-- **Derandomization against the random oracle**: an adversary with coins does no better than
some deterministic adversary of the same query budget, for any continuation and any event. -/
theorem exists_det {α γ : Type} (g : α × KeccakCalls.QueryCache → ProbComp γ) (E : γ → Prop)
    (X : OracleComp (unifSpec + KeccakCalls) α) :
    ∀ (Q : ℕ), Common.QueryCostAtMost X hashCalls Q → ∀ c : KeccakCalls.QueryCache,
      ∃ A : OracleComp KeccakCalls α, IsTotalQueryBound A Q ∧
        Pr{let y ← (simulateQ KeccakCalls.romImpl X).run c >>= g}[E y] ≤
          Pr{let y ← (simulateQ KeccakCalls.randomOracle A).run c >>= g}[E y] :=
  exists_det_of KeccakCalls.romImpl stepCache
    (fun n c z hz ↦ by
      rw [romImpl_inl_run, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rfl)
    (fun _ _ _ hz ↦ snd_eq_stepCache hz) hashCalls (fun _ ↦ rfl) (fun _ ↦ rfl) g E X

/-- The random-oracle experiment (`LeanVM/Protocol/Rom/Statement.lean`) against an adversary that also has private coins. -/
noncomputable def experimentCoins (B : OracleComp (unifSpec + KeccakCalls) (ProgramAndInput × Proof)) :
    ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ KeccakCalls.romImpl B).run ∅
  let (verdict, cache) ←
    (simulateQ KeccakCalls.randomOracle (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-- **Knowledge soundness against adversaries with coins**: private coins do not help, so the
bound of `knowledgeSoundnessRom_holds` holds for every adversary with coins of at most `Q` oracle
calls. -/
theorem knowledgeSoundness_coins {B : OracleComp (unifSpec + KeccakCalls) (ProgramAndInput × Proof)} {Q : ℕ}
    (hB : Common.QueryCostAtMost B hashCalls Q) :
    Pr{let z ← experimentCoins B}[Breaks extractor z] ≤ soundnessError Q := by
  obtain ⟨A, hA, hle⟩ := exists_det (fun p ↦ do
      let (verdict, cache) ←
        (simulateQ KeccakCalls.randomOracle (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1 p.1.1.2 p.1.2)).run p.2
      return ((p.1, verdict), cache, p.2)) (Breaks extractor) B Q hB ∅
  exact hle.trans (knowledgeSoundnessRom_holds A Q hA)

/-! ## The random-permutation experiments -/

/-- The oracle of a deterministic adversary: `loggedRandomPermutationOracles` (`Statement/LeanVm.lean`) on `π` and
`π⁻¹`. -/
noncomputable def loggedPermDet : QueryImpl (Common.permutationOracleSpec KeccakState) (StateT (Common.PermutationEdges KeccakState × PermutationTranscript) ProbComp) :=
  fun q ↦ loggedRandomPermutationOracles (.inr q)

/-- A deterministic adversary in the random-permutation model: oracle access to `π` and `π⁻¹`,
no coins. -/
abbrev DetAdversary : Type := OracleComp (Common.permutationOracleSpec KeccakState) (ProgramAndInput × Proof)

/-- `rpmExperiment` (`Statement/LeanVm.lean`) for a deterministic adversary. -/
noncomputable def detExperiment (A : DetAdversary) : ProbComp ExperimentOutcomeWithHash := do
  let (z, perms, transcript) ← (simulateQ loggedPermDet A).run ([], [])
  let verdict ← (simulateQ keccakCallsOverRandomPermutation (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run' perms
  return ((z, verdict), transcript)

/-- `runAdversaryThen` (`Statement/LeanVm.lean`) for a deterministic adversary, without the transcript. -/
noncomputable def detRun {α β : Type} (A : OracleComp (Common.permutationOracleSpec KeccakState) α)
    (V : α → OracleComp KeccakCalls β) : ProbComp (α × β) := do
  let (z, perms, _) ← (simulateQ loggedPermDet A).run ([], [])
  let v ← (simulateQ keccakCallsOverRandomPermutation (V z)).run' perms
  return (z, v)

/-- The edges after the lazily sampled permutation answers `a` to `q` from the edges `E`. -/
def stepLog (E : Common.PermutationEdges KeccakState) : (q : Common.PermutationQuery KeccakState) → KeccakState → (Common.PermutationEdges KeccakState)
  | .forward x, a => match Common.forwardLookup E x with
    | some _ => E
    | none => (x, a) :: E
  | .inverse y, a => match Common.inverseLookup E y with
    | some _ => E
    | none => (a, y) :: E

/-- The state after a query to `π` or `π⁻¹` is determined by its answer. -/
theorem snd_eq_stepLog {q : Common.PermutationQuery KeccakState} {s : (Common.PermutationEdges KeccakState) × PermutationTranscript}
    {z : KeccakState × (Common.PermutationEdges KeccakState × PermutationTranscript)} (hz : z ∈ support ((loggedRandomPermutationOracles (.inr q)).run s)) :
    z.2 = (stepLog s.1 q z.1, s.2 ++ [(q, z.1)]) := by
  simp only [loggedRandomPermutationOracles, StateT.run_mk, support_map, Set.mem_image] at hz
  obtain ⟨r, hr, rfl⟩ := hz
  cases q with
  | forward x =>
    simp only [Common.lazyRandomPermutation, StateT.run_mk] at hr
    rcases hx : Common.forwardLookup s.1 x with _ | y
    · rw [hx] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨y, -, rfl⟩ := hr
      simp [stepLog, hx]
    · rw [hx] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp [stepLog, hx]
  | inverse y =>
    simp only [Common.lazyRandomPermutation, StateT.run_mk] at hr
    rcases hy : Common.inverseLookup s.1 y with _ | x
    · rw [hy] at hr
      simp only [support_map, Set.mem_image] at hr
      obtain ⟨x, -, rfl⟩ := hr
      simp [stepLog, hy]
    · rw [hy] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp [stepLog, hy]

/-- **Coins do not help in the random-permutation model**: against `loggedRandomPermutationOracles`, an adversary
with coins of at most `Q` queries to `π` and `π⁻¹` does no better than some deterministic
adversary of at most `Q` queries, for any continuation and any event. -/
theorem exists_det_rpm {α γ : Type} (g : α × (Common.PermutationEdges KeccakState × PermutationTranscript) → ProbComp γ) (E : γ → Prop)
    {B : OracleComp (unifSpec + Common.permutationOracleSpec KeccakState) α} {Q : ℕ} (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) :
    ∃ A : OracleComp (Common.permutationOracleSpec KeccakState) α, A.IsTotalQueryBound Q ∧
      Pr{let y ← (simulateQ loggedRandomPermutationOracles B).run ([], []) >>= g}[E y] ≤
        Pr{let y ← (simulateQ loggedPermDet A).run ([], []) >>= g}[E y] :=
  exists_det_of loggedRandomPermutationOracles (fun s q a ↦ (stepLog s.1 q a, s.2 ++ [(q, a)]))
    (fun n s z hz ↦ by
      simp only [loggedRandomPermutationOracles, liftM, monadLift, MonadLift.monadLift, StateT.run_lift,
        support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
      obtain ⟨u, -, rfl⟩ := hz
      rfl)
    (fun _ _ _ hz ↦ snd_eq_stepLog hz) Common.permutationCallCost (fun _ ↦ rfl) (fun _ ↦ rfl) g E B Q hB ([], [])

/-- **The experiment against an adversary with coins is bounded by a deterministic one's**:
for every event, some deterministic adversary of as many queries to `π` and `π⁻¹`. -/
theorem rpmExperiment_le_det {B : RandomPermutationAdversary} {Q : ℕ}
    (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) (E : ExperimentOutcomeWithHash → Prop) :
    ∃ A : DetAdversary, A.IsTotalQueryBound Q ∧
      Pr{let z ← soundnessExperimentWithHash B}[E z] ≤ Pr{let z ← detExperiment A}[E z] :=
  exists_det_rpm _ E hB

/-- **`runAdversaryThen` against an adversary with coins is bounded by a deterministic one's**: for every
event of the outputs, some deterministic adversary of as many queries to `π` and `π⁻¹`. -/
theorem rpmRun_le_det {α β : Type} {B : OracleComp (unifSpec + Common.permutationOracleSpec KeccakState) α} {Q : ℕ}
    (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) (V : α → OracleComp KeccakCalls β)
    (E : α × β → Prop) :
    ∃ A : OracleComp (Common.permutationOracleSpec KeccakState) α, A.IsTotalQueryBound Q ∧
      Pr{let z ← runAdversaryThen B V}[E z.1] ≤ Pr{let z ← detRun A V}[E z] := by
  obtain ⟨A, hA, hle⟩ := exists_det_rpm (fun p ↦ do
      let v ← (simulateQ keccakCallsOverRandomPermutation (V p.1)).run' p.2.1
      return ((p.1, v), p.2.2)) (fun z ↦ E z.1) hB
  refine ⟨A, hA, hle.trans (le_of_eq ?_)⟩
  have h : detRun A V = (fun z ↦ z.1) <$> ((simulateQ loggedPermDet A).run ([], []) >>= fun p ↦ do
      let v ← (simulateQ keccakCallsOverRandomPermutation (V p.1)).run' p.2.1
      return ((p.1, v), p.2.2)) := by
    simp only [detRun, map_bind, map_pure]
  rw [h, prEvent_map]

end LeanVM.Rpm
