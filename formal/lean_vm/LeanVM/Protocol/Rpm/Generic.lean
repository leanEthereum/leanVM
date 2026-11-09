/-
  LeanVM.Protocol.Rpm.Generic

  The transfer from the random-permutation model to the two-oracle random-oracle model for any
  adversary querying `π` and `π⁻¹`, followed by any computation over the verifier's calls that
  follows the duplex discipline: the step of `LeanVMRpm.lean`'s proof, for other verifiers.
-/

import LeanVM.Protocol.LeanVMRpm
import LeanVM.Protocol.WithHash

/-!
# The transfer, for any verifier

`runAdversaryThen A V` (`Statement/LeanVm.lean`, its outputs), here `detRun A V` for a deterministic adversary
(`Coins.lean`, where `rpmRun_le_det` bounds an adversary with coins by one): an adversary `A`
against the lazily sampled permutation (its queries recorded, as in `rpmExperiment`), then a computation `V` on its output over the calls of `Statement.lean`, with
Keccak-256 the sponge over the same permutation and Keccak-f[1600] the permutation. If `V` follows
the duplex discipline (`DuplexVm`) and makes at most `QV` permutation calls, then for every event
`E` there is an adversary `A'` against the two independent random oracles, of as many queries as
`A`, whose experiment (`romStep`) has `E` with probability at least that of `detRun A V` less
`rpmError (Q + QV)` (`detRun_le_rom`). The proof is that of `knowledgeSoundnessRpm` without the
extractor: the experiment is the real world of a transfer game (`detRun_evalDistEq`),
`Common.keccak256_transfer2` moves it to the random-oracle game of the adversary with the
indifferentiability simulator (`romGameG_le`), and coins do not help (`exists_det`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

variable {α β : Type}

/-! ## The experiment and its game -/

/-- The adversary on bytes, with its transcript. -/
def advRG (A : OracleComp (Common.permutationOracleSpec KeccakState) α) : OracleComp RSpec (α × PermutationTranscript) :=
  (simulateQ logRel A).run []

/-- The computation on the adversary's output, its queries read on bytes. -/
def postG (V : α → OracleComp KeccakCalls β) (z : α × PermutationTranscript) : OracleComp HFSpec (α × β) :=
  (fun v ↦ (z.1, v)) <$> simulateQ toRHF (V z.1)

/-- **The transfer game** of `detRun A V`. -/
def gameG (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (V : α → OracleComp KeccakCalls β) :
    OracleComp D2Spec (α × β) :=
  Common.rpmGame2 (pure ()) (fun _ ↦ advRG A) (fun _ z ↦ postG V z)

/-- **The experiment is the real world of the transfer game.** -/
theorem detRun_evalDistEq (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (V : α → OracleComp KeccakCalls β) :
    detRun A V =ᵈ Common.realGame2 Common.keccakPadding Common.KState.zero (gameG A V) := by
  rw [realGame2_eq, gameG, Common.rpmGame2]
  simp only [simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  simp only [postG, simulateQ_map, StateT.run_map, Functor.map_map, RR,
    QueryImpl.simulateQ_compose]
  have hadv := (adv_relabel A [] []).symm
  simp only [projLog, logMap, List.map_nil, QueryImpl.simulateQ_compose] at hadv
  rw [detRun, advRG]
  refine EvalDistEq.trans (EvalDistEq.bind_left hadv _) ?_
  rw [bind_map_left]
  refine EvalDistEq.bind_right _ fun p ↦ ?_
  have h := (post_relabel' (V p.1.1) p.2).symm.map fun v ↦ (p.1.1, v)
  simp only [StateT.run'_eq, Functor.map_map, QueryImpl.simulateQ_compose, projLog, logMap] at h
  simp only [StateT.run'_eq, bind_pure_comp, Functor.map_map]
  exact h

/-! ## The game's discipline and permutation calls -/

theorem duplex_postG (V : α → OracleComp KeccakCalls β) (hV : ∀ a, DuplexVm (V a) [])
    (z : α × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postG V z) [] :=
  duplex_map _ _ [] (duplex_toRHF _ [] (hV z.1))

theorem isWeightBound_advRG_cost {A : OracleComp (Common.permutationOracleSpec KeccakState) α} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) : Common.QueryCostAtMost (advRG A) advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) _ (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query advCost (.inr (.inr (permQueryToRpm q)))))

/-- **The permutation calls of the transfer game**: the adversary's `Q`, then at most `QV` of the
computation. -/
theorem isWeightBound_gameG {A : OracleComp (Common.permutationOracleSpec KeccakState) α} {V : α → OracleComp KeccakCalls β}
    {Q QV : ℕ} (hA : A.IsTotalQueryBound Q)
    (hV : ∀ a, Common.QueryCostAtMost (V a) hashBlocks QV) :
    Common.QueryCostAtMost (gameG A V) gameCost (Q + QV) := by
  rw [gameG, Common.rpmGame2, simulateQ_pure, pure_bind]
  refine (isWeightBound_advEmbed (isWeightBound_advRG_cost hA)).bind fun z ↦ ?_
  rw [postG, simulateQ_map]
  exact Common.isWeightBound_map _ (isWeightBound_hfEmbed_toRHF (hV _))

/-! ## The random-oracle side -/

/-- The random-oracle adversary of the transfer: the adversary with the indifferentiability
simulator, its oracle queries read on lanes, its transcript dropped. -/
noncomputable def romAdvG (A : OracleComp (Common.permutationOracleSpec KeccakState) α) : OracleComp CSpec α :=
  (fun z ↦ z.1) <$> simulateQ ofRHF
    (Common.advS2 Common.keccakPadding Common.KState.zero (advRG A))

theorem isWeightBound_advRG {A : OracleComp (Common.permutationOracleSpec KeccakState) α} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (advRG A) wR Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) wR (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query wR (.inr (.inr (permQueryToRpm q)))))

/-- The random-oracle adversary makes at most one oracle query per query of the adversary to `π`
or `π⁻¹`. -/
theorem isWeightBound_romAdvG {A : OracleComp (Common.permutationOracleSpec KeccakState) α} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (romAdvG A) hashCalls Q := by
  refine Common.isWeightBound_map _ (isWeightBound_simulateQ_ofRHF ?_)
  rw [Common.advS2, StateT.run'_eq]
  exact Common.isWeightBound_map _ (Common.isWeightBound_run_simulateQ _ wR wHF
    isWeightBound_advImpl2 (isWeightBound_advRG hA) _)

/-- The computation's phase of the random-oracle experiment, from the adversary's output and the
oracles' cache. -/
noncomputable def romStep (V : α → OracleComp KeccakCalls β) (p : α × KeccakCalls.QueryCache) :
    ProbComp (α × β) :=
  (fun r ↦ (p.1, r.1)) <$> (simulateQ KeccakCalls.randomOracle (V p.1)).run p.2

/-- **The random-oracle game of the transfer is the random-oracle experiment of the transfer's
adversary**, with coins. -/
theorem romGameG_le (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (V : α → OracleComp KeccakCalls β)
    (E : α × β → Prop) :
    Pr{let a ← Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
        Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advRG A) x) >>= fun a ↦
          (fun _ z ↦ postG V z) x a)}[E a] ≤
      Pr{let z ← (simulateQ KeccakCalls.romImpl (romAdvG A)).run ∅ >>= romStep V}[E z] := by
  set X := Common.advS2 Common.keccakPadding Common.KState.zero (advRG A)
  set J := (simulateQ HFS.romImpl X).run ∅ with hJ
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advRG A) x) >>= fun a ↦
        (fun _ z ↦ postG V z) x a) =
      J >>= fun p ↦ (simulateQ HFS.romImpl (postG V p.1)).run' p.2 := by
    simp only [Common.romRun2, simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, hJ, X]
  rw [e1]
  have e2 : (simulateQ KeccakCalls.romImpl (romAdvG A)).run ∅ >>= romStep V =ᵈ
      J >>= fun p ↦ romStep V (p.1.1, cmap p.2) := by
    rw [romAdvG, simulateQ_map, StateT.run_map]
    have h := run_ofRHF X ∅
    rw [cmap_empty] at h
    rw [bind_map_left]
    refine (EvalDistEq.bind_left h _).trans ?_
    rw [bind_map_left]
    exact EvalDistEq.rfl
  rw [e2.prEvent_eq]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p _ ↦ le_of_eq ?_
  rw [postG, simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_map, prEvent_map, romStep,
    prEvent_map]
  have h := (run'_toRHF (V p.1.1) p.2).prEvent_eq (fun v ↦ E (p.1.1, v))
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map] at h
  exact h

/-! ## The transfer -/

/-- **From the random-permutation model to the two-oracle random-oracle model.** For an adversary
`A` of at most `Q` queries to `π` and `π⁻¹`, and a computation `V` that follows the duplex
discipline with at most `QV` permutation calls, every event of `detRun A V` has probability at
most that of the random-oracle experiment of some adversary `A'` of at most `Q` queries to the two
random oracles, plus `rpmError (Q + QV)`. -/
theorem detRun_le_rom (A : OracleComp (Common.permutationOracleSpec KeccakState) α) (V : α → OracleComp KeccakCalls β)
    (hV : ∀ a, DuplexVm (V a) []) {Q QV : ℕ} (hA : A.IsTotalQueryBound Q)
    (hVw : ∀ a, Common.QueryCostAtMost (V a) hashBlocks QV) (E : α × β → Prop) :
    ∃ A' : OracleComp KeccakCalls α, A'.IsTotalQueryBound Q ∧
      Pr{let z ← detRun A V}[E z] ≤
        Pr{let z ← (simulateQ KeccakCalls.randomOracle A').run ∅ >>= romStep V}[E z] +
          rpmError (Q + QV) := by
  obtain ⟨A', hA', hle⟩ := exists_det (romStep V) E (romAdvG A) Q (isWeightBound_romAdvG hA) ∅
  refine ⟨A', hA', ?_⟩
  rw [(detRun_evalDistEq A V).prEvent_eq, gameG]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ advRG A)
    (fun _ z ↦ postG V z) (fun _ z ↦ duplex_postG V hV z) (Q + QV) (isWeightBound_gameG hA hVw) E
  exact h1.trans (add_le_add ((romGameG_le A V E).trans hle) le_rfl)

/-- The random-oracle experiment of `romStep` is `romExperiment`'s, without the final cache. -/
theorem romStep_eq (A : OracleComp KeccakCalls α) (V : α → OracleComp KeccakCalls Bool) :
    (simulateQ KeccakCalls.randomOracle A).run ∅ >>= romStep V =
      (fun w ↦ w.1) <$> LeanVM.Protocol.Rom.romExperiment A V := by
  rw [LeanVM.Protocol.Rom.romExperiment_eq, map_bind]
  refine bind_congr fun p ↦ ?_
  simp only [romStep, Functor.map_map]

end LeanVM.Rpm
