/-
  LeanVM.Protocol.LeanVMRpm

  The proofs of the two statements of `Statement/LeanVm.lean`, `LeanVM.KnowledgeSoundness` and
  `LeanVM.Completeness`: knowledge soundness and completeness of the leanVM verifier in the
  random-permutation model, from the two-oracle random-oracle model.
-/

import LeanVM.Protocol.LeanVM
import LeanVM.Protocol.ErrorBounds
import Common.Linear
import LeanVM.Protocol.Rpm.Cost
import LeanVM.Protocol.Rpm.Duplex
import LeanVM.Protocol.Rpm.Extract
import LeanVM.Protocol.Extraction.Extract
import LeanVM.Protocol.Rpm.RomRelabel
import LeanVM.Protocol.Rpm.RpmRelabel
import LeanVM.Protocol.WithHash
import LeanVM.Protocol.ExperimentBridge

/-!
# leanVM in the random-permutation model

The statements are in `Statement/LeanVm.lean`: Keccak-256 the sponge over one uniformly random
permutation `π` of the Keccak state, Keccak-f[1600] `π` itself, the adversary querying `π` and
`π⁻¹` and flipping coins.

**Knowledge soundness** (`knowledgeSoundnessRpm_coins`): for an adversary of at most `Q` queries
to `π` and `π⁻¹`, its coins free, the probability that the verifier accepts while the extractor `transcriptExtractor` (the extractor of
`Extractor.lean` on the Keccak-256 evaluations of the adversary's transcript) does not return a valid execution is at most
`soundnessError Q + (Q + 13261 · 2^32)² / 2^508`, which is at most `(Q + 2^14) · 2^-124` for
`Q ≤ 2^120` (`soundnessRpm_le_bits`), at most `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256` for
`Q ≤ 2^128` (`soundnessRpm_le_statement`, the end statement `KnowledgeSoundness`) and at most
`2^-60` for `Q ≤ 2^64` (`soundnessRpm_le`), all in `LeanVM.Protocol.ErrorBounds`. The proof:

0. the adversary's coins do not help (`rpmExperiment_le_det`, `Coins.lean`): the experiment is
   bounded by that of a deterministic adversary of as many queries (`knowledgeSoundnessRpm_coins`);
1. that adversary's experiment is `common`'s real world of a transfer game
   (`detExperiment_evalDistEq`, `RpmRelabel.lean`): the adversary, recording its transcript, then
   the verifier;
2. the verifier's permutation calls follow the duplex discipline (`duplex_postR`, from
   `Duplex.lean`), and the game makes at most `Q + verifierPermCalls` permutation calls
   (`isWeightBound_game`, from `Cost.lean`);
3. `Common.keccak256_transfer2` moves the event to the two-oracle random-oracle model, against
   the adversary with the indifferentiability simulator, at a cost of `q² / 2^508`, which is where
   the random-permutation model meets the random-oracle model;
4. there, the adversary's cached Keccak-256 answers are exactly the evaluations of its transcript
   (`transcriptHashes_eq_of_mem_support`, `Extract.lean`), so the event is the event of
   `KnowledgeSoundnessRom` (`LeanVM/Protocol/Rom/Statement.lean`) against the random-oracle
   adversary `romAdv` (`romGame_le`), which makes at
   most `Q` oracle queries (`isWeightBound_romAdv`) and flips coins;
5. coins do not help (`knowledgeSoundness_coins`, `Coins.lean`), and
   `knowledgeSoundnessRom_holds` bounds the rest by `soundnessError Q`.

**Completeness** (`completenessRpm`): the same game with no adversary and, after it, the honest
prover of `CompletenessRom` followed by the verifier, both following the duplex discipline
(`duplexVm_honest`), of at most `completenessPermCalls fuel` permutation calls
(`isWeightBound_honest`): the rejection probability is at most
`completenessError fuel + completenessPermCalls fuel² / 2^508`, below `2^-256` at a fuel of `2^33`
(`completenessRpm_le`).

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` (`LeanVM.lean`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-! ## The duplex discipline on bytes -/

/-- An admissible permutation call on lanes is admissible on bytes. -/
theorem admissible_toRpm {hist : List KeccakState} {x : KeccakState} (h : AdmissibleVm hist x) :
    Common.Admissible Common.KState.zero Common.keccakNF (hist.map KState.toRpm)
      (KState.toRpm x) := by
  rcases h with h | ⟨y, hy, h⟩
  · left
    have hk := keccakNF_of_keep x (Vector.replicate 25 0) fun i hi ↦ by simp [h i hi]
    rw [toRpm_zero] at hk
    exact hk
  · right
    exact ⟨KState.toRpm y, List.mem_map_of_mem hy, keccakNF_of_keep x y h⟩

/-- **The discipline on lanes is the discipline on bytes**: a computation over the calls of
`Statement.lean` (`HashSpec`) whose permutation calls follow the duplex discipline on lanes, read
on bytes, follows `common`'s duplex discipline (`Common.Duplex`, at the zero state, for the
non-final blocks `Common.keccakNF`). -/
theorem duplex_toRHF {β : Type} (V : OracleComp KeccakCalls β) (hist : List KeccakState)
    (hV : DuplexVm V hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (simulateQ toRHF V)
      (hist.map KState.toRpm) := by
  induction V using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [duplexVm_query_bind] at hV
    rcases t with m | x
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      intro d
      exact ih _ hist (hV _)
    · simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self, toRHF,
        bind_map_left]
      refine ⟨admissible_toRpm hV.1, fun y ↦ ?_⟩
      have := ih (KState.ofRpm y) (KState.ofRpm y :: hist) (hV.2 _)
      rw [List.map_cons, toRpm_ofRpm] at this
      exact this

/-- A map keeps the duplex discipline. -/
theorem duplex_map {α β : Type} (f : α → β) (X : OracleComp HFSpec α)
    (hist : List Common.KState)
    (hX : Common.Duplex Common.KState.zero Common.keccakNF X hist) :
    Common.Duplex Common.KState.zero Common.keccakNF (f <$> X) hist := by
  induction X using OracleComp.inductionOn generalizing hist with
  | pure a => trivial
  | query_bind t k ih =>
    rw [map_bind]
    rcases t with n | m | x
    · exact fun u ↦ ih u hist (hX u)
    · exact fun u ↦ ih u hist (hX u)
    · exact ⟨hX.1, fun y ↦ ih y (y :: hist) (hX.2 y)⟩

/-- The verifier on bytes follows the duplex discipline. -/
theorem duplex_postR (z : (ProgramAndInput × Proof) × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postR z) [] :=
  duplex_map _ _ [] (duplex_toRHF _ [] (duplexVm_verifier _ _ _))

/-! ## The permutation calls of the games -/

/-- Weight bounds through a stateless simulation. -/
theorem isWeightBound_simulateQ' {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {α : Type} (impl : QueryImpl spec (OracleComp spec')) (w : ι → ℕ) (w' : ι' → ℕ)
    (h : ∀ t, Common.QueryCostAtMost (impl t) w' (w t)) {X : OracleComp spec α} {n : ℕ}
    (hX : Common.QueryCostAtMost X w n) : Common.QueryCostAtMost (simulateQ impl X) w' n := by
  induction X using OracleComp.inductionOn generalizing n with
  | pure a => trivial
  | query_bind t k ih =>
    rw [Common.isWeightBound_query_bind_iff] at hX
    simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
    exact ((h t).bind fun u ↦ ih u (hX.2 u)).mono (by omega)

/-- The cost of the game's queries (`Common.queryCost2`): a hash of `n` bytes `⌊n / 136⌋ + 1`,
a permutation query or call one. -/
abbrev gameCost : D2Spec.Domain → ℕ := Common.queryCost2 (Dg := Common.DigestBytes) Common.keccakPadding

/-- The cost of the adversary's queries (`Common.queryCost`). -/
abbrev advCost : RSpec.Domain → ℕ :=
  Common.queryCost (Dg := Common.DigestBytes) (St := Common.KState) Common.keccakPadding

/-- The adversary's permutation queries, one each. -/
theorem isWeightBound_advR_cost {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (advR A) advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) _ (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query advCost (.inr (.inr (permQueryToRpm q)))))

theorem isWeightBound_advEmbed {α : Type} {X : OracleComp RSpec α} {n : ℕ}
    (hX : Common.QueryCostAtMost X advCost n) :
    Common.QueryCostAtMost (simulateQ Common.advEmbed X) gameCost n := by
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hX
  rcases t with k | m | q
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inl k)
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
  · exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inl q)))

theorem isWeightBound_hfEmbed_toRHF {β : Type} {V : OracleComp KeccakCalls β} {n : ℕ}
    (hV : Common.QueryCostAtMost V hashBlocks n) :
    Common.QueryCostAtMost (simulateQ Common.hfEmbed (simulateQ toRHF V)) gameCost n := by
  rw [← QueryImpl.simulateQ_compose]
  refine isWeightBound_simulateQ' _ _ _ (fun t ↦ ?_) hV
  rcases t with m | x
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.hQuery, hq_eq, simulateQ_spec_query]
    have := Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inl m))
    rwa [show gameCost (.inr (.inl m)) = hashBlocks (.inl m) from Common.keccakPad_length m]
      at this
  · simp only [QueryImpl.apply_compose, toRHF, simulateQ_map]
    refine Common.isWeightBound_map _ ?_
    simp only [Common.fQuery, hq_eq, simulateQ_spec_query]
    exact Common.isWeightBound_query (spec := D2Spec) gameCost (.inr (.inr (.inr _)))

/-- **The permutation calls of the transfer game**: the adversary's `Q`, then at most
`verifierPermCalls` of the verifier. -/
theorem isWeightBound_game {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (game A) gameCost (Q + verifierPermCalls) := by
  rw [game, Common.rpmGame2, simulateQ_pure, pure_bind]
  refine (isWeightBound_advEmbed (isWeightBound_advR_cost hA)).bind fun z ↦ ?_
  rw [postR, simulateQ_map]
  exact Common.isWeightBound_map _ (isWeightBound_hfEmbed_toRHF (isWeightBound_verifier _ _ _))

/-! ## Knowledge soundness -/

/-- The verifier's phase of the random-oracle experiment, from the adversary's statement and proof
and the oracles' cache. -/
noncomputable def verifierPhase (z : ProgramAndInput × Proof) (cA : KeccakCalls.QueryCache) :
    ProbComp Outcome :=
  (fun r ↦ ((z, r.1), r.2, cA)) <$>
    (simulateQ KeccakCalls.randomOracle (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run cA

theorem experimentCoins_eq (B : OracleComp CSpec (ProgramAndInput × Proof)) :
    experimentCoins B = (simulateQ KeccakCalls.romImpl B).run ∅ >>= fun p ↦ verifierPhase p.1 p.2 := by
  simp only [experimentCoins, verifierPhase, bind_pure_comp]

/- The extractor is an algorithm; unification must never run it on symbolic inputs. -/
attribute [local irreducible] Extraction.extract

/-- **The random-oracle game of the transfer is bounded by the random-oracle experiment of the
transfer's adversary**: the transcript's Keccak-256 evaluations are the adversary's cached hash
answers (`transcriptHashes_eq_of_mem_support`), so the extractor in the random-permutation model
sees what the extractor of the random-oracle model (`LeanVM.extractor`) sees: the extraction depends
on the answers only, not on which byte strings covering them it is given as keys
(`extractorRpm_eq_extract`). -/
theorem romGame_le (A : DetAdversary) :
    Pr{let a ← Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
        Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
          (fun _ z ↦ postR z) x a)}[BreaksKnowledgeSoundnessWithHash a] ≤
      Pr{let z ← experimentCoins (romAdv A)}[Breaks extractor z] := by
  set X := Common.advS2 Common.keccakPadding Common.KState.zero (advR A)
  set J := (simulateQ HFS.romImpl X).run ∅ with hJ
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
        (fun _ z ↦ postR z) x a) =
      J >>= fun p ↦ (simulateQ HFS.romImpl (postR p.1)).run' p.2 := by
    simp only [Common.romRun2, simulateQ_pure, pure_bind, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, hJ, X]
  rw [e1]
  have e2 : experimentCoins (romAdv A) =ᵈ J >>= fun p ↦ verifierPhase p.1.1 (cmap p.2) := by
    rw [experimentCoins_eq, romAdv, simulateQ_map, StateT.run_map]
    have h := run_ofRHF X ∅
    rw [cmap_empty] at h
    rw [bind_map_left]
    refine (EvalDistEq.bind_left h _).trans ?_
    rw [bind_map_left]
    exact EvalDistEq.rfl
  rw [e2.prEvent_eq]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ le_of_eq ?_
  have ht := transcriptHashes_eq_of_mem_support A hp
  rw [postR, simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_map, prEvent_map,
    verifierPhase, prEvent_map]
  have h := (run'_toRHF (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1.1 p.1.1.1.2 p.1.1.2) p.2).prEvent_eq
    (fun v ↦ BreaksKnowledgeSoundnessWithHash ((p.1.1, v), p.1.2))
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map] at h
  refine h.trans ?_
  congr 2
  funext r
  have e := fun prog input proof ↦
    Extraction.ExtractProofs.extractorRpm_eq_extract prog input p.1.2 proof ht
  simp only [BreaksKnowledgeSoundnessWithHash, Breaks, extractor, e]
  rfl

/-- **Knowledge soundness in the random-permutation model**, for a deterministic adversary. An
adversary of at most `Q` queries to `π` and `π⁻¹` breaks soundness, for the extractor
`transcriptExtractor`, with probability at most the random-oracle error at `Q` queries plus
`(Q + verifierPermCalls)² / 2^508`. -/
theorem knowledgeSoundnessRpm {A : DetAdversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← detExperiment A}[BreaksKnowledgeSoundnessWithHash z] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls) := by
  rw [(detExperiment_evalDistEq A).prEvent_eq, game]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)
    (fun _ z ↦ duplex_postR z) (Q + verifierPermCalls) (isWeightBound_game hA)
    (BreaksKnowledgeSoundnessWithHash)
  refine h1.trans (add_le_add ((romGame_le A).trans ?_) le_rfl)
  exact knowledgeSoundness_coins (isWeightBound_romAdv hA)

/-- **Knowledge soundness in the random-permutation model**, for an adversary with coins of at
most `Q` queries to `π` and `π⁻¹`: some deterministic adversary of at most `Q` queries does as
well (`rpmExperiment_le_det`). -/
theorem knowledgeSoundnessRpm_coins
    {B : RandomPermutationAdversary} {Q : ℕ}
    (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) :
    Pr{let z ← soundnessExperimentWithHash B}[BreaksKnowledgeSoundnessWithHash z] ≤
      soundnessError Q + rpmError (Q + verifierPermCalls) := by
  obtain ⟨A, hA, hle⟩ := rpmExperiment_le_det hB (BreaksKnowledgeSoundnessWithHash)
  exact hle.trans (knowledgeSoundnessRpm hA)

/-! ## Completeness -/

open LeanVM.Protocol.Rom (romExperiment)

/-- The verdict of a prover then a verifier against the random oracles is the random-oracle
experiment's. -/
theorem run'_bind_eq (X : OracleComp KeccakCalls Proof) (V : Proof → OracleComp KeccakCalls Bool) :
    (simulateQ KeccakCalls.randomOracle (X >>= V)).run' ∅ = (fun z ↦ z.1.2) <$> romExperiment X V := by
  simp only [romExperiment, simulateQ_map, StateT.run_map, map_bind, simulateQ_bind,
    StateT.run'_eq, StateT.run_bind]
  refine bind_congr fun p ↦ ?_
  simp

/-- **From the random-oracle model to the random-permutation model**, for a prover then a
verifier: if they follow the duplex discipline and make at most `N` permutation calls, the
rejection probability in the random-permutation model is at most the random-oracle experiment's
plus `rpmError N` (`Common.keccak256_transfer2`). -/
theorem rpm_le_of_rom (X : OracleComp KeccakCalls Proof) (V : Proof → OracleComp KeccakCalls Bool)
    {N : ℕ} (hd : DuplexVm (X >>= V) []) (hN : Common.QueryCostAtMost (X >>= V) hashBlocks N)
    {ε : ℝ≥0∞} (hrom : Pr{let z ← romExperiment X V}[z.1.2 = false] ≤ ε) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation (X >>= V)).run' []}[v = false] ≤ ε + rpmError N := by
  have hG : Common.QueryCostAtMost (honestGame (X >>= V)) gameCost N := by
    rw [honestGame, Common.rpmGame2, simulateQ_pure, pure_bind, simulateQ_pure, pure_bind]
    exact isWeightBound_hfEmbed_toRHF hN
  rw [(rpmHonest_evalDistEq _).prEvent_eq, honestGame]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ (pure () : OracleComp RSpec Unit))
    (fun _ _ ↦ simulateQ toRHF (X >>= V)) (fun _ _ ↦ duplex_toRHF _ [] hd) N hG (· = false)
  refine h1.trans (add_le_add (le_of_eq_of_le ?_ hrom) le_rfl)
  have e1 : Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
      Common.advS2 Common.keccakPadding Common.KState.zero
        ((fun _ ↦ (pure () : OracleComp RSpec Unit)) x) >>= fun a ↦
          (fun _ _ ↦ simulateQ toRHF (X >>= V)) x a) =
      (simulateQ HFS.romImpl (simulateQ toRHF (X >>= V))).run' ∅ := by
    simp [Common.romRun2, Common.advS2]
  rw [e1, (run'_toRHF _ _).prEvent_eq, cmap_empty, run'_bind_eq, prEvent_map]

/-- **Completeness in the random-permutation model, at a witness**: the specification's honest
prover at an honest witness `w` at the sizes `s` (`HonestFor`), then the verifier, at a fuel of at
most `2^64` nonces. -/
theorem completenessRpm_at {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    {ρ : ℕ}
    {w : Air.Flat.EnsembleWitness (Arithmetization.leanIsaEnsemble prog t.logMemorySize)} {s : LeanIsa.Sizes}
    (hw : EndToEnd.Complete.HonestFor prog input t ρ w s) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← (simulateQ keccakCallsOverRandomPermutation
        (Rom.honestComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
          (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
          (EndToEnd.Complete.leanVmProver prog s ρ (LeanIsa.stackOf prog s w)) fuel >>= fun proof ↦
            verifierWithHash callKeccak256 callKeccakF1600 prog input proof)).run' []}[v = false] ≤
      completenessError fuel + rpmError (completenessPermCalls fuel) := by
  refine rpm_le_of_rom _ _ ((duplexVm_romHonestComp prog input _ fuel).bind fun proof ↦
    duplexVm_verifier prog input proof) (isWeightBound_romHonest hw fuel) ?_
  have hV : verifierWithHash callKeccak256 callKeccakF1600 prog input =
      LeanVM.Protocol.Compile.Rom.verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  rw [hV, completenessError_eq]
  exact EndToEnd.Complete.romComplete_at hw hfuel

/-- **Completeness in the random-permutation model**, for the honest prover
`LeanVM.Protocol.EndToEnd.Complete.honestComp`. -/
theorem completenessRpm {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}
    (hv : ValidExecution prog input t) (hbudget : t.committedSize ≤ 2 ^ 28) {ρ : ℕ}
    (hρ : 1 ≤ ρ ∧ ρ ≤ 4) {fuel : ℕ} (hfuel : fuel ≤ 2 ^ 64) :
    Pr{let v ← verifierCompletenessExperimentWithHash
        (fun prog input t ρ fuel ↦ some <$> EndToEnd.Complete.honestComp prog input t ρ fuel)
        prog input t ρ fuel}[v = false] ≤
      completenessError fuel + rpmError (completenessPermCalls fuel) := by
  obtain ⟨w, s, hw, hrep, hs, hadm⟩ := EndToEnd.Complete.exists_admissible_witness hv hbudget
  have hex : ∃ w s, EndToEnd.Complete.HonestFor prog input t ρ w s := ⟨w, s, hρ, hw, hs, hadm, hrep⟩
  have e0 : verifierCompletenessExperimentWithHash
      (fun prog input t ρ fuel ↦ some <$> EndToEnd.Complete.honestComp prog input t ρ fuel)
      prog input t ρ fuel = (simulateQ keccakCallsOverRandomPermutation
        (EndToEnd.Complete.honestComp prog input t ρ fuel >>= fun proof ↦
          verifierWithHash callKeccak256 callKeccakF1600 prog input proof)).run' [] := by
    simp only [verifierCompletenessExperimentWithHash, bind_map_left]
  rw [e0]
  unfold EndToEnd.Complete.honestComp
  simp only [hex, ↓reduceDIte]
  exact completenessRpm_at hex.choose_spec.choose_spec hfuel

/-! ## The numbers -/

/-- **The completeness bound in the random-permutation model**: at a fuel of `2^33` nonces per
proof of work, at most `2^-256`: the random-oracle error and the transfer's are each below
`2^-257`. -/
theorem completenessRpm_le :
    completenessError (2 ^ 33) + rpmError (completenessPermCalls (2 ^ 33)) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  calc completenessError (2 ^ 33) + rpmError (completenessPermCalls (2 ^ 33))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ 257 + (2 : ℝ≥0∞)⁻¹ ^ 257 :=
        add_le_add completenessError_le rpmError_completenessPermCalls_le
    _ = (2 : ℝ≥0∞)⁻¹ ^ 256 := by
        rw [← two_mul, pow_succ, ← mul_assoc, mul_comm 2, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

end LeanVM.Rpm

namespace LeanVM

/-! ## The statements of `Statement/LeanVm.lean` -/

/-- Knowledge soundness in the experiment with the two calls, for the extractor
`transcriptExtractorWithHash`. -/
theorem knowledgeSoundnessWithHash_holds :
    KnowledgeSoundnessWithHash :=
  fun _ _ hA hQ ↦ (Rpm.knowledgeSoundnessRpm_coins hA).trans (soundnessRpm_le_statement hQ)

/-- **Knowledge soundness holds** (in the random-permutation model), for the extractor
`transcriptExtractor`: the statement's experiment, its transcript's coins left out, is the one
with the two calls (`map_soundnessExperiment`). -/
theorem knowledgeSoundness_holds : KnowledgeSoundness transcriptExtractor :=
  knowledgeSoundness_of_withHash knowledgeSoundnessWithHash_holds

-- `LeanVM.completeness_holds`, for the statement's prover `LeanVM.leanVmHonestProver`, is proved in
-- `LeanVM/Prover/End.lean` from `completeness_of_spec` (`LeanVM/Prover/Complete.lean`).

/-- Keccak-256 over the deployed Keccak-f[1600] is the deployed Keccak-256, and `common`'s
Keccak-256 sponge over it, read on bytes. -/
theorem keccak256_eq_rpm (data : Protocol.Compile.Bytes) :
    Protocol.KeccakHash.keccak256With (m := Id) Semantics.keccakF1600 data = Protocol.KeccakHash.keccak256 data ∧
      Protocol.KeccakHash.keccak256 data = Digest.ofRpm (Common.keccak256With (m := Id)
        (fun x ↦ KState.toRpm (Semantics.keccakF1600 (Rpm.KState.ofRpm x))) data) :=
  ⟨Rpm.keccak256With_keccakF data, Rpm.keccak256_eq_rpm data⟩

end LeanVM
