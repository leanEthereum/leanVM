/-
  LeanVM.Protocol.LeanVMRpmAS

  Knowledge soundness of the leanVM verifier in the random-permutation model, for the
  agreement-set extractor, from its random-oracle bound: the end statement `KnowledgeSoundness`
  of `Statement/LeanVm.lean`, for `Relation.transcriptExtractor`.
-/

module

public import LeanVM.Protocol.Rom.Statement
public import LeanVM.Protocol.Rpm.VerifierCost
public import LeanVM.Protocol.Rpm.ExtractF
public import LeanVM.Protocol.Rpm.Coins
public import LeanVM.Protocol.ExperimentBridge
public import LeanVM.Protocol.Errors
public import LeanVM.Protocol.Relation.Avail
import LeanVM.Protocol.Rpm.Extract
import LeanVM.Protocol.Rpm.RomRelabel
import LeanVM.Protocol.Rpm.RpmRelabel
import Common.Linear
import Common.Prob

@[expose] public section

/-!
# leanVM in the random-permutation model, for the agreement-set extractor

`Relation.transcriptExtractor` (`Relation/ExtractorDef.lean`): the agreement-set extractor
(`Relation.extractAS`) on the Keccak-256 evaluations of the adversary's transcript and the answers
of its first forward queries (`Rpm.firstForward`). `knowledgeSoundness_of_rom`: if the
random-oracle extractor `extractorAS` (`Rom/Statement.lean`) has error `soundnessErrorAS`
(`KnowledgeSoundnessRom`), the transcript's satisfies the end statement `KnowledgeSoundness`.

The transfer is the bus era's (`LeanVMRpmAS.lean`, `LeanVMRpm.lean` at tag
`formal-bus-archive`), unchanged but for the extractor and the query counts: coins do not help
(`rpmExperiment_le_det`); a deterministic adversary's experiment is the real world of a transfer
game (`detExperiment_evalDistEq`), whose verifier follows the duplex discipline (`duplex_postR`)
in at most `Q + verifierPermCalls` permutation calls (`isWeightBound_game`);
`Common.keccak256_transfer2` moves the event to the random-oracle game, at a cost of
`rpmError (Q + verifierPermCalls)`. There the transcript's evaluations are the cache's hash
answers (`Rpm.transcriptHashes_eq_of_mem_support`) and its first forward answers extend the
cache's `F` answers (`Rpm.cacheF_firstForward`); the extractor is monotone in its permutation
answers (`Relation.extractAS_mono`), so wherever the random-oracle extractor returns an
execution, the transcript's returns it too (`Rpm.romGame_leAS`). The error fits the end
statement's bound for `Q ≤ 2^128` (`soundnessRpmAS_le_statement`), and past it the bound
exceeds one.
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open scoped ENNReal

/-- The adversary breaks soundness for the agreement-set extractor, in the experiment with the two
calls. -/
def BreaksASWithHash (z : ExperimentOutcomeWithHash) : Prop :=
  z.accepted ∧ ¬ ∃ t, Relation.transcriptExtractorWithHash z.program z.input z.transcript z.proof =
    some t ∧ ValidExecution z.program z.input t

namespace Rpm

/-- The random-oracle experiment (`Rom/Statement.lean`) against an adversary that also has
private coins. -/
noncomputable def experimentCoins (B : OracleComp (unifSpec + KeccakCalls) (ProgramAndInput × Proof)) :
    ProbComp Outcome := do
  let (z, adversaryCache) ← (simulateQ KeccakCalls.romImpl B).run ∅
  let (verdict, cache) ← (simulateQ KeccakCalls.randomOracle
    (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run adversaryCache
  return ((z, verdict), cache, adversaryCache)

/-- The verifier's phase of the random-oracle experiment, from the adversary's statement and proof
and the oracles' cache. -/
noncomputable def verifierPhase (z : ProgramAndInput × Proof) (cA : KeccakCalls.QueryCache) :
    ProbComp Outcome :=
  (fun r ↦ ((z, r.1), r.2, cA)) <$> (simulateQ KeccakCalls.randomOracle
    (verifierWithHash callKeccak256 callKeccakF1600 z.1.1 z.1.2 z.2)).run cA

theorem experimentCoins_eq (B : OracleComp CSpec (ProgramAndInput × Proof)) :
    experimentCoins B =
      (simulateQ KeccakCalls.romImpl B).run ∅ >>= fun p ↦ verifierPhase p.1 p.2 := by
  simp only [experimentCoins, verifierPhase, bind_pure_comp]

/-- Coins do not help against the extractor in the random-oracle model. -/
theorem knowledgeSoundnessAS_coins {ε : ℕ → ℝ≥0∞} (hrom : KnowledgeSoundnessRom extractorAS ε)
    {B : OracleComp (unifSpec + KeccakCalls) (ProgramAndInput × Proof)} {Q : ℕ}
    (hB : Common.QueryCostAtMost B hashCalls Q) :
    Pr{let z ← experimentCoins B}[Breaks extractorAS z] ≤ ε Q := by
  obtain ⟨A, hA, hle⟩ := exists_det (fun p ↦ do
      let (verdict, cache) ← (simulateQ KeccakCalls.randomOracle
        (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1 p.1.1.2 p.1.2)).run p.2
      return ((p.1, verdict), cache, p.2)) (Breaks extractorAS) B Q hB ∅
  exact hle.trans (hrom A Q hA)

/-- **The random-oracle game of the transfer is bounded by the random-oracle experiment** of the
transfer's adversary: the transcript's evaluations are the cache's hash answers, and its first
forward answers extend the cache's `F` answers, so wherever the random-oracle extractor returns a
valid execution, the transcript's returns it. -/
theorem romGame_leAS (A : DetAdversary) :
    Pr{let a ← Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
        Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
          (fun _ z ↦ postR z) x a)}[BreaksASWithHash a] ≤
      Pr{let z ← experimentCoins (romAdv A)}[Breaks extractorAS z] := by
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
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun p hp ↦ ?_
  have ht := transcriptHashes_eq_of_mem_support A hp
  have hf := cacheF_firstForward A hp
  rw [postR, simulateQ_map, StateT.run'_eq, StateT.run_map, prEvent_map, prEvent_map,
    verifierPhase, prEvent_map]
  have h := (run'_toRHF (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1.1 p.1.1.1.2
    p.1.1.2) p.2).prEvent_eq (fun v ↦ BreaksASWithHash ((p.1.1, v), p.1.2))
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map] at h
  refine h.le.trans (prEvent_mono _ _ _ fun r hr ↦ ?_)
  refine ⟨hr.1, fun ⟨t, hte, htv⟩ ↦ hr.2 ⟨t, ?_, htv⟩⟩
  have hH : lookupEvaluation (keccakEvaluationsOfTranscript p.1.2) =
      fun x ↦ cmap p.2 (.inl x) := by
    rw [ht]
    funext m
    rw [cmap_inl]
  unfold Relation.transcriptExtractorWithHash
  have hc : Extraction.MerkleProofs.KeysCover (lookupEvaluation (keccakEvaluationsOfTranscript p.1.2))
      ((keccakEvaluationsOfTranscript p.1.2).map (·.1)) :=
    Relation.keysCover_hashesOf _
  rw [Relation.extractAS_keys_congr _ _ hc
    (Relation.keysCover_supportKeys (Relation.finite_of_keysCover hc)), hH]
  exact Relation.extractAS_mono hte fun s y hs ↦ hf s y hs

/-- **Knowledge soundness in the random-permutation model, from the random-oracle model**, for a
deterministic adversary of at most `Q` queries to `π` and `π⁻¹`. -/
theorem knowledgeSoundnessRpmAS {ε : ℕ → ℝ≥0∞} (hrom : KnowledgeSoundnessRom extractorAS ε)
    {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← detExperiment A}[BreaksASWithHash z] ≤ ε Q + rpmError (Q + verifierPermCalls) := by
  rw [(detExperiment_evalDistEq A).prEvent_eq, game]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)
    (fun _ z ↦ duplex_postR z) (Q + verifierPermCalls) (isWeightBound_game hA) BreaksASWithHash
  refine h1.trans (add_le_add ((romGame_leAS A).trans ?_) le_rfl)
  exact knowledgeSoundnessAS_coins hrom (isWeightBound_romAdv hA)

/-- The same, for an adversary with coins. -/
theorem knowledgeSoundnessRpmAS_coins {ε : ℕ → ℝ≥0∞} (hrom : KnowledgeSoundnessRom extractorAS ε)
    {B : RandomPermutationAdversary} {Q : ℕ}
    (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) :
    Pr{let z ← soundnessExperimentWithHash B}[BreaksASWithHash z] ≤
      ε Q + rpmError (Q + verifierPermCalls) := by
  obtain ⟨A, hA, hle⟩ := rpmExperiment_le_det hB BreaksASWithHash
  exact hle.trans (knowledgeSoundnessRpmAS hrom hA)

end Rpm

/-! ## The numbers -/

theorem romRootCap_le : romRootCap ≤ 2 ^ 16 := by decide

/-- **The agreement-set extractor's error fits the end statement's bound**: for `Q ≤ 2^128`
queries, with the transfer to the random-permutation model, at most
`(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`. The fresh hit `2^-127`, the fresh roots
`V · romRootCap · 2^-256` and the transfer's error are each at most `2^-125`, and
`V + 3 ≤ 2^14` (`leanVmQueryBound_add_three_le`). -/
theorem soundnessRpmAS_le_statement {Q : ℕ} (hQ : Q ≤ 2 ^ 128) :
    soundnessErrorAS Q + rpmError (Q + Rpm.verifierPermCalls) ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hA3 : ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) + 3 ≤ (Q + 2 ^ 14 : ℝ≥0∞) := by
    have h : Q + leanVmQueryBound + 3 ≤ Q + 2 ^ 14 := by
      have := leanVmQueryBound_add_three_le
      omega
    exact_mod_cast h
  have hHit : (2 : ℝ≥0∞)⁻¹ ^ 127 ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.inv_two_pow_le_of_le (by norm_num)
  have hRoots : (leanVmQueryBound : ℝ≥0∞) * (romRootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 125 := by
    have hn : leanVmQueryBound * romRootCap ≤ 2 ^ 131 := by
      have := romRootCap_le
      rw [leanVmQueryBound_eq]
      calc 12672 * romRootCap ≤ 12672 * 2 ^ 16 := Nat.mul_le_mul_left _ this
        _ ≤ 2 ^ 131 := by norm_num
    calc (leanVmQueryBound : ℝ≥0∞) * (romRootCap * (2 ^ 256 : ℝ≥0∞)⁻¹)
        = ((leanVmQueryBound * romRootCap : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
          rw [Nat.cast_mul, mul_assoc, ENNReal.inv_pow]
      _ ≤ (2 : ℝ≥0∞) ^ 131 * (2 : ℝ≥0∞)⁻¹ ^ (131 + 125) := by
          gcongr
          exact_mod_cast hn
      _ = (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.two_pow_mul_inv_pow 131 125
  have hP : Rpm.verifierPermCalls ≤ 2 ^ 128 :=
    calc Rpm.verifierPermCalls = leanVmQueryBound * 2 ^ 30 := rfl
      _ ≤ 2 ^ 14 * 2 ^ 30 :=
        Nat.mul_le_mul_right _ ((Nat.le_add_right _ 3).trans leanVmQueryBound_add_three_le)
      _ = 2 ^ 44 := by rw [← pow_add]
      _ ≤ 2 ^ 128 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have hq : Q + Rpm.verifierPermCalls ≤ 2 ^ 129 :=
    calc Q + Rpm.verifierPermCalls ≤ 2 ^ 128 + 2 ^ 128 := Nat.add_le_add hQ hP
      _ = 2 ^ 129 := by norm_num
  have hR : rpmError (Q + Rpm.verifierPermCalls) ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 :=
    calc rpmError (Q + Rpm.verifierPermCalls)
        ≤ ((Q + Rpm.verifierPermCalls : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 379 :=
          Common.sq_div_le_mul_inv_pow (k := 129) 379 hq
      _ ≤ (2 : ℝ≥0∞) ^ 129 * (2 : ℝ≥0∞)⁻¹ ^ (129 + 250) := by
          gcongr
          exact_mod_cast hq
      _ = (2 : ℝ≥0∞)⁻¹ ^ 250 := Common.two_pow_mul_inv_pow 129 250
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 125 := Common.inv_two_pow_le_of_le (by norm_num)
  have h5 : ((5 * (Q + leanVmQueryBound) : ℕ) : ℝ≥0∞) / 2 ^ 256 =
      5 * ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
    rw [Nat.cast_mul, div_eq_mul_inv, ENNReal.inv_pow, Nat.cast_ofNat]
  unfold soundnessErrorAS
  rw [h5]
  calc ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 256) +
        (2 : ℝ≥0∞)⁻¹ ^ 127 + (leanVmQueryBound : ℝ≥0∞) * (romRootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) +
        rpmError (Q + Rpm.verifierPermCalls)
      = ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((2 : ℝ≥0∞)⁻¹ ^ 127 + (leanVmQueryBound : ℝ≥0∞) * (romRootCap * (2 ^ 256 : ℝ≥0∞)⁻¹) +
            rpmError (Q + Rpm.verifierPermCalls)) := by ring
    _ ≤ ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 +
          ((2 : ℝ≥0∞)⁻¹ ^ 125 + (2 : ℝ≥0∞)⁻¹ ^ 125 + (2 : ℝ≥0∞)⁻¹ ^ 125) :=
        add_le_add le_rfl (add_le_add (add_le_add hHit hRoots) hR)
    _ = (((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) + 3) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by ring
    _ ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
          5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
        have hA : ((Q + leanVmQueryBound : ℕ) : ℝ≥0∞) ≤ (Q + 2 ^ 14 : ℝ≥0∞) := le_self_add.trans hA3
        gcongr

/-- Past `2^128` queries the end statement's bound exceeds one. -/
theorem one_le_statement {Q : ℕ} (hQ : ¬ Q ≤ 2 ^ 128) :
    1 ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256 := by
  have hQ' : (2 : ℝ≥0∞) ^ 125 ≤ (Q : ℝ≥0∞) := by
    have : 2 ^ 125 ≤ Q :=
      ((Nat.pow_le_pow_right (by norm_num) (by norm_num : 125 ≤ 128)).trans
        (Nat.le_of_lt (not_le.mp hQ)))
    exact_mod_cast this
  calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 125 * (2 : ℝ≥0∞)⁻¹ ^ 125 := by
        rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    _ ≤ (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 := by
        gcongr
        exact hQ'.trans le_self_add
    _ ≤ _ := le_self_add

/-- **Knowledge soundness in the random-permutation model, from the random-oracle model**: if
the agreement-set extractor on the adversary's cache has error `soundnessErrorAS`, the same
extractor on the adversary's transcript (`Relation.transcriptExtractor`) satisfies the end
statement. -/
theorem knowledgeSoundness_of_rom (hrom : KnowledgeSoundnessRom extractorAS soundnessErrorAS) :
    KnowledgeSoundness Relation.transcriptExtractor := by
  intro A Q hQ
  by_cases hcap : Q ≤ 2 ^ 128
  · have := (Rpm.knowledgeSoundnessRpmAS_coins hrom hQ).trans (soundnessRpmAS_le_statement hcap)
    rw [← map_soundnessExperiment, prEvent_map] at this
    exact this
  · exact (prEvent_le_one _).trans (one_le_statement hcap)

end LeanVM

end
