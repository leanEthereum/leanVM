/-
  LeanVM.Protocol.LeanVMRpmAS

  Knowledge soundness of the leanVM verifier in the random-permutation model, for the
  agreement-set extractor over any near-tuple decoder: the end statement `KnowledgeSoundness` of
  `Statement/LeanVm.lean`, for that extractor.
-/

module

public import LeanVM.Protocol.LeanVMRpm
public import LeanVM.Protocol.LeanVMSoundAS
public import LeanVM.Protocol.Rpm.ExtractF

@[expose] public section

/-!
# leanVM in the random-permutation model, for the agreement-set extractor

`transcriptExtractorAS D`: the agreement-set extractor (`Sound.extractAS`, over the near-tuple
decoder `D`) on the Keccak-256 evaluations of the adversary's transcript and the answers of its
first forward queries (`Rpm.firstForward`). `knowledgeSoundnessAS_holds`: it satisfies the end
statement `KnowledgeSoundness`, with its bound unchanged.

The proof uses the transfer of `LeanVM.Protocol.LeanVMRpm`. The transcript's evaluations are the cache's hash answers (`Rpm.transcriptHashes_eq_of_mem_support`)
and its first forward answers extend the cache's `F` answers (`Rpm.cacheF_firstForward`); the
extractor is monotone in its permutation answers (`Sound.extractAS_mono`), so wherever the
random-oracle extractor returns an execution, the transcript's returns it too (`Rpm.romGame_leAS`).
Then `knowledgeSoundnessRomAS` and the transfer, within the statement's bound
(`soundnessRpmAS_le_statement`).
-/

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.Compile.Rom (replayU_mono)
open OracleComp OracleSpec
open scoped ENNReal

/-- **The agreement-set extractor is monotone in its permutation answers**: answers that extend
the ones it returned an execution on give the same execution. -/
theorem Protocol.EndToEnd.Sound.extractAS_mono (D : NearDecoder) {prog : LeanIsaProgram}
    {input : PublicInput} {H : Bytes → Option Digest} {keys : List Bytes}
    {F F' : KeccakState → Option KeccakState}
    {π : Proof} {t : Execution prog}
    (h : Protocol.EndToEnd.Sound.extractAS D prog input H keys F π = some t)
    (hF : ∀ x y, F x = some y → F' x = some y) :
    Protocol.EndToEnd.Sound.extractAS D prog input H keys F' π = some t := by
  unfold Protocol.EndToEnd.Sound.extractAS at h ⊢
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
  have hseed' : (leanVmSeed (bytecodeWords prog) (EndToEnd.Complete.publicInputDigest input)).run
      H F' = some seed := by
    rw [Protocol.EndToEnd.Sound.leanVmSeed_run_option] at hseed ⊢
    obtain ⟨d, hd, ht⟩ := Option.bind_eq_some_iff.mp hseed
    rw [hd, Option.bind_some]
    exact hF _ _ ht
  rw [hseed', Option.bind_some, replayU_mono hr hF, Option.bind_some]
  exact h

/-- **The agreement-set extractor on a transcript of permutation queries**: on its Keccak-256
evaluations and the answers of its first forward queries. -/
noncomputable def transcriptExtractorASWithHash (D : NearDecoder) (prog : LeanIsaProgram)
    (input : PublicInput) (T : PermutationTranscript) (proof : Proof) : Option (Execution prog) :=
  Protocol.EndToEnd.Sound.extractAS D prog input (lookupEvaluation (keccakEvaluationsOfTranscript T))
    ((keccakEvaluationsOfTranscript T).map (·.1)) (Rpm.firstForward T) proof

/-- **The agreement-set extractor in the random-permutation model**, on the adversary's
transcript, its coins left out. -/
noncomputable def transcriptExtractorAS (D : NearDecoder) : StraightLineExtractor :=
  fun prog input T proof ↦ transcriptExtractorASWithHash D prog input (permutationQueries T) proof

/-- The adversary breaks soundness for the agreement-set extractor, in the experiment with the two
calls. -/
def BreaksASWithHash (D : NearDecoder) (z : ExperimentOutcomeWithHash) : Prop :=
  z.accepted ∧ ¬ ∃ t, transcriptExtractorASWithHash D z.program z.input z.transcript z.proof = some t ∧
    ValidExecution z.program z.input t

namespace Rpm

/-- Coins do not help against the agreement-set extractor in the random-oracle model. -/
theorem knowledgeSoundnessAS_coins (D : NearDecoder)
    {B : OracleComp (unifSpec + KeccakCalls) (ProgramAndInput × Proof)} {Q : ℕ}
    (hB : Common.QueryCostAtMost B hashCalls Q) :
    Pr{let z ← experimentCoins B}[Breaks (extractorAS D) z] ≤ soundnessErrorAS Q := by
  obtain ⟨A, hA, hle⟩ := exists_det (fun p ↦ do
      let (verdict, cache) ←
        (simulateQ KeccakCalls.randomOracle (verifierWithHash callKeccak256 callKeccakF1600 p.1.1.1 p.1.1.2 p.1.2)).run p.2
      return ((p.1, verdict), cache, p.2)) (Breaks (extractorAS D)) B Q hB ∅
  exact hle.trans (knowledgeSoundnessRomAS D hA)

/-- **The random-oracle game of the transfer is bounded by the random-oracle experiment** of the
transfer's adversary, for the agreement-set extractor: the transcript's evaluations are the
cache's hash answers, and its first forward answers extend the cache's `F` answers, so wherever
the random-oracle extractor returns a valid execution, the transcript's returns it. -/
theorem romGame_leAS (D : NearDecoder) (A : DetAdversary) :
    Pr{let a ← Common.romRun2 (simulateQ Common.hInF (pure ()) >>= fun x ↦
        Common.advS2 Common.keccakPadding Common.KState.zero ((fun _ ↦ advR A) x) >>= fun a ↦
          (fun _ z ↦ postR z) x a)}[BreaksASWithHash D a] ≤
      Pr{let z ← experimentCoins (romAdv A)}[Breaks (extractorAS D) z] := by
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
    p.1.1.2) p.2).prEvent_eq (fun v ↦ BreaksASWithHash D ((p.1.1, v), p.1.2))
  rw [StateT.run'_eq, StateT.run'_eq, prEvent_map, prEvent_map] at h
  refine h.le.trans (prEvent_mono _ _ _ fun r hr ↦ ?_)
  refine ⟨hr.1, fun ⟨t, hte, htv⟩ ↦ hr.2 ⟨t, ?_, htv⟩⟩
  have hH : lookupEvaluation (keccakEvaluationsOfTranscript p.1.2) =
      fun x ↦ cmap p.2 (.inl x) := by
    rw [ht]
    funext m
    rw [cmap_inl]
  unfold transcriptExtractorASWithHash
  have hc : Extraction.MerkleProofs.KeysCover (lookupEvaluation (keccakEvaluationsOfTranscript p.1.2))
      ((keccakEvaluationsOfTranscript p.1.2).map (·.1)) :=
    Extraction.ExtractProofs.keysCover_hashesOf _
  rw [Protocol.EndToEnd.Sound.extractAS_keys_congr D _ _ hc
    (Extraction.ExtractProofs.keysCover_supportKeys (Extraction.ExtractProofs.finite_of_keysCover hc)),
    hH]
  exact Protocol.EndToEnd.Sound.extractAS_mono D hte fun s y hs ↦ hf s y hs

/-- **Knowledge soundness in the random-permutation model, for the agreement-set extractor**, for
a deterministic adversary of at most `Q` queries to `π` and `π⁻¹`. -/
theorem knowledgeSoundnessRpmAS (D : NearDecoder) {A : DetAdversary} {Q : ℕ}
    (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← detExperiment A}[BreaksASWithHash D z] ≤
      soundnessErrorAS Q + rpmError (Q + verifierPermCalls) := by
  rw [(detExperiment_evalDistEq A).prEvent_eq, game]
  obtain ⟨h1, -⟩ := Common.keccak256_transfer2 (pure ()) (fun _ ↦ advR A) (fun _ z ↦ postR z)
    (fun _ z ↦ duplex_postR z) (Q + verifierPermCalls) (isWeightBound_game hA)
    (BreaksASWithHash D)
  refine h1.trans (add_le_add ((romGame_leAS D A).trans ?_) le_rfl)
  exact knowledgeSoundnessAS_coins D (isWeightBound_romAdv hA)

/-- The same, for an adversary with coins. -/
theorem knowledgeSoundnessRpmAS_coins (D : NearDecoder) {B : RandomPermutationAdversary} {Q : ℕ}
    (hB : Common.QueryCostAtMost B Common.permutationCallCost Q) :
    Pr{let z ← soundnessExperimentWithHash B}[BreaksASWithHash D z] ≤
      soundnessErrorAS Q + rpmError (Q + verifierPermCalls) := by
  obtain ⟨A, hA, hle⟩ := rpmExperiment_le_det hB (BreaksASWithHash D)
  exact hle.trans (knowledgeSoundnessRpmAS D hA)

end Rpm

/-- **Knowledge soundness holds for the agreement-set extractor** (in the random-permutation
model), over any near-tuple decoder, with the end statement's bound. -/
theorem knowledgeSoundnessAS_holds (D : NearDecoder) :
    KnowledgeSoundness (transcriptExtractorAS D) := by
  intro A Q hQ hcap
  have := (Rpm.knowledgeSoundnessRpmAS_coins D hQ).trans (soundnessRpmAS_le_statement hcap)
  rw [← map_soundnessExperiment, prEvent_map] at this
  exact this

end LeanVM

end
