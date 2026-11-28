/-
  LeanVM.Protocol.Rpm.VerifierCost

  The permutation calls of the leanVM verifier, and of the knowledge-soundness transfer's game.
-/

module

public import LeanVM.Protocol.Rpm.Embed
public import LeanVM.Protocol.Rpm.RomRelabel
public import LeanVM.Protocol.Verifier.Cost
public import LeanVM.Protocol.Relation.NoCommit
import Statement.Fast.Keccak

@[expose] public section

/-!
# The leanVM verifier's permutation calls

Every commitment the leanVM verifier program reads has width at most `maxWidth = 128`
(`widthsLE_leanVmProgram`): the stack's root is `2^fold` wide and a later level's `2 · 2^fold`,
with every fold of an admissible ladder at most `6` (`ladder_folds`); the front phases read no
commitment (`NoCommit`). So every hash the verifier computes is short (`allQ_verifier`), and its
`leanVmQueryBound` queries cost at most `verifierPermCalls = leanVmQueryBound · 2^30` permutation
calls (`isWeightBound_verifier`). With the adversary's `Q`, the transfer's game makes at most
`Q + verifierPermCalls` (`isWeightBound_game`), and its verifier follows the duplex discipline
(`duplex_postR`).
-/

namespace LeanVM.Rpm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec

variable {α : Type}

/-! ## The widths of the verifier's commitments -/

/-- A program without commitments has every width bound. -/
theorem WidthsLE.of_noCommit {W : ℕ} {p : VerifierProgram α} (h : NoCommit p) : WidthsLE W p := by
  induction h with
  | ret a => trivial
  | fail => trivial
  | read _ ih => exact ih
  | sample _ ih => exact ih
  | readPacked _ ih => exact ih
  | samplePacked _ ih => exact ih
  | grind _ ih => exact ih
  | query _ ih => exact ih

/-- Every level of an admissible ladder folds at most `6` variables; decided over the admissible
pairs. -/
theorem ladder_folds (μ logInvRate : ℕ) (levels : List Whir.Level)
    (h : Whir.ladder μ logInvRate = some levels) : ∀ l ∈ levels, l.fold ≤ 6 := by
  by_cases hadm : Whir.Admissible μ logInvRate
  · have key : ∀ μ < Whir.maxLogStack + 1, ∀ r < 5, Whir.Admissible μ r →
        ∀ levels, Whir.ladder μ r = some levels →
          (levels.all fun l ↦ decide (l.fold ≤ 6)) = true := by
      decide +kernel
    have hk := key μ (Nat.lt_succ_of_le hadm.2.1) logInvRate (Nat.lt_succ_of_le hadm.2.2.2)
      hadm levels h
    simpa using hk
  · simp [Whir.ladder, hadm] at h

theorem noCommit_queryOpenings (i : ℕ) (ps : List ℕ) :
    NoCommit (VerifierProgram.queryOpenings i ps) :=
  .query fun _ ↦ .ret _

theorem noCommit_sampleQueriesAux (depth : ℕ) :
    ∀ (fuel remaining : ℕ), NoCommit (sampleQueriesAux depth fuel remaining)
  | 0, _ => by unfold sampleQueriesAux; exact noCommit_pure _
  | fuel + 1, remaining => by
    unfold sampleQueriesAux
    split
    · exact noCommit_pure _
    · exact noCommit_sampleChallenge.bind' fun _ ↦
        (noCommit_sampleQueriesAux depth fuel _).bind' fun _ ↦ noCommit_pure _

theorem noCommit_foldRounds : ∀ (n : ℕ) (s : WhirState), NoCommit (foldRounds n s)
  | 0, _ => by unfold foldRounds; exact noCommit_pure _
  | n + 1, s => by
    unfold foldRounds
    refine NoCommit.bind' ?_ fun _ ↦ ?_
    · unfold foldRound
      exact noCommit_readScalar.bind' fun _ ↦ noCommit_readScalar.bind' fun _ ↦
        noCommit_readScalar.bind' fun _ ↦ noCommit_readScalar.bind' fun _ ↦
        (noCommit_grindProofOfWork _).bind' fun _ ↦ noCommit_sampleChallenge.bind' fun _ ↦
        noCommit_sampleChallenge.bind' fun _ ↦ noCommit_pure _
    · exact (noCommit_foldRounds n _).bind' fun _ ↦ noCommit_pure _

theorem widthsLE_whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ∀ (index : ℕ) (levels : List Whir.Level) (s : WhirState), (∀ l ∈ levels, l.fold ≤ 6) →
      WidthsLE maxWidth (whirLevels logN laneFolds evaluateBasis index levels s)
  | _, [], _, _ => by unfold whirLevels; exact WidthsLE.fail
  | index, [level], s, _ => by
    unfold whirLevels
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_foldRounds _ _)) fun r ↦ ?_
    obtain ⟨s', rounds⟩ := r
    dsimp only
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_readScalars _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_grindProofOfWork _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_sampleQueriesAux _ _ _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_queryOpenings _ _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_require _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_sumcheck _ _ _)) fun _ ↦ ?_
    exact WidthsLE.of_noCommit (noCommit_require _)
  | index, level :: next :: rest, s, hf => by
    have hn : next.fold ≤ 6 := hf next (by simp)
    unfold whirLevels
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_foldRounds _ _)) fun r ↦ ?_
    obtain ⟨s', rounds⟩ := r
    dsimp only
    refine WidthsLE.seq (WidthsLE.commitP (two_pow_le hn)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_readScalars _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_grindProofOfWork _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_sampleChallenges _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit noCommit_readScalar) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_grindProofOfWork _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_sampleQueriesAux _ _ _)) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit noCommit_sampleChallenge) fun _ ↦ ?_
    refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_queryOpenings _ _)) fun _ ↦ ?_
    exact widthsLE_whirLevels logN laneFolds evaluateBasis _ _ _
      fun l hl ↦ hf l (List.mem_cons_of_mem _ hl)

theorem widthsLE_verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim)
    (batching : E) :
    WidthsLE maxWidth (verifyStackedOpening stackLog logInvRate claims batching) := by
  unfold verifyStackedOpening verifyWhir
  exact WidthsLE.seq (WidthsLE.of_noCommit (noCommit_require _)) fun _ ↦
    WidthsLE.liftOption_seq fun config hc ↦
      widthsLE_whirLevels _ _ _ _ config _ (ladder_folds _ _ _ hc)

theorem widthsLE_commitStack (logN logInvRate : ℕ) :
    WidthsLE maxWidth (commitStack logN logInvRate) := by
  unfold commitStack
  exact WidthsLE.liftOption_seq fun config hc ↦ by
    cases config with
    | nil => exact WidthsLE.fail
    | cons level rest =>
      exact WidthsLE.commitP (pow_le (ladder_folds _ _ _ hc level (by simp)))

theorem noCommit_readOod (n : ℕ) : NoCommit (readOod n) := by
  unfold readOod
  exact (noCommit_grindProofOfWork _).bind' fun _ ↦ (noCommit_sampleChallenges _).bind' fun _ ↦
    noCommit_readScalar.bind' fun _ ↦ noCommit_pure _

theorem noCommit_ringSwitch (claims : List RingClaim) : NoCommit (ringSwitch claims) := by
  unfold ringSwitch
  exact (noCommit_grindProofOfWork _).bind' fun _ ↦
    (noCommit_sampleChallengesPacked _).bind' fun _ ↦ noCommit_pure _

theorem noCommit_memoryTermClaim (layout : Layout) (link : LinkEnd) :
    NoCommit (memoryTermClaim layout link) := by
  unfold memoryTermClaim
  exact (noCommit_liftOption _).bind' fun _ ↦ (noCommit_liftOption _).bind' fun _ ↦
    noCommit_pure _

/-- **Every commitment of the leanVM verifier program has width at most `128`.** -/
theorem widthsLE_leanVmProgram (bytecode : List K) (publicInput : Digest) :
    WidthsLE maxWidth (leanVmVerifierProgram bytecode publicInput) := by
  unfold leanVmVerifierProgram verifyExecution
  refine WidthsLE.seq (WidthsLE.seq (WidthsLE.of_noCommit (noCommit_readAnnouncedSizes bytecode))
    fun p ↦ ?_) fun _ ↦ trivial
  obtain ⟨layout, logInverseRate⟩ := p
  refine WidthsLE.seq (widthsLE_commitStack _ _) fun _ ↦ ?_
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_readOod _)) fun _ ↦ ?_
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_verifyLink layout)) fun link ↦ ?_
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_bindPublicInput _ _)) fun _ ↦ ?_
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_keccakValidity _ link)) fun r ↦ ?_
  obtain ⟨outputs, keccakPoint, keccakSlices⟩ := r
  refine WidthsLE.liftOption_seq fun _ _ ↦ ?_
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_ringSwitch _)) fun r ↦ ?_
  obtain ⟨ring, batching⟩ := r
  refine WidthsLE.seq (WidthsLE.of_noCommit (noCommit_memoryTermClaim _ _)) fun _ ↦ ?_
  exact widthsLE_verifyStackedOpening _ _ _ _

/-! ## The verifier's permutation calls -/

/-- `TAG` is nine bytes. -/
theorem versionTag_length : versionTag.length = 9 := by
  unfold versionTag
  decide +kernel

theorem allQ_seedRun (prog : LeanIsaProgram) (input : PublicInput) :
    AllQueriesSatisfy ((leanVmSeed (bytecodeWords prog) (publicInputDigest input)).run
      callKeccak256 callKeccakF1600) Short := by
  refine allQueriesSatisfy_bind (allQ_hsRun _ _ fun f hf ds ↦ ?_) fun _ ↦ allQ_queryF _
  simp only [leanVmSeed, List.mem_cons, List.not_mem_nil, or_false] at hf
  subst hf
  rw [List.length_append, versionTag_length]
  have := bytecode_length prog
  omega

/-- The verifier of the statement is the seeded verifier at the leanVM seed and program. -/
theorem verifier_eq (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    verifierWithHash callKeccak256 callKeccakF1600 prog input proof =
      verifierComp (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input)) proof :=
  (verifierComp_leanVm _ _ _).symm

theorem allQ_verifier (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    AllQueriesSatisfy (verifierWithHash callKeccak256 callKeccakF1600 prog input proof) Short := by
  rw [verifier_eq]
  exact allQueriesSatisfy_bind (allQ_seedRun prog input) fun seed ↦
    allQ_runProof _ seed proof (widthsLE_leanVmProgram _ _)

/-- The permutation calls of the verifier, at most, on every statement and proof: its
`leanVmQueryBound` queries, each a permutation or a Keccak-256 hash of at most `2^37 + 9` bytes,
at most `2^30` blocks. -/
def verifierPermCalls : ℕ := leanVmQueryBound * 2 ^ 30

/-- **The verifier makes at most `verifierPermCalls` permutation calls** on every statement and
proof. -/
theorem isWeightBound_verifier (prog : LeanIsaProgram) (input : PublicInput) (proof : Proof) :
    Common.QueryCostAtMost (verifierWithHash callKeccak256 callKeccakF1600 prog input proof)
      hashBlocks verifierPermCalls := by
  have hN := isTotalQueryBound_leanVm (bytecodeWords prog) (publicInputDigest input) proof
  rw [← verifier_eq] at hN
  exact isWeightBound_of_isTotalQueryBound hashBlocks (2 ^ 30) hN
    ((allQ_verifier prog input proof).mono fun _ h ↦ hashBlocks_le_of_short h)

/-! ## The transfer's game -/

/-- The verifier on bytes follows the duplex discipline. -/
theorem duplex_postR (z : (ProgramAndInput × Proof) × PermutationTranscript) :
    Common.Duplex Common.KState.zero Common.keccakNF (postR z) [] :=
  duplex_map _ _ [] (duplex_toRHF _ [] (duplexVm_verifier _ _ _))

/-- The adversary's permutation queries, one each. -/
theorem isWeightBound_advR_cost {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (advR A) advCost Q := by
  refine Common.isWeightBound_run_simulateQ logRel (fun _ ↦ 1) _ (fun q T ↦ ?_)
    (isWeightBound_one_of_total hA) []
  simp only [logRel, StateT.run_mk, relP]
  exact Common.isWeightBound_map _ (Common.isWeightBound_map _
    (Common.isWeightBound_query advCost (.inr (.inr (permQueryToRpm q)))))

/-- **The permutation calls of the transfer game**: the adversary's `Q`, then at most
`verifierPermCalls` of the verifier. -/
theorem isWeightBound_game {A : DetAdversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Common.QueryCostAtMost (game A) gameCost (Q + verifierPermCalls) := by
  rw [game, Common.rpmGame2, simulateQ_pure, pure_bind]
  refine (isWeightBound_advEmbed (isWeightBound_advR_cost hA)).bind fun z ↦ ?_
  rw [postR, simulateQ_map]
  exact Common.isWeightBound_map _ (isWeightBound_hfEmbed_toRHF (isWeightBound_verifier _ _ _))

end LeanVM.Rpm

end
