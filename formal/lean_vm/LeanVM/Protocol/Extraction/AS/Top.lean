/-
  LeanVM.Protocol.Extraction.AS.Top

  The agreement-set extractor on the transcript's indices.
-/

module

public import LeanVM.Protocol.Extraction.AS.Hash
public import LeanVM.Protocol.Extraction.Fast.Transcript
public import LeanVM.Protocol.Extraction.Fast.RunVec
public import LeanVM.Protocol.Extraction.Fast.AfterRoot
public import LeanVM.Protocol.LeanVMRpmASC

/-!
# The extractor on the transcript's indices

`extractM prog input qs π`: `extractASF` on the transcript's permutation queries `qs`, the
permutation answered by the index of first forward answers (`fwdIndex`), the bytecode's digest
computed through it (`keccak256_of_lookupEvaluation`), and every root's committed word read
through the transcript's preimage index (`leavesOf`, `leavesOf_eq`).
Wherever the skeleton's extractor returns an execution, it returns it (`extractM_of_ASF`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Params
open LeanVM.Extraction.Fast Common
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)

@[expose] public section

attribute [local instance] lexOrd

variable {D : NearDecoder} (W : ValsDecoder D)

/-- The extractor's finish with the committed words given by `word root height width`. -/
def finishW (prog : LeanIsaProgram) (input : PublicInput) (word : Digest → ℕ → ℕ → ℕ → List K)
    (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    Option (Execution prog) :=
  if hμ : laneBits ≤ r.1.2.1.1.stackLog then
    if hn : 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤ (codesOf r.1.2.1.1.stackLog r.1.2.1.2 0).n then
      (descendTraceV W (codesOf r.1.2.1.1.stackLog r.1.2.1.2)
        (r.2.roots.map fun x ↦ (x.2.1, x.2.2, word x.1 x.2.1 x.2.2))
        r.1.2.2 0).bind fun T ↦
      if hm : T.1 = laneBits then
        Extraction.candidateExecution prog input r.1.2.1.1 (stackV hμ hn (hm ▸ T.2)).values
      else none
    else none
  else none

theorem finishAS_eq (prog : LeanIsaProgram) (input : PublicInput) (H : Bytes → Option Digest)
    (keys : List Bytes) (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    finishAS W prog input H keys r =
      finishW W prog input (fun root h w ↦ Extraction.committedWordC H keys root h w) r :=
  rfl

/-- **The committed leaves through the preimage index** are the statement's. -/
theorem leavesOf_eq (qs : List (PermutationQuery KeccakState × KeccakState)) (w h : ℕ)
    (root : Digest) :
    Fast.leavesOf qs w h root =
      let P := keccakEvaluationsOfTranscript qs
      committedLeaves (lookupEvaluation P) (P.map (·.1)) root h w := by
  unfold Fast.leavesOf committedLeaves
  rw [← subtreeLeavesWith_preimage]
  have key : ∀ d, ∀ len ∈ [64, 8 * w],
      preimageIn (transcriptIndex qs (max 64 (8 * w))) d len =
        preimage (answerPairs (lookupEvaluation (keccakEvaluationsOfTranscript qs))
          ((keccakEvaluationsOfTranscript qs).map (·.1))) d len := fun d len hlen ↦ by
    have hL : len ≤ max 64 (8 * w) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
      omega
    rw [transcriptIndex, preimageIn_preimageIndex, answerPairs_firstAnswers,
      keccakEvaluationsFast_eq, ← filter_answerPairs, preimage_filter]
    intro p _ hp
    simp [hp, hL]
  exact subtreeLeavesWith_congr (fun d ↦ key d 64 (by simp)) (fun d ↦ key d (8 * w) (by simp)) h root

/-- The committed word of a root, through the preimage index. -/
def wordM (qs : List (PermutationQuery KeccakState × KeccakState)) (root : Digest) (h w : ℕ) :
    ℕ → List K :=
  leafAt (Fast.leavesOf qs w h root) h w

/-- **The agreement-set extractor on the transcript's indices.** -/
def extractM (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let F := fwdF (fwdIndex qs)
  (seedWithHash (KeccakHash.keccak256With F) F (bytecodeWords prog)
    (publicInputDigest input)).bind fun seed ↦
  (skelReplay F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizes (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplay F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBody a.1 a.2 r₂.1).bind fun tr ↦
  finishW W prog input (wordM qs) ((true, (a, tr)), r₂.2)

/-- **Wherever the skeleton's extractor returns an execution, the indexed one returns it.** -/
theorem extractM_of_ASF {prog : LeanIsaProgram} {input : PublicInput} {T : OracleQueryLog}
    {π : Proof} {t : Execution prog} (h : transcriptExtractorASF W prog input T π = some t) :
    extractM W prog input (permutationQueries T) π = some t := by
  unfold transcriptExtractorASF extractASF at h
  simp only at h
  obtain ⟨seed, hseed, h⟩ := Option.bind_eq_some_iff.mp h
  rw [seedRun_leanVmSeed] at hseed
  unfold seedWithHash fiatShamirIvWithHash at hseed
  obtain ⟨iv, hiv, hseed⟩ := Option.bind_eq_some_iff.mp hseed
  unfold extractM
  rw [fwdF_fwdIndex]
  have hiv' := keccak256_of_lookupEvaluation hiv
  simp only [seedWithHash, fiatShamirIvWithHash, bind, Option.bind, hiv'] at hseed ⊢
  simp only [hseed]
  have hfin : ∀ r, finishAS W prog input (lookupEvaluation (keccakEvaluationsOfTranscript
      (permutationQueries T))) ((keccakEvaluationsOfTranscript (permutationQueries T)).map (·.1)) r =
        finishW W prog input (wordM (permutationQueries T)) r := fun r ↦ by
    rw [finishAS_eq]
    unfold wordM Extraction.committedWordC
    simp only [leavesOf_eq]
  simp only [hfin] at h
  exact h
