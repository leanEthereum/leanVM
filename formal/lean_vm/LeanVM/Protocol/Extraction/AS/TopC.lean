/-
  LeanVM.Protocol.Extraction.AS.TopC

  The agreement-set extractor in the form the cost machine compiles.
-/

module

public import LeanVM.Protocol.Extraction.AS.TopA
public import LeanVM.Protocol.Whir.Sound.DescentC
public import LeanVM.Protocol.EndToEnd.Sound.SkelPairs

/-!
# The extractor, compiled form

`extractC`: `extractA` with the descent in its compiled form (`descendTraceC`) and the levels'
shapes as numbers (`lvC`). It is `extractA` (`extractC_eq`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Params
open LeanVM.Extraction.Fast Common
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)

@[expose] public section

/-- Every root's word, column by column, the levels' shapes as numbers. -/
def wordsC (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) : List AV :=
  roots.mapIdx fun i x ↦
    let lv := Fast.leavesOf qs x.2.2 x.2.1 x.1
    Array.ofFn fun v : Fin (2 ^ ((lvC μ R i).1 + (lvC μ R i).2.1)) ↦
      (lanesOf i (leafAt lv x.2.1 x.2.2 v)).toArray

theorem wordsC_eq (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) : wordsC μ R qs roots = wordsA μ R qs roots := by
  unfold wordsC wordsA
  refine List.mapIdx_eq_mapIdx_iff.mpr fun i _ ↦ ?_
  rw [lvC_eq]

/-- **The extractor's finish, compiled form.** -/
def finishC (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    Option (Execution prog) :=
  if laneBits ≤ r.1.2.1.1.stackLog ∧ 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤
      2 ^ ((lvC r.1.2.1.1.stackLog r.1.2.1.2 0).1 + (lvC r.1.2.1.1.stackLog r.1.2.1.2 0).2.1) then
    (descendTraceC r.1.2.1.1.stackLog r.1.2.1.2
      (wordsC r.1.2.1.1.stackLog r.1.2.1.2 qs r.2.roots) r.1.2.2 0).bind fun T ↦
    if T.1 = laneBits then
      Extraction.candidateExecution prog input r.1.2.1.1 (stackA r.1.2.1.1.stackLog T.2)
    else none
  else none

theorem finishC_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    finishC prog input qs r = finishA prog input qs r := by
  unfold finishC finishA
  rw [descendTraceC_eq, wordsC_eq, lvC_eq]

/-- **The agreement-set extractor, compiled form.** -/
def extractC (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let F := fwdF (fwdIndex qs)
  (seedWithHash (KeccakHash.keccak256With F) F (bytecodeWords prog)
    (publicInputDigest input)).bind fun seed ↦
  (skelReplay F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizes (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplay F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBody a.1 a.2 r₂.1).bind fun tr ↦
  finishC prog input qs ((true, (a, tr)), r₂.2)

theorem extractC_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractC prog input qs π = extractA prog input qs π := by
  unfold extractC extractA
  simp only [finishC_eq]

/-- **The agreement-set extractor, compiled form**: the replay records each event's values
only (`skelReplayP`), the decoders read them (`decSizesP`, `decBodyP`). -/
def extractP (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let F := fwdF (fwdIndex qs)
  (seedWithHash (KeccakHash.keccak256With F) F (bytecodeWords prog)
    (publicInputDigest input)).bind fun seed ↦
  (skelReplayP F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizesP (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplayP F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBodyP a.1 a.2 r₂.1).bind fun tr ↦
  finishC prog input qs ((true, (a, tr)), r₂.2)

theorem extractP_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractP prog input qs π = extractC prog input qs π := by
  unfold extractP extractC
  simp only [skelReplayP_eq, Option.bind_map, Function.comp_def, ← decSizes_eq, ← decBody_eq]

end
end LeanVM.Extraction.AS
