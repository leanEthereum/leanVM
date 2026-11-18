/-
  LeanVM.Protocol.Extraction.AS.TopA

  The agreement-set extractor on the transcript's indices, over arrays.
-/

module

public import LeanVM.Protocol.Extraction.AS.Top
public import LeanVM.Protocol.Whir.Sound.StackA

/-!
# The extractor over arrays

`extractA prog input qs π`: `extractM` over one-error decoding, its finish over arrays
(`finishA`): every root's leaves inverted once (`Fast.leavesOf`), its word held column by column
(`wordsA`), the descent over arrays (`descendTraceA`), level 0's stack from its array (`stackA`).
It is `extractM newtonValsDecoder` (`extractA_eq`).
-/

namespace LeanVM.Extraction.AS

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Protocol.Whir.Sound
open LeanVM.Protocol.EndToEnd LeanVM.Protocol.EndToEnd.Sound LeanVM.Protocol.Whir.Params
open LeanVM.Extraction.Fast Common
open LeanVM.Protocol.EndToEnd.Complete (publicInputDigest)

@[expose] public section

/-- Every root's word, column by column: its leaves inverted once. -/
def wordsA (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) : List AV :=
  roots.mapIdx fun i x ↦
    let lv := Fast.leavesOf qs x.2.2 x.2.1 x.1
    Array.ofFn fun v : Fin (codesOf μ R i).n ↦ (lanesOf i (leafAt lv x.2.1 x.2.2 v)).toArray

/-- **The extractor's finish over arrays.** -/
def finishA (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    Option (Execution prog) :=
  if laneBits ≤ r.1.2.1.1.stackLog ∧
      2 ^ (r.1.2.1.1.stackLog - laneBits) ≤ (codesOf r.1.2.1.1.stackLog r.1.2.1.2 0).n then
    (descendTraceA (codesOf r.1.2.1.1.stackLog r.1.2.1.2)
      (wordsA r.1.2.1.1.stackLog r.1.2.1.2 qs r.2.roots) r.1.2.2 0).bind fun T ↦
    if T.1 = laneBits then
      Extraction.candidateExecution prog input r.1.2.1.1 (stackA r.1.2.1.1.stackLog T.2)
    else none
  else none

theorem lanesOf_nil (i : ℕ) : lanesOf i [] = [] := by
  unfold lanesOf; split <;> rfl

theorem laneO_wordsA (μ R : ℕ) (qs : List (PermutationQuery KeccakState × KeccakState))
    (roots : List (Digest × ℕ × ℕ)) (i j : ℕ) (v : Fin (codesOf μ R i).n) :
    laneO i (roots.map fun x ↦ (x.2.1, x.2.2, wordM qs x.1 x.2.1 x.2.2)) (codesOf μ R i).n j v =
      (((wordsA μ R qs roots).getD i #[]).getD v #[]).getD j 0 := by
  unfold laneO wordOf wordsA
  by_cases hi : i < roots.length
  · have h1 : (roots.mapIdx fun i x ↦ Array.ofFn fun v : Fin (codesOf μ R i).n ↦
        (lanesOf i (leafAt (Fast.leavesOf qs x.2.2 x.2.1 x.1) x.2.1 x.2.2 v)).toArray).getD i #[] =
        Array.ofFn fun v : Fin (codesOf μ R i).n ↦ (lanesOf i (leafAt (Fast.leavesOf qs
          roots[i].2.2 roots[i].2.1 roots[i].1) roots[i].2.1 roots[i].2.2 v)).toArray := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_getElem hi]
      rfl
    simp only at h1 ⊢
    rw [h1, Prover.Enc.getD_ofFn _ _ _ v.isLt, List.getElem?_map, List.getElem?_eq_getElem hi]
    simp [wordM, Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  · have h1 : (roots.mapIdx fun i x ↦ Array.ofFn fun v : Fin (codesOf μ R i).n ↦
        (lanesOf i (leafAt (Fast.leavesOf qs x.2.2 x.2.1 x.1) x.2.1 x.2.2 v)).toArray).getD i #[] =
        #[] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_mapIdx, List.getElem?_eq_none (by omega)]
      rfl
    simp only at h1 ⊢
    rw [h1, List.getElem?_map, List.getElem?_eq_none (by omega)]
    simp [lanesOf_nil, Array.getD_eq_getD_getElem?]

/-- **The finish over arrays is the finish over values**, with one-error decoding. -/
theorem finishA_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState))
    (r : (Bool × ((Verifier.Layout × ℕ) × WhirTrace)) × VerifierProgramState) :
    finishA prog input qs r = finishW newtonValsDecoder prog input (wordM qs) r := by
  unfold finishA finishW
  by_cases hμ : laneBits ≤ r.1.2.1.1.stackLog
  · rw [dite_eq_left hμ]
    by_cases hn : 2 ^ (r.1.2.1.1.stackLog - laneBits) ≤ (codesOf r.1.2.1.1.stackLog r.1.2.1.2 0).n
    · rw [ite_eq_left ⟨hμ, hn⟩, dite_eq_left hn, descendTraceA_eq _ _
        (laneO_wordsA r.1.2.1.1.stackLog r.1.2.1.2 qs r.2.roots), Option.bind_map]
      refine congrArg _ (funext fun T ↦ ?_)
      obtain ⟨k, V⟩ := T
      simp only [Function.comp, toAVS]
      by_cases hm : k = laneBits
      · subst hm
        rw [dite_eq_left rfl, stackA_eq hμ hn]
        exact ite_eq_left rfl
      · rw [dite_eq_right hm]
        exact ite_eq_right hm
    · rw [ite_eq_right fun h ↦ hn h.2, dite_eq_right hn]
  · rw [ite_eq_right fun h ↦ hμ h.1, dite_eq_right hμ]

/-- **The agreement-set extractor on the transcript's indices, over arrays.** -/
def extractA (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    Option (Execution prog) :=
  let F := fwdF (fwdIndex qs)
  (seedWithHash (KeccakHash.keccak256With F) F (bytecodeWords prog)
    (publicInputDigest input)).bind fun seed ↦
  (skelReplay F skSizes (startState π seed)).bind fun r₁ ↦
  (decSizes (bytecodeWords prog) r₁.1).bind fun a ↦
  (skelReplay F (skBody a.1 a.2) r₁.2).bind fun r₂ ↦
  (decBody a.1 a.2 r₂.1).bind fun tr ↦
  finishA prog input qs ((true, (a, tr)), r₂.2)

theorem extractA_eq (prog : LeanIsaProgram) (input : PublicInput)
    (qs : List (PermutationQuery KeccakState × KeccakState)) (π : Proof) :
    extractA prog input qs π = extractM newtonValsDecoder prog input qs π := by
  unfold extractA extractM
  simp only [finishA_eq]

end
end LeanVM.Extraction.AS
