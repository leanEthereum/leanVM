import Whir.WHIRNativeArithmetic
import Whir.WHIRPhysicalErasure

/-! Native scalar arithmetic observes commitment presence but never the embedded ghost oracle. Erasing it preserves the exact result, including every error branch and actual query-row computation. -/
namespace Whir.WHIRNativeErasure
open Concrete Protocol WHIRPhysicalErasure WHIRNativeArithmetic

@[simp] theorem eraseLevel_default : eraseLevel default = default := rfl

@[simp] theorem getElem!_eraseLevel (levels : Array LevelProof) (i : Nat) :
    (levels.map eraseLevel)[i]! = eraseLevel levels[i]! := by
  by_cases h : i < levels.size
  · simp only [getElem!_pos, Array.size_map, h, Array.getElem_map]
  · rw [getElem!_neg (levels.map eraseLevel) i (by simpa using h), getElem!_neg levels i h]
    rfl

@[simp] theorem foldBlock_erase (cs : LevelChallenges) (p : LevelProof) (s : State) :
    foldBlock cs (eraseLevel p) s = foldBlock cs p s := rfl

@[simp] theorem oodBatch_erase (cs : LevelChallenges) (p : LevelProof) (s : State) :
    oodBatch cs (eraseLevel p) s = oodBatch cs p s := rfl

@[simp] theorem queryBatch_erase (n i : Nat) (cs : LevelChallenges) (p : LevelProof)
    (qs : Array Nat) (s : State × E) :
    queryBatch n i cs (eraseLevel p) qs s = queryBatch n i cs p qs s := rfl

theorem verifyLevel_erase (c : Config) (ch : Challenges) (proof : Opening) (i : Nat) (s : State) :
    WHIRNativeArithmetic.verifyLevel c ch (eraseOracles proof) i s =
      WHIRNativeArithmetic.verifyLevel c ch proof i s := by
  simp only [WHIRNativeArithmetic.verifyLevel, eraseOracles, getElem!_eraseLevel]
  simp only [foldBlock_erase, oodBatch_erase, queryBatch_erase]
  simp only [eraseLevel, Option.isSome_map]
  rfl

theorem closeTail_erase (ch : Challenges) (proof : Opening) (s : State) :
    closeTail ch (eraseOracles proof) s = closeTail ch proof s := rfl

theorem nativeVerify_erased (c : Config) (ch : Challenges) (lanes : Nat) (initialClaim : E)
    (callerAt : Array E → E) (proof : Opening) :
    nativeVerify c ch lanes initialClaim callerAt (eraseOracles proof) =
      nativeVerify c ch lanes initialClaim callerAt proof := by
  have levels : WHIRNativeArithmetic.verifyLevel c ch (eraseOracles proof) =
      WHIRNativeArithmetic.verifyLevel c ch proof := by
    funext i s
    exact verifyLevel_erase c ch proof i s
  simp only [nativeVerify]
  simp only [levels, closeTail_erase]
  simp only [eraseOracles, Array.size_map]
  rfl

end Whir.WHIRNativeErasure
