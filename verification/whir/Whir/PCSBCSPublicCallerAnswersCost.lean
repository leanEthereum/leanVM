import Whir.PCSBCSPublicCallerAnswers
import Whir.MerkleQueryLogExtractionPublicCost

/-! Actual reached primitive-record comparisons for public caller answer replay.
One comparison examines a fixed 32-byte CV, 64-byte block, counter and final bit.
This is a structural cost, not native CPU time or allocator certification. -/
set_option autoImplicit false
namespace Whir.PCSBCSPublicCallerAnswers
open Concrete FiatShamirGame DuplexRefinement DuplexFraming DuplexModeGame PublicMerkleLog

/-- Missing earlier nodes stop the same executable replay immediately. -/
def replayFromCounted (log : PublicLog) (cv : Digest32) :
    List DuplexEncoding.Instruction → Option Digest32 × Nat
  | [] => (some cv,1)
  | instruction :: rest =>
      let found := MerkleQueryLogExtraction.PublicCost.lookup log ⟨cv,instruction.1,instruction.2,true⟩
      match found.1 with
      | none => (none,found.2+1)
      | some result =>
          let later := replayFromCounted log result rest
          (later.1,found.2+later.2+1)

theorem replayFromCounted_value (log : PublicLog) (cv : Digest32)
    (plan : List DuplexEncoding.Instruction) :
    (replayFromCounted log cv plan).1 = replayFrom log cv plan := by
  induction plan generalizing cv with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [replayFromCounted,replayFrom,
        MerkleQueryLogExtraction.PublicCost.lookup_value,Option.bind_eq_bind]
      split
      · rename_i found
        simp only [found,Option.bind_none]
      · rename_i result found
        simpa only [found,Option.bind_some] using ih result

theorem replayFromCounted_work (log : PublicLog) (cv : Digest32)
    (plan : List DuplexEncoding.Instruction) :
    (replayFromCounted log cv plan).2 ≤ plan.length*(log.length+1)+1 := by
  induction plan generalizing cv with
  | nil => simp only [replayFromCounted,List.length_nil,Nat.zero_mul,Nat.zero_add,le_refl]
  | cons instruction rest ih =>
      have scan := MerkleQueryLogExtraction.PublicCost.lookup_steps log
        ⟨cv,instruction.1,instruction.2,true⟩
      simp only [replayFromCounted]
      split
      · simp only [List.length_cons]
        nlinarith
      · rename_i result found
        have later := ih result
        simp only [List.length_cons]
        nlinarith

#print axioms replayFromCounted_value
#print axioms replayFromCounted_work
end Whir.PCSBCSPublicCallerAnswers
