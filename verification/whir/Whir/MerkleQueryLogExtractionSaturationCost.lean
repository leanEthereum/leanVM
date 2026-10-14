import Whir.MerkleQueryLogExtractionPublicCost

/-! Polynomial cost of saturating the ACTUAL public compression log once.
The counted parser's value is exactly PublicMerkleLog.records, including
rejection of incomplete/malformed chains. No availability assumption is used.
Together with fused_visit_budget/N pushes this is polynomial in Q,N,width. -/
namespace Whir.MerkleQueryLogExtraction.PublicCost
open Concrete FiatShamirGame DuplexModeGame DuplexRefinement DuplexFraming PublicMerkleLog
open MerkleTransport.Commitments

/-- Replay and reconstruction are executed once, with their actual counters. -/
def parse (log : PublicLog) (n : Node) (answer : Digest32) : Option (List Byte) × Nat :=
  if n.last != true then (none,1) else
    let size := finalLength n.tweak.toNat
    let recovered := recover log (log.length+1) (n.tweak.toNat-size) n.cv
    match recovered.1 with
    | none => (none,recovered.2+1)
    | some prior =>
      let bytes := prior ++ (List.ofFn n.block).take size
      let pieces := chunks bytes
      let replay := run log DuplexCompression.parameterIV 0 pieces.1
      (if replay.1 = some answer then some bytes else none,
        recovered.2+prior.length+64+pieces.2+replay.2+34)

theorem parse_value (log : PublicLog) (n : Node) (answer : Digest32) :
    (parse log n answer).1 = PublicMerkleLog.parse log n answer := by
  unfold parse PublicMerkleLog.parse
  split
  next rejected => rfl
  next final =>
    dsimp only
    rw [← recover_value]
    cases hp : (recover log (log.length+1)
      (n.tweak.toNat-finalLength n.tweak.toNat) n.cv).1 with
    | none => simp
    | some prior =>
      simp only [Option.bind_eq_bind,Option.bind_some]
      rw [chunks_value,run_value]

def parseBudget (Q : Nat) : Nat := 20000*(Q+2)*(Q+2)

theorem parse_steps (log : PublicLog) (n : Node) (answer : Digest32) :
    (parse log n answer).2 ≤ parseBudget log.length := by
  have prefixCost := recover_steps log (log.length+1)
    (n.tweak.toNat-finalLength n.tweak.toNat) n.cv
  unfold parse
  split
  next rejected => simp only [parseBudget]; nlinarith
  next final =>
    dsimp only
    cases hp : (recover log (log.length+1)
      (n.tweak.toNat-finalLength n.tweak.toNat) n.cv).1 with
    | none => simp only []; unfold recoverBudget at prefixCost; unfold parseBudget; nlinarith
    | some prior =>
      have priorSize := PublicMerkleLog.recover_bound (by rw [← recover_value]; exact hp)
      let bytes := prior ++ (List.ofFn n.block).take (finalLength n.tweak.toNat)
      have byteSize : bytes.length ≤ 64*(log.length+2) := by
        have tail : ((List.ofFn n.block).take (finalLength n.tweak.toNat)).length ≤ 64 := by
          simp only [List.length_take,List.length_ofFn]; exact Nat.min_le_right _ _
        dsimp only [bytes]
        simp only [List.length_append]
        omega
      have chunkCost := chunks_steps bytes
      have chunkBudget : (chunks bytes).2 ≤
          (64*(log.length+2)+1)*(64*(log.length+2)+130) :=
        chunkCost.trans (Nat.mul_le_mul (by omega) (by omega))
      have replayCost := run_steps log DuplexCompression.parameterIV 0 (chunks bytes).1
      rw [chunks_value,PublicMerkleLog.chunks_flatten] at replayCost
      have count := chunks_count bytes
      have replayBudget : (run log DuplexCompression.parameterIV 0 (chunks bytes).1).2 ≤
          64*(log.length+2)+(64*(log.length+2)+2)*(log.length+65) := by
        rw [chunks_value]
        apply replayCost.trans
        apply Nat.add_le_add byteSize
        apply Nat.mul_le_mul_right
        omega
      simp only []
      change (recover log (log.length+1)
        (n.tweak.toNat-finalLength n.tweak.toNat) n.cv).2 + prior.length + 64 +
        (chunks bytes).2 + (run log DuplexCompression.parameterIV 0 (chunks bytes).1).2 + 34 ≤ _
      unfold recoverBudget at prefixCost
      unfold parseBudget
      nlinarith

def recordsFrom (log : PublicLog) : PublicLog → Records × Nat
  | [] => ([],0)
  | (n,d)::rest =>
    let current := parse log n d
    let later := recordsFrom log rest
    (match current.1 with
      | none => later.1
      | some bytes => (bytes,d)::later.1,
      current.2+later.2+1)

theorem recordsFrom_value (log entries : PublicLog) :
    (recordsFrom log entries).1 = entries.filterMap
      (fun (n,d) => (PublicMerkleLog.parse log n d).map (fun bytes => (bytes,d))) := by
  induction entries with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨n,d⟩
    simp only [recordsFrom,List.filterMap_cons]
    rw [← parse_value log n d]
    cases hp : (parse log n d).1 <;> simp only [Option.map_none,Option.map_some,ih]

theorem recordsFrom_steps (log entries : PublicLog) :
    (recordsFrom log entries).2 ≤ entries.length*(parseBudget log.length+1) := by
  induction entries with
  | nil => simp [recordsFrom]
  | cons e rest ih =>
    rcases e with ⟨n,d⟩
    have current := parse_steps log n d
    simp only [recordsFrom,List.length_cons]
    nlinarith

/-- Complete saturation is cubic in the actual shared compression budget.
This cost is paid ONCE before preindexing/tree descent, never per output row. -/
theorem actual_records_value (log : PublicLog) :
    (recordsFrom log log).1 = PublicMerkleLog.records log := recordsFrom_value log log

theorem actual_saturation_steps (log : PublicLog) :
    (recordsFrom log log).2 ≤ log.length*(20000*(log.length+2)*(log.length+2)+1) :=
  recordsFrom_steps log log

end Whir.MerkleQueryLogExtraction.PublicCost
