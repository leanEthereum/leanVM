import Whir.MerkleQueryLogExtractionCost

/-! Actual public-compression saturation accounting. Counters charge one
fixed-size node comparison plus copied/list-visited bytes; the 256-bit digest,
64-byte block and 64-bit counter have fixed size. They do NOT charge calls to a
whole-hash oracle. Every counted interpreter below executes only public answers.
This is an explicit data-operation model, not a wall-clock/compiler cost claim. -/
namespace Whir.MerkleQueryLogExtraction.PublicCost
open Concrete FiatShamirGame DuplexModeGame DuplexRefinement DuplexFraming PublicMerkleLog

/-- First public answer, with actual record comparisons counted. -/
def lookup : PublicLog → Node → Option Digest32 × Nat
  | [], _ => (none,0)
  | (m,d)::rest, n => if n = m then (some d,1) else
    let later := lookup rest n
    (later.1,later.2+1)

theorem lookup_value (log : PublicLog) (n : Node) : (lookup log n).1 = PublicMerkleLog.lookup log n := by
  induction log with
  | nil => rfl
  | cons e rest ih => rcases e with ⟨m,d⟩; simp only [lookup,PublicMerkleLog.lookup]; split <;> simp [ih]

theorem lookup_steps (log : PublicLog) (n : Node) : (lookup log n).2 ≤ log.length := by
  induction log with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨m,d⟩
    simp only [lookup,List.length_cons]
    split <;> simp only [] <;> omega

def predecessor : PublicLog → Nat → Digest32 → Option Node × Nat
  | [], _, _ => (none,0)
  | (n,d)::rest, count, cv =>
    if d = cv ∧ n.tweak.toNat = count ∧ n.last = false then (some n,1) else
      let later := predecessor rest count cv
      (later.1,later.2+1)

theorem predecessor_value (log : PublicLog) (count : Nat) (cv : Digest32) :
    (predecessor log count cv).1 = PublicMerkleLog.predecessor log count cv := by
  induction log with
  | nil => rfl
  | cons e rest ih => rcases e with ⟨n,d⟩; simp only [predecessor,PublicMerkleLog.predecessor]; split <;> simp [ih]

theorem predecessor_steps (log : PublicLog) (count : Nat) (cv : Digest32) :
    (predecessor log count cv).2 ≤ log.length := by
  induction log with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨n,d⟩
    simp only [predecessor,List.length_cons]
    split <;> simp only [] <;> omega

/-- Recovery counts every predecessor scan and the actual prefix copy. -/
def recover (log : PublicLog) : Nat → Nat → Digest32 → Option (List Byte) × Nat
  | 0, _, _ => (none,1)
  | fuel+1, count, cv =>
    if count = 0 then (if cv = DuplexCompression.parameterIV then some [] else none,1)
    else if count % 64 = 0 then
      let previous := predecessor log count cv
      match previous.1 with
      | none => (none,previous.2+1)
      | some n =>
        let prior := recover log fuel (count-64) n.cv
        match prior.1 with
        | none => (none,previous.2+prior.2+1)
        | some bytes => (some (bytes ++ List.ofFn n.block),previous.2+prior.2+bytes.length+65)
    else (none,1)

theorem recover_value (log : PublicLog) (fuel count : Nat) (cv : Digest32) :
    (recover log fuel count cv).1 = PublicMerkleLog.recover log fuel count cv := by
  induction fuel generalizing count cv with
  | zero => rfl
  | succ fuel ih =>
    simp only [recover,PublicMerkleLog.recover]
    split
    next zero => split <;> rfl
    next positive =>
      split
      next aligned =>
        rw [← predecessor_value]
        cases hp : (predecessor log count cv).1 with
        | none => simp
        | some n =>
          simp only [Option.bind_eq_bind,Option.bind_some]
          rw [← ih (count-64) n.cv]
          cases (recover log fuel (count-64) n.cv).1 <;> simp
      next unaligned => rfl

def recoverBudget (Q fuel : Nat) : Nat := fuel*(Q+3)+64*fuel*fuel+1

theorem recover_steps (log : PublicLog) (fuel count : Nat) (cv : Digest32) :
    (recover log fuel count cv).2 ≤ recoverBudget log.length fuel := by
  induction fuel generalizing count cv with
  | zero => simp [recover,recoverBudget]
  | succ fuel ih =>
    have scan := predecessor_steps log count cv
    simp only [recover]
    split
    next zero => simp [recoverBudget]
    next positive =>
      split
      next aligned =>
        cases hp : (predecessor log count cv).1 with
        | none => simp only []; unfold recoverBudget; nlinarith
        | some n =>
          have prior := ih (count-64) n.cv
          cases hr : (recover log fuel (count-64) n.cv).1 with
          | none => simp only [hr]; unfold recoverBudget at *; nlinarith
          | some bytes =>
            have size := PublicMerkleLog.recover_bound
              (by rw [← recover_value]; exact hr)
            simp only [hr]
            unfold recoverBudget at *
            nlinarith
      next unaligned => simp [recoverBudget]

/-- Construct the same chunks, counting list-length scans and bounded take/
drop work. The 128 charge covers both 64-byte traversals. -/
def chunks (bytes : List Byte) : List (List Byte) × Nat :=
  if bytes.length ≤ 64 then ([bytes],bytes.length+1) else
    let rest := chunks (bytes.drop 64)
    (bytes.take 64 :: rest.1,bytes.length+129+rest.2)
termination_by bytes.length
decreasing_by simp; omega

theorem chunks_value (bytes : List Byte) : (chunks bytes).1 = PublicMerkleLog.chunks bytes := by
  induction bytes using (measure List.length).wf.induction with
  | h bytes ih =>
    rw [chunks,PublicMerkleLog.chunks]
    split
    next short => rfl
    next long =>
      simp only []
      rw [ih (bytes.drop 64) (by
        change (bytes.drop 64).length < bytes.length
        simp only [List.length_drop]
        omega)]

theorem chunks_count (bytes : List Byte) : (PublicMerkleLog.chunks bytes).length ≤ bytes.length+1 := by
  induction bytes using (measure List.length).wf.induction with
  | h bytes ih =>
    rw [PublicMerkleLog.chunks]
    split
    next short => simp
    next long =>
      have rest := ih (bytes.drop 64) (by
        change (bytes.drop 64).length < bytes.length
        simp only [List.length_drop]
        omega)
      simp only [List.length_cons,List.length_drop] at *
      omega

theorem chunks_steps (bytes : List Byte) :
    (chunks bytes).2 ≤ (bytes.length+1)*(bytes.length+130) := by
  induction bytes using (measure List.length).wf.induction with
  | h bytes ih =>
    rw [chunks]
    split
    next short => simp only []; nlinarith
    next long =>
      have rest := ih (bytes.drop 64) (by
        change (bytes.drop 64).length < bytes.length
        simp only [List.length_drop]
        omega)
      simp only [List.length_drop] at rest
      simp only []
      have length : bytes.length-64+64 = bytes.length := by omega
      nlinarith

/-- Ordinary replay against only recorded answers. Node preparation charges
its actual input length plus 64 padded block slots. -/
def run (log : PublicLog) (cv : Digest32) (count : Nat) :
    List (List Byte) → Option Digest32 × Nat
  | [] => (none,1)
  | [bytes] =>
    let answer := lookup log (node cv count bytes true)
    (answer.1,answer.2+bytes.length+65)
  | bytes :: next :: rest =>
    let answer := lookup log (node cv count bytes false)
    match answer.1 with
    | none => (none,answer.2+bytes.length+65)
    | some d =>
      let later := run log d (count+bytes.length) (next::rest)
      (later.1,answer.2+bytes.length+65+later.2)

theorem run_value (log : PublicLog) (cv : Digest32) (count : Nat) (bs : List (List Byte)) :
    (run log cv count bs).1 = PublicMerkleLog.run (PublicMerkleLog.lookup log) cv count bs := by
  induction bs generalizing cv count with
  | nil => rfl
  | cons bytes rest ih =>
    cases rest with
    | nil => exact lookup_value log _
    | cons next rest =>
      simp only [run,PublicMerkleLog.run]
      rw [← lookup_value]
      cases ha : (lookup log (node cv count bytes false)).1 <;> simp [ih]

theorem run_steps (log : PublicLog) (cv : Digest32) (count : Nat) (bs : List (List Byte)) :
    (run log cv count bs).2 ≤ bs.flatten.length+(bs.length+1)*(log.length+65) := by
  induction bs generalizing cv count with
  | nil => simp [run]
  | cons bytes rest ih =>
    cases rest with
    | nil =>
      have scan := lookup_steps log (node cv count bytes true)
      simp only [run,List.length_cons,List.length_nil,List.flatten_cons,List.flatten_nil,
        List.append_nil]
      nlinarith
    | cons next rest =>
      have scan := lookup_steps log (node cv count bytes false)
      have later := ih
      simp only [run]
      cases ha : (lookup log (node cv count bytes false)).1 with
      | none =>
        simp only [List.flatten_cons,List.length_append,List.length_cons]
        nlinarith
      | some d =>
        have budget := later d (count+bytes.length)
        simp only [List.flatten_cons,List.length_append,List.length_cons] at *
        nlinarith

end Whir.MerkleQueryLogExtraction.PublicCost
