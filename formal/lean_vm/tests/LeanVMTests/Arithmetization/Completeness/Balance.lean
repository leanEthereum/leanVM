import LeanVM.Arithmetization.Completeness.Balance

/-!
# Tests: the chain balance

`chain_balance` is the list arithmetic behind the balance of the memory and the bytecode pair:
the seeds and the pushes of the reads are a permutation of the finalizes and the pulls, when the
reads of each cell number its messages in order. The concrete lists here are the lemma at small
inhabitants, and the four rejections are each hypothesis dropped: a repeated number, a cell
outside the block, a wrong finalize, and a key missing from the regrouping.
-/

namespace LeanVMTests.Arithmetization.Completeness.Balance

open LeanVM.Arithmetization

/-! ## The read counters -/

-- A cell is numbered by its own reads, `0, 1, 2, …`, never by the position in the sequence.
#guard readExps (fun _ : ℕ ↦ 0) [1, 2, 1, 1] = [0, 0, 1, 2]

#guard readExps (fun _ : ℕ ↦ 0) [1, 2, 3] = [0, 0, 0]

-- The counters after the reads are the number of reads of each cell.
#guard readBump (fun _ : ℕ ↦ 0) [1, 2, 1, 1] 1 = 3

#guard readBump (fun _ : ℕ ↦ 0) [1, 2, 1, 1] 2 = 1

#guard readBump (fun _ : ℕ ↦ 0) [1, 2, 1, 1] 3 = 0

-- Counters carry over a concatenation, so a sequence of rows is one sequence of reads.
example : readExps (fun _ : ℕ ↦ 0) ([1, 2] ++ [1, 2]) =
    readExps (fun _ : ℕ ↦ 0) [1, 2] ++ readExps (readBump (fun _ : ℕ ↦ 0) [1, 2]) [1, 2] :=
  readExps_append _ _ _

/-! ## The chain lemma at a small inhabitant -/

/-- Two cells, reads of the first twice and of the second once. -/
example : ([1, 2].map (fun a ↦ (a, (fun _ : ℕ ↦ 0) a)) ++
      List.zipWith (fun a e ↦ (a, e + 1)) [1, 2, 1] (readExps (fun _ : ℕ ↦ 0) [1, 2, 1])).Perm
    ([1, 2].map (fun a ↦ (a, readBump (fun _ : ℕ ↦ 0) [1, 2, 1] a)) ++
      List.zipWith (fun a e ↦ (a, e)) [1, 2, 1] (readExps (fun _ : ℕ ↦ 0) [1, 2, 1])) :=
  chain_balance [1, 2] (by decide) (fun a e ↦ (a, e)) [1, 2, 1] (by decide) _

/-- The same instance computed: seeds `(1,0), (2,0)` and pushes `(1,1), (2,1), (1,2)` against
finalizes `(1,2), (2,1)` and pulls `(1,0), (2,0), (1,1)`. -/
example : ([1, 2].map (fun a ↦ (a, 0)) ++ [(1, 1), (2, 1), (1, 2)]).Perm
    ([(1, 2), (2, 1)] ++ [(1, 0), (2, 0), (1, 1)]) := by decide

/-! ## Each hypothesis is load-bearing -/

/-- Two reads of one cell that both carry the number `0` do not balance: the second pulls a
message nobody pushed. -/
example : ¬ (([1].map fun a ↦ (a, 0)) ++ [(1, 1), (1, 1)]).Perm
    (([1].map fun a ↦ (a, 2)) ++ [(1, 0), (1, 0)]) := by decide

/-- A read of a cell outside the block does not balance: nothing seeds it. -/
example : ¬ (([1, 2].map fun a ↦ (a, 0)) ++ [(3, 1)]).Perm
    (([1, 2].map fun a ↦ (a, 0)) ++ [(3, 0)]) := by decide

/-- A finalize that is not the cell's last message leaves the multisets apart. -/
example : ¬ (([1].map fun a ↦ (a, 0)) ++ [(1, 1)]).Perm
    (([1].map fun a ↦ (a, 0)) ++ [(1, 0)]) := by decide

/-- A key list with a repeated cell is not `Nodup`: the chain lemma does not apply to it. -/
example : ¬ [1, 1].Nodup := by decide

/-! ## The regrouping -/

/-- The rows of the run, regrouped into the tables, are the same rows. -/
example : ([1, 2].flatMap fun o ↦ [1, 2, 1, 2, 2].filter fun x ↦ x = o).Perm [1, 2, 1, 2, 2] :=
  regroup_perm [1, 2] id _ (by decide) (by decide)

/-- A row whose key is not a table is dropped: the regrouped list is not the list. -/
example : ¬ ([1, 2].flatMap fun o ↦ [1, 2, 3].filter fun x ↦ x = o).Perm [1, 2, 3] := by decide

/-! ## The state chain -/

/-- The initial state and the successors against the final state and the states: `f 0` and
`f 1, f 2, f 3` pushed, `f 3` and `f 0, f 1, f 2` pulled. -/
example : (0 :: (List.range 3).map fun k ↦ 10 * (k + 1)).Perm
    (30 :: (List.range 3).map fun k ↦ 10 * k) :=
  shift_perm (fun k ↦ 10 * k) 3

/-- Without the closing pull the rotation does not balance. -/
example : ¬ (0 :: (List.range 3).map fun k ↦ 10 * (k + 1)).Perm
    (20 :: (List.range 3).map fun k ↦ 10 * k) := by decide

end LeanVMTests.Arithmetization.Completeness.Balance
