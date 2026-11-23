module

public import NativeVm.Model.Whir

/-!
# The subspace polynomials as `whir.rs` computes them

`subspace_at_table(table, x)` runs `subspaceAtTable`'s fold one table entry at a time
(`atAfter`, `atAfter_succ`), the slot of `What_i` then the next `W`.
-/

namespace NativeRustcVm.Whir

open NativeVm.Model

@[expose] public section

/-- A step of `subspaceAtTable`'s fold. -/
def atStep (acc : Array UInt64 × UInt64) (e : UInt64 × UInt64) : Array UInt64 × UInt64 :=
  (acc.1.push (kmul acc.2 e.2), kmul acc.2 acc.2 ^^^ kmul e.1 acc.2)

/-- The fold after the table's first `i` entries. -/
def atAfter (tb : Array (UInt64 × UInt64)) (x : UInt64) (i : Nat) : Array UInt64 × UInt64 :=
  (tb.toList.take i).foldl atStep (#[], x)

end

public section

theorem atAfter_zero (tb : Array (UInt64 × UInt64)) (x : UInt64) : atAfter tb x 0 = (#[], x) := by
  simp [atAfter]

theorem atAfter_succ (tb : Array (UInt64 × UInt64)) (x : UInt64) {i : Nat} (h : i < tb.size) :
    atAfter tb x (i + 1) = atStep (atAfter tb x i) tb[i] := by
  rw [atAfter, atAfter, List.take_add_one, List.foldl_append]
  simp [h]

theorem atAfter_size (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    ∀ i ≤ tb.size, (atAfter tb x i).1.size = i
  | 0, _ => rfl
  | i + 1, h => by
    rw [atAfter_succ tb x (by omega), atStep, Array.size_push, atAfter_size tb x i (by omega)]

theorem subspaceAtTable_eq (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    subspaceAtTable tb x = (atAfter tb x tb.size).1 := by
  rw [atAfter, List.take_of_length_le (by simp), Array.foldl_toList]
  rfl

theorem subspaceAtTable_size (tb : Array (UInt64 × UInt64)) (x : UInt64) :
    (subspaceAtTable tb x).size = tb.size := by
  rw [subspaceAtTable_eq, atAfter_size _ _ _ le_rfl]

end

end NativeRustcVm.Whir
