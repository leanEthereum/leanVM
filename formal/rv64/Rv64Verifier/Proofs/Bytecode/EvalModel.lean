import Rv64Verifier.Model.Bytecode

/-!
# `evaluateRust`, step by step

The mirror folds over slices (`(l.drop a).take (b - a)`); the code walks them an element at a
time. `take_drop_succ` extends a slice by its next element, so each loop's invariant is the fold
over the slice so far.
-/

namespace Rv64Verifier.Model
open LeanVM.Parameters

theorem take_drop_succ {α : Type} (l : List α) {a j : Nat} (ha : a ≤ j) (hj : j < l.length) :
    (l.drop a).take (j + 1 - a) = (l.drop a).take (j - a) ++ [l[j]] := by
  rw [show j + 1 - a = (j - a) + 1 by omega, List.take_add_one, List.getElem?_drop,
    show a + (j - a) = j by omega, List.getElem?_eq_getElem hj]
  rfl

theorem take_drop_self {α : Type} (l : List α) (a : Nat) : (l.drop a).take (a - a) = [] := by
  simp

/-- `memberSumRust` over one more position. -/
theorem memberSum_snoc (lowW : List E) (ps : List (BitVec 16)) (p : BitVec 16) :
    memberSumRust lowW (ps ++ [p]) = memberSumRust lowW ps + lowW.getD p.toNat 0 := by
  rw [memberSumRust, memberSumRust, List.foldl_append]
  rfl

/-- The initial state of `evaluate`'s loop. -/
def evalInit : EvalState := ⟨List.replicate 2048 0, 0, 0, 0, 0⟩

/-- The state after the first `i` blocks. -/
def evalAfter (bc : BytecodeRust) (lowW highW : List E) (i : Nat) : EvalState :=
  (bc.blocks.take i).foldl (blockStepRust bc lowW highW) evalInit

theorem evalAfter_succ (bc : BytecodeRust) (lowW highW : List E) {i : Nat}
    (hi : i < bc.blocks.length) :
    evalAfter bc lowW highW (i + 1) =
      blockStepRust bc lowW highW (evalAfter bc lowW highW i) bc.blocks[i] := by
  rw [evalAfter, evalAfter, List.take_succ_eq_append_getElem hi, List.foldl_append]
  rfl

theorem evalAfter_length (bc : BytecodeRust) (lowW highW : List E) :
    evalAfter bc lowW highW bc.blocks.length =
      bc.blocks.foldl (blockStepRust bc lowW highW) evalInit := by
  simp [evalAfter]

end Rv64Verifier.Model
