import LeanVM.Guest.VcTactic
import LeanVM.Guest.Renumber

/-!
# The `vc` tactic's conditions

A function with every kind of statement and of atom, and the condition `vc` gives it, matched up
to reducible unfolding: a read of a defined value its word, a value an equation defines (a
constant, a copy, a product, the product a range check names, the inverse an assertion pins, a
`KECCAK`'s two written cells) substituted, a branch that falls through to the rest of its block
and a `match` split.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

namespace LeanVMTests.Guest.Vc

noncomputable def body : List Stmt := [
  .atom (.load (.n 2) (.n 0) 0),
  .atom (.const (.n 3) (word 1 0)),
  .atom (.copy (.n 4) (.n 2)),
  .atom (.assertEq (.n 4) (.n 1)),
  .call "g" [.n 2, .n 1] [.n 5],
  .atom (.hint (.inverse (.n 5) (.n 6))),
  .atom (.assertNe (.n 5) (.n 6) (.n 7)),
  .atom (.rangeCheck (.n 2) (.n 6) (.n 8) (.n 9) (.n 10)),
  .atom (.assertInK (.n 2) (.n 3)),
  .atom (.frameAddr (.n 11) [.n 2, .n 5]),
  .atom (.touch (.n 12) (.n 11)),
  .atom (.keccak [.n 2, .n 3, .n 2, .n 3, .n 2, .n 3, .n 2, .n 3, .n 2, .n 3, .n 2, .n 3, .n 1]
    [.n 13, .n 14] false false),
  .callIf (.n 13) "loop" [.n 2],
  .dispatch (.n 14) ["f0", "f1"] [.n 2] [.n 15],
  .ite (.n 5) [.atom (.const (.n 16) 0)] [.atom (.mul (.n 16) (.n 5) (.n 6))],
  .match_ (.n 2) [[.ret [.n 16]], [.atom (.add (.n 17) (.n 16) (.n 1)), .ret [.n 17, .n 15]]]]

example (C : CallRel) (rd : Reader) (p a : E) (rets : List E) :
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], body⟩ [p, a] rets ↔
      ∃ x2, LoadHolds rd p 0 x2 ∧ x2 + a = 0 ∧ ∃ x5, C "g" [x2, a] [x5] ∧ ∃ x6, x5 * x6 = 1 ∧
        ∃ x8, LoadHolds rd x2 0 x8 ∧ ∃ x9, LoadHolds rd x6 0 x9 ∧ IsInK x2 ∧ IsInK (word 1 0) ∧
          ∃ x11, IsInK x11 ∧
            (∀ k < 2, ∀ w, rd (x11.limb 0 * addressOfIndex k) = some w → w = [x2, x5].getD k 0) ∧
            ∃ x12, LoadHolds rd x11 0 x12 ∧
              let S := keccakF1600 (stateOfCells (cells13 [x2, word 1 0, x2, word 1 0, x2,
                word 1 0, x2, word 1 0, x2, word 1 0, x2, word 1 0, a]) false)
              IsInK (cellsOfState S false 0) ∧ (cellsOfState S false 0 ≠ 0 → C "loop" [x2] []) ∧
              ∃ x15, (∃ j, cellsOfState S false 1 = ofK (addressOfIndex j) ∧
                  ∃ (_ : j < 2), C ["f0", "f1"][j] [x2] [x15]) ∧ IsInK x5 ∧
                (x5 = 0 → x2 = ofK (addressOfIndex 0) ∧ [0] = rets ∨
                  x2 = ofK (addressOfIndex 1) ∧ [0 + a, x15] = rets) ∧
                (x5 ≠ 0 → x2 = ofK (addressOfIndex 0) ∧ [x5 * x6] = rets ∨
                  x2 = ofK (addressOfIndex 1) ∧ [x5 * x6 + a, x15] = rets) := by
  vc
  with_reducible exact Iff.rfl

end LeanVMTests.Guest.Vc
