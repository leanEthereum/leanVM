import LeanVM.Guest.VcTactic
import LeanVM.Guest.Renumber

/-!
# The `vc` tactic's conditions

A function with every kind of statement and of atom, and the condition `vc` gives it, matched up
to reducible unfolding: a read of a defined value its word, a value an equation defines (a
constant, a copy, a product, the product a range check names, the inverse an assertion pins, a
`KECCAK`'s two written cells) substituted, a branch that falls through to the rest of its block
and a `match` split; and the same condition, `Expr.equal` to it, computed in chunks of one
statement, cut in the branches and the arms. Cut at every statement, a let-bound argument, tail of
the body or type, and a rule whose proof needs a let-variable's value, give the expected condition;
and cuts that would tell apart two terms of one word (so `vc` computes without generalizing) give
the same condition as no cuts. Under `keccak_cells_all_fn`, chained thirteen-cell `KECCAK`s keep
their written cells as words, each `KECCAK` one equation.
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

open Lean Meta Elab Tactic in
/-- Closes `P ↔ P'`, `P'` `Expr.equal` to `P` but for `rets'` in place of `rets`. -/
elab "same_cond" : tactic => withMainContext do
  let some (l, r) := (← getMainTarget).iff? | throwError "not an iff"
  unless l.equal (r.replaceFVar (← getFVarFromUserName `rets') (← getFVarFromUserName `rets)) do
    throwError "the chunked condition differs"
  evalTactic (← `(tactic| (subst_vars; exact Iff.rfl)))

example (C : CallRel) (rd : Reader) (p a : E) (rets rets' : List E) (h : rets = rets') :
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], body⟩ [p, a] rets ↔
      Fn.Sem C rd ⟨"t", [.n 0, .n 1], body⟩ [p, a] rets' := by
  set_option vc.chunkSize 1 in vc
  vc
  same_cond

noncomputable def chain : List Stmt := [.atom (.mul (.n 2) (.n 0) (.n 1)),
  .atom (.add (.n 3) (.n 2) (.n 1)), .atom (.add (.n 4) (.n 3) (.n 1)), .ret [.n 4]]

example (C : CallRel) (rd : Reader) (p a : E) (rets : List E) :
    let q := p * a
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], chain⟩ [q, a] rets ↔ [q * a + a + a] = rets := by
  intro q
  set_option vc.chunkSize 1 in vc
  with_reducible exact Iff.rfl

example (C : CallRel) (rd : Reader) (p a : E) (rets : List E) :
    let tl : List Stmt := [.atom (.add (.n 4) (.n 3) (.n 1)), .ret [.n 4]]
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], .atom (.mul (.n 2) (.n 0) (.n 1)) ::
      .atom (.add (.n 3) (.n 2) (.n 1)) :: tl⟩ [p, a] rets ↔ [p * a + a + a] = rets := by
  intro tl
  set_option vc.chunkSize 1 in vc
  with_reducible exact Iff.rfl

example (C : CallRel) (rd : Reader) (a : E) (rets : List E) :
    let T := E
    ∀ x : T, Fn.Sem C rd ⟨"t", [.n 0, .n 1], chain⟩ [x, a] rets ↔ [x * a + a + a] = rets := by
  intro T x
  set_option vc.chunkSize 1 in vc
  with_reducible exact Iff.rfl

example (C : CallRel) (rd : Reader) (p : E) (rets : List E) :
    let z : E := 0
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], [.atom (.mul (.n 2) (.n 0) (.n 1)),
      .atom (.mul (.n 3) (.n 0) (.n 1)), .ret [.n 3]]⟩ [p, z] rets ↔ [0] = rets := by
  intro z
  set_option vc.chunkSize 1 in vc [show p * z = 0 from mul_zero p]
  with_reducible exact Iff.rfl

noncomputable def twice : List Stmt := [.atom (.mul (.n 2) (.n 0) (.n 1)),
  .atom (.mul (.n 3) (.n 0) (.n 1)), .atom (.add (.n 4) (.n 2) (.n 3)), .ret [.n 4]]

/-- trace: [vc] cuts tell apart two terms of one word: computing without generalizing -/
#guard_msgs in
example (C : CallRel) (rd : Reader) (p a : E) (rets rets' : List E) (h : rets = rets') :
    Fn.Sem C rd ⟨"t", [.n 0, .n 1], twice⟩ [p, a] rets ↔
      Fn.Sem C rd ⟨"t", [.n 0, .n 1], twice⟩ [p, a] rets' := by
  set_option trace.vc true in set_option vc.chunkSize 1 in vc
  vc
  same_cond

noncomputable def sponge : List Stmt := [
  .atom (.keccak [.n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0, .n 0]
    [.n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13] false true),
  .atom (.add (.n 14) (.n 1) (.n 0)),
  .atom (.keccak [.n 14, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 12, .n 13]
    [.n 15, .n 16, .n 17, .n 18, .n 19, .n 20, .n 21, .n 22, .n 23, .n 24, .n 25, .n 26, .n 27]
    true false),
  .ret [.n 15]]

example (C : CallRel) (rd : Reader) (p : E) (rets : List E) :
    Fn.Sem C rd ⟨"t", [.n 0], sponge⟩ [p] rets ↔
      ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13,
        cells13 [x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13] =
          cellsOfState (keccakF1600 (stateOfCells (cells13 [p, p, p, p, p, p, p, p, p, p, p, p, p])
            false)) true ∧
        ∃ x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27,
          cells13 [x15, x16, x17, x18, x19, x20, x21, x22, x23, x24, x25, x26, x27] =
            cellsOfState (keccakF1600 (stateOfCells
              (cells13 [x1 + p, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13]) true)) false ∧
          [x15] = rets := by
  vc [-keccak_cells_all, keccak_cells_all_fn]
  with_reducible exact Iff.rfl

end LeanVMTests.Guest.Vc
