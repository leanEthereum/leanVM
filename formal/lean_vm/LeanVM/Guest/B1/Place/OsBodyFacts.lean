/-
  LeanVM.Guest.B1.Place.OsBodyFacts

  The facts of `open_stacked`'s body the placed lift (`os_completeAt_placeJ`) needs.
-/

module

public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Whir.Flatness

/-!
# `open_stacked`'s body, its placed facts

`osBodyA_straight`: the body before its `ret` is straight-line (it is flat, `osBodyA_flat`).
`OsBodyFacts c`: it has no `frameAddr`, decided per configuration (`osBodyFacts_of`, by kernel
evaluation of `osBodyFactsB c`). Its calls and `HeapBuf` hints are `filterMap`s over the same
statements (`Main.Stmt.callS`, `Main.Stmt.allocSz`), read off per configuration by the assembly.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1.Whir

@[expose] public section

theorem osBodyA_straight (c : OsCfg) : (osBodyA c).all Main.Stmt.straight = true :=
  straight_of_flat _ (osBodyA_flat c)

/-- `open_stacked`'s body, checked: no `frameAddr` before its `ret`. -/
def osBodyFactsB (c : OsCfg) : Bool := decide ((osBodyA c).filterMap Main.Stmt.addrS = [])

/-- `open_stacked`'s body has no `frameAddr`. -/
structure OsBodyFacts (c : OsCfg) : Prop where
  addrs : (osBodyA c).filterMap Main.Stmt.addrS = []

theorem osBodyFacts_of {c : OsCfg} (h : osBodyFactsB c = true) : OsBodyFacts c := by
  unfold osBodyFactsB at h
  exact ⟨of_decide_eq_true h⟩

end
end LeanVM.Guest.B1
