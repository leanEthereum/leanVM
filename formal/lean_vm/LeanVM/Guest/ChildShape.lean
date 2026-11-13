/-
  LeanVM.Guest.ChildShape

  A child's announced stack log and rate: which of the guest's opening arms its `verify_sub`
  dispatches to, the parameter a child's share of the budget depends on.
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Facts.Guest
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Protocol.Verifier

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

theorem childShape_of {bytecode : List K} {c : Child} {layout : Layout} {r : ℕ}
    (h : announcedLayoutAndRate bytecode c.proof.stream = some (layout, r)) :
    childShape bytecode c = (layout.stackLog, r) := by
  unfold childShape; rw [h]

end
end LeanVM.Guest
