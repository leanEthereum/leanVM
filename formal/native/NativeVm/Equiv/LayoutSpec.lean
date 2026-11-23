module

public import NativeVm.Equiv.Form
public import NativeVm.Model.Claims

/-!
# The layout and the claims: the model's words as the statement's values

`LayoutW.toSpec` reads a model layout (`LayoutW`, `NativeVm/Model/Layout.lean`) as the statement's
`Layout`: the bytecode's lanes as `K`, the bus blocks through `BusBlockW.toSpec`, the arrays as
lists. `ColumnClaimW.toSpec` reads a column claim the same way. A stack claim's weight is data in
the model (`StackWeight`) and a function in the statement; `StackWeight.Rel w f` says `w` evaluates
as `f` at every point of words, and `StackClaimW.Rel` adds the value.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- A layout as the statement's `Layout`. -/
def LayoutW.toSpec (l : LayoutW) : Layout :=
  ⟨l.logMemory, l.logBytecode, l.bytecode.toList.map K.ofLane, l.push.toList.map BusBlockW.toSpec,
    l.pull.toList.map BusBlockW.toSpec, l.count.toList.map BusBlockW.toSpec, l.placements.toList,
    l.stackLog, l.tableLogHeights.toList⟩

/-- A column claim as the statement's `ColumnClaim`. -/
def ColumnClaimW.toSpec (c : ColumnClaimW) : ColumnClaim :=
  ⟨c.column, c.point.toList.map EW.toE, c.value.toE⟩

/-- A weight evaluates as the statement's function at every point of words. -/
def StackWeight.Rel (w : StackWeight) (f : List E → E) : Prop :=
  ∀ x : Array EW, (w.eval x).toE = f (x.toList.map EW.toE)

/-- A stack claim is the statement's: its weight evaluates as the function, its value is the
value. -/
def StackClaimW.Rel (c : StackClaimW) (s : StackClaim) : Prop :=
  c.weight.Rel s.1 ∧ c.value.toE = s.2

end NativeVm.Model
