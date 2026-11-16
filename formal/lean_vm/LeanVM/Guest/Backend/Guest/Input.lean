/-
  LeanVM.Guest.Backend.Guest.Input

  The guest as the back end's input, computed: the traced expansion of the guest's source, every
  value renamed as `coreProgram` names it. `lake exe guest-traced` writes it out and
  `lake exe guest-pieces` writes the pieces of its compilation.
-/

module

public import LeanVM.Guest.Data.Source
public import LeanVM.Guest.Backend.Compile
public import LeanVM.Guest.Renumber

/-!
# The guest's traced input, computed

`input` is what `Backend/Guest/Traced.lean` denotes (`guestTraced`): the traced expansion of the
guest's source, each function's values renamed as `coreProgram` names them. A value of the core
function becomes its number in `Fn.renumber` (`V.n i`), and a value only the trace names (a cell no
statement reads) the next number past them, in the order the trace makes it.
-/

namespace LeanVM.Guest.Backend.GuestInput

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend

public section

/-- The renaming of function `f`'s values: its core values by `Fn.renumber`'s numbering, the
values only its trace names past them, in the trace's order. -/
def renamingOf (f : Fn) (trace : Array Event) : Std.HashMap V Nat := Id.run do
  let (m, t) := f.numbering
  let mut m := m
  let mut next := t.size
  for e in trace do
    let vs := match e with
      | .alloc vs _ => vs
      | .use v => [v]
      | .shift v _ => [v]
      | _ => []
    for v in vs do
      unless m.contains v do
        m := m.insert v next
        next := next + 1
  return m

/-- An event with its values renamed. -/
def renameEvent (r : V → V) : Event → Event
  | .alloc vs k => .alloc (vs.map r) k
  | .use v => .use (r v)
  | .shift v e => .shift (r v) e
  | e => e

/-- The guest's traced functions, renamed: the input `Backend/Guest/Traced.lean` denotes. -/
def renamed (P : List TracedFn) : List TracedFn :=
  P.map fun tf =>
    let m := renamingOf tf.core tf.trace
    let r : V → V := fun v => V.n (m.getD v 0)
    { tf with core := tf.core.renumber, trace := tf.trace.map (renameEvent r) }

/-- A result, or the error thrown. -/
def orThrow {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The traced input: the traced expansion renamed. Its core functions are `Expand.expandProgram`'s,
the same pass, renumbered as `guest-core` writes them. -/
def input : IO (List TracedFn) := do
  return renamed (← orThrow (Expand.expandProgramTraced Data.guest))

end
end LeanVM.Guest.Backend.GuestInput
