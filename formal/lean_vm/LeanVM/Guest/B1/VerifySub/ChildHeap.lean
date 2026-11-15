/-
  LeanVM.Guest.B1.VerifySub.ChildHeap

  A child's advised sizes: `verify_sub`'s `zeta` buffer of the bus depth and `verify_tables`' three round
  buffers.
-/

module

public import LeanVM.Guest.Hints
-- Private: `guest_const%` inserts literals.
import LeanVM.Guest.Data.Source

/-!
# A child's advised sizes

`childHeapH bytecode c`: the `heap_sizes` entries of a child, `Hints.childHints`' first four, none without an
announced layout.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **A child's advised sizes** (`Hints.childHints`' first four entries): `verify_sub`'s `zeta` buffer of the bus
depth and `verify_tables`' three round buffers, none without an announced layout. -/
def childHeapH (bytecode : List K) (c : Child) : List (List E) :=
  match announcedLayoutAndRate bytecode c.proof.stream with
  | none => []
  | some (layout, _) =>
    let rounds := layout.tableLogHeights.foldl max 0
    [(busLayout [0, layout.logMemory, layout.logBytecode] layout.push).depth,
      (rounds + 1) * guest_const% ROUND_SLOTS, rounds + 1, rounds + 1].map fun n => [Hints.count n]

end

end LeanVM.Guest.B1.VerifySub
