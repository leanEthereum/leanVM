import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Backend.Complete.Scoped

/-!
# `guest-cplframe`: the placement-side completeness hypotheses on the guest

Run from `lean_vm` as `lake exe guest-cplframe [--detail]`. No proof: compiled execution only.

For each function of the guest's traced input (`GuestInput.input`, as `guest-traced` makes it) it
decides `Complete.scopedB`, the hypothesis the placement-side completeness theorems take of a
traced function, and reports every function that fails it with the walk's reason.
-/

open LeanVM.Guest.Core LeanVM.Guest.Backend LeanVM.Guest.Backend.Complete
  LeanVM.Guest.Backend.GuestInput

/-- A value. -/
def vv (k : Nat) : V := ⟨[], 1, k⟩

/-- Traced functions placement accepts and `scopedB` must refuse: a value of one arm named after
the `match`, a second return area on a path, a return area past the return cells. -/
def counterexamples : List (String × TracedFn) :=
  let x := V.param 0
  let mk (name : String) (body : List Stmt) (trace : List Event) (rets : Nat) : TracedFn :=
    { core := { name, params := [x], body }, trace := trace.toArray, rets, loop := (false, none) }
  [("arm value after its match", mk "cx1"
      [.match_ x [[.atom (.const (vv 1) 0)], [.atom (.const (vv 2) 1)]],
       .atom (.mul (vv 3) (vv 1) (vv 1)), .ret []]
      [.enter, .alloc [vv 1] .cell, .emit, .leave, .enter, .alloc [vv 2] .cell, .emit, .leave, .emit,
       .alloc [vv 3] .cell, .emit, .emit] 0),
   ("two return areas on a path", mk "cx2"
      [.atom (.const (vv 1) 0), .atom (.const (vv 2) 1), .ret [vv 2]]
      [.alloc [vv 1] .ret, .emit, .alloc [vv 2] .ret, .emit, .emit] 1),
   ("a return area past the return cells", mk "cx3"
      [.atom (.const (vv 1) 0), .atom (.const (vv 2) 1), .ret []]
      [.alloc [vv 1, vv 2] .ret, .emit, .emit, .emit] 0)]

def main (args : List String) : IO UInt32 := do
  let detail := args.contains "--detail"
  if args.contains "--selftest" then
    let mut fails := 0
    for (what, tf) in counterexamples do
      let placed := match placeFn {} (sigTable [tf]) {} tf with
        | .ok _ => "placed"
        | .error e => s!"not placed ({e})"
      let sc := scopedB tf
      IO.println s!"{what}: {placed}, scopedB {sc}"
      if sc then fails := fails + 1
    return if fails == 0 then 0 else 1
  let P ← input
  let mut ok := 0
  let mut bad : Array String := #[]
  for tf in P do
    match scopedE tf with
    | .ok () => ok := ok + 1
    | .error e => bad := bad.push s!"{tf.core.name}: {e}"
  IO.println s!"scoped: {ok} of {P.length} functions"
  let shown := if detail then bad else bad.extract 0 40
  for b in shown do IO.println s!"  {b}"
  if bad.size > shown.size then IO.println s!"  ... {bad.size - shown.size} more (--detail)"
  return if bad.isEmpty then 0 else 1
