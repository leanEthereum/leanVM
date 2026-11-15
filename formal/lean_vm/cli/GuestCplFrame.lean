import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Backend.Complete.Scoped
import LeanVM.Guest.Backend.Complete.Cells

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
      [.alloc [vv 1, vv 2] .ret, .emit, .emit, .emit] 0),
   ("a range check temporary as a selector (scoped; frame words depend on it)", mk "cx4"
      [.atom (.rangeCheck x x (vv 1) (vv 2) x),
       .match_ (vv 1) [[.atom (.const (vv 3) 1)], [.atom (.const (vv 4) 2)]], .ret []]
      [.alloc [vv 1] .cell, .alloc [vv 2] .cell, .emit, .enter, .alloc [vv 3] .pooled, .emit, .leave,
       .enter, .alloc [vv 4] .pooled, .emit, .leave, .emit, .emit] 0)]

/-- Whether a body calls the function `f` by a `call` or a `dispatch`, at any depth. -/
partial def callsSelf (f : String) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with
      | .call g _ _ => g == f
      | .dispatch _ gs _ _ => gs.contains f
      | .ite _ z n => callsSelf f z || callsSelf f n
      | .match_ _ arms => arms.any (callsSelf f)
      | _ => false) || callsSelf f ss

def main (args : List String) : IO UInt32 := do
  let detail := args.contains "--detail"
  if args.contains "--selftest" then
    let mut fails := 0
    for (what, tf) in counterexamples do
      let placed := match placeFn {} (sigTable [tf]) {} tf with
        | .ok (pf, _) =>
          let cells := (List.range 4).filterMap fun k => match pf.locs[vv k]? with
            | some (.cell c) => some s!"v{k}@{c}"
            | _ => none
          s!"placed (frame size {pf.fn.frameSize}, cells {cells})"
        | .error e => s!"not placed ({e})"
      let sc := scopedB tf
      let ta := match placeFn {} (sigTable [tf]) {} tf with
        | .ok (pf, _) => tmpsApartB tf pf
        | .error _ => false
      IO.println s!"{what}: {placed}, scopedB {sc}, tmpsApartB {ta}"
      if sc && ta then fails := fails + 1
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
  let (pls, _) ← orThrow (placeProgram P)
  let mut okT := 0
  let mut badT : Array String := #[]
  let mut ntmps := 0
  for (pf, tf) in pls.zip P do
    ntmps := ntmps + (LeanVM.Guest.Memory.Stmt.tmpsList tf.core.body).length
    if tmpsApartB tf pf then okT := okT + 1
    else badT := badT.push tf.core.name
  IO.println s!"temporaries apart: {okT} of {pls.length} functions ({ntmps} temporaries)"
  let selfCallers := P.filter fun tf => callsSelf tf.core.name tf.core.body
  IO.println s!"functions calling themselves by call or dispatch: {selfCallers.length}"
  let nsc := (P.filter noSelfCallB).length
  IO.println s!"noSelfCallB: {nsc} of {P.length} functions"
  for b in (if detail then badT else badT.extract 0 40) do IO.println s!"  {b}"
  return if bad.isEmpty && badT.isEmpty then 0 else 1
