import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Backend.Guest.Cpl.Static
import LeanVM.Guest.Data.FrameSizes
import LeanVM.Guest.Data.CplArms

/-!
# `guest-cplguest`: the per-function checks of the guest's completeness instance

Run from `lean_vm` through `python3 -I scripts/cpl-guest`, which has `scripts/cpl-crosscheck` write
the certificate tables as text (`.lake/cpl-crosscheck-tables.txt`, for the path maxima `pmax`) and
runs `lake exe guest-cplguest FILE [--detail]`. No proof: compiled execution only, the test of
what `Guest/Cpl/Eval/` then has the kernel decide.

The guest is the back end's input as `guest-traced` makes it (`GuestInput.input`), placed
(`placeProgram`). For each function, entry `i` (function `i + 1`):

1. `Cpl.staticOk` against the frame size `Cpl.fsWant i` (frame size, loop name, self cell,
   parameters' and returns' cells, temporaries, frame runs);
2. `Complete.pmaxP keyed` against the table's `pmax`, `keyed` when `Data.cplArms` counts the
   function's arms separately;
3. `Complete.armsP keyed` against `Data.cplArms`;
4. `Complete.scopedB`;
5. `Complete.tmpsApartB`.
-/

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend LeanVM.Guest.Backend.GuestInput

namespace GuestCplGuest

/-- The `pmax` of each function of the tables text, by function index. -/
def pmaxOf (text : String) : Std.HashMap Nat (List Nat) := Id.run do
  let mut m : Std.HashMap Nat (List Nat) := {}
  let mut cur : Option Nat := none
  for line in text.splitOn "\n" do
    match line.splitOn " " with
    | "F" :: j :: _ => cur := j.toNat?
    | "M" :: rest =>
        if let some j := cur then m := m.insert j (rest.filterMap String.toNat?)
    | _ => pure ()
  return m

/-- The frame size of entry `i` in the completeness instance (`Cpl.fsWant`). -/
def fsWantE (i : Nat) : Nat :=
  if i = 0 then Data.mainCells else max 2 (Data.frameSizes.getD (i + 1) 0)

end GuestCplGuest

open GuestCplGuest in
def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: guest-cplguest TABLES [--detail]"; return 2
  let detail := args.contains "--detail"
  let pm := pmaxOf (← IO.FS.readFile path)
  let P ← input
  let (pls, _) ← orThrow (placeProgram P)
  let loops := loopTable P
  let names := ["static", "pmax", "arms", "scoped", "tmpsApart"]
  let mut ok : Array Nat := #[0, 0, 0, 0, 0]
  let mut bad : Array String := #[]
  for (tf, i) in P.zipIdx do
    let some pf := pls[i]? | bad := bad.push s!"{i} {tf.core.name}: not placed"
    let arms := Data.cplArms.getD (i + 1) []
    let keyed := !arms.isEmpty
    let mine := Complete.ofCnt (Complete.pmaxP keyed pf)
    let theirs := (pm.get? (i + 1)).getD []
    let r := [Cpl.staticOk loops tf pf (fsWantE i), mine == theirs,
      Complete.armsP keyed tf pf == arms, Complete.scopedB tf, Complete.tmpsApartB tf pf]
    for (b, k) in r.zipIdx do
      if b then ok := ok.modify k (· + 1)
      else
        let what := if k == 1 then s!" (back end {mine}, table {theirs})" else ""
        bad := bad.push s!"{i} {tf.core.name}: {names.getD k ""}{what}"
  for (n, k) in names.zipIdx do
    IO.println s!"{n}: {ok.getD k 0} of {P.length}"
  let shown := if detail then bad else bad.extract 0 40
  for b in shown do IO.println s!"  {b}"
  if bad.size > shown.size then IO.println s!"  ... {bad.size - shown.size} more (--detail)"
  return if bad.isEmpty then 0 else 1
