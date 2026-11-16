import LeanVM.Guest.Backend.Guest.Input
import LeanVM.Guest.Backend.Guest.Cpl.Static
import LeanVM.Guest.Data.NameStrings

/-!
# `guest-tables`: the back end's tables of the guest

Places the guest (the back end's input as `guest-traced` makes it, `GuestInput.input`) natively and
writes, by compiled function index `j` (`j = i + 1` for entry `i` of the input, `0` for
`__jump_tables`):

* `LeanVM/Guest/Deployed/Data.lean`: the frame sizes (`placeProgram`'s `frameSize`; `main`'s
  without the jump tables), `mainCells` (`main`'s frame size, where the jump tables start),
  `jtSlots` (the jump tables' slots, `guestSlots.size`), the path maxima
  (`Complete.ofCnt (Complete.pmaxP keyed pf)`), the function whose `match`es count their arms
  separately (`armFn`, `main_loop2`'s index), its arms (`Complete.armsP true`) and the most a path
  through its body passes of them (`armMax`);
* with `--decoder-inputs FILE`, the input of `scripts/decoder-tables`: each function's return words,
  whether it is a registered loop helper, and its place codes, one per value index (`placeCode`).

`lake exe guest-tables [--check]` writes `Deployed/Data.lean`, or with `--check` writes nothing and
fails when it differs.
-/

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend LeanVM.Guest.Backend.GuestInput

namespace GuestTables

def outPath : System.FilePath := "LeanVM/Guest/Deployed/Data.lean"

/-- The function whose `match`es count their arms separately. -/
def armedName : String := Data.N.«main_loop2»

/-- A place as one natural: the cell `n` as `n`, the cell `n` shifted by `g^e` as
`n + 2^20 * (e + 1)`; `none` past the cells a code holds. -/
def placeCode : Loc → Option Nat
  | .cell n => if n < 2 ^ 20 then some n else none
  | .shifted n e => if n < 2 ^ 20 then some (n + 2 ^ 20 * (e + 1)) else none

/-- Entry `tf`'s place codes, one per value of its core function (`V.n k` for `k` below their
number, `Fn.numbering`), `none` for a value of no place. Fails on a place past the codes. -/
def placeRow (tf : TracedFn) (pf : Placed) : Except String (List (Option Nat)) :=
  (List.range tf.core.numbering.2.size).mapM fun k =>
    match pf.locs[V.n k]? with
    | none => pure none
    | some l => match placeCode l with
      | some c => pure (some c)
      | none => throw s!"{pf.fn.name}: value {k}'s place has no code"

/-- The most a path through `ss` passes of the separately counted arms `acs`, at opcode `k`
(`Deployed.costMaxW`). -/
partial def armMaxW (acs : List (Nat × List (List Nat))) (k : Nat) : List Stmt → Nat
  | [] => 0
  | .ite _ z n :: ss => max (armMaxW acs k z) (armMaxW acs k n) + armMaxW acs k ss
  | .match_ x arms :: ss =>
    let key := match acs.find? (·.1 == x.idx) with
      | some (_, cs) => cs.foldr (fun l m => max (l.getD k 0) m) 0
      | none => 0
    key + arms.foldr (fun a m => max (armMaxW acs k a) m) 0 + armMaxW acs k ss
  | _ :: ss => armMaxW acs k ss

/-- The back end's tables, by compiled function index. -/
structure Out where
  frameSizes : List Nat
  mainCells : Nat
  jtSlots : Nat
  pmax : List (List Nat)
  armFn : Nat
  armMax : List Nat
  arms : List (List (Nat × List (List Nat)))
  rets : List Nat
  registered : List Bool
  /-- The place codes, `none` for a value of no place (`0` in the table). -/
  places : List (List (Option Nat))

def tablesOf (P : List TracedFn) : Except String Out := do
  let (pls, tables) ← placeProgram P
  unless pls.length == P.length do throw "not every function placed"
  let loops := loopTable P
  let armed := (P.zipIdx.filter (·.1.core.name == armedName)).map (·.2 + 1)
  let armFn := armed.headD 0
  let pairs := P.zip pls
  let arms := (List.range (pairs.length + 1)).map fun j =>
    if j == armFn && j != 0 then
      match pairs[j - 1]? with
      | some (tf, pf) => Complete.armsP true tf pf
      | none => []
    else []
  let armRow := arms.getD armFn []
  let armMax := if armFn == 0 then List.replicate 6 0 else
    (List.range 6).map fun k => armMaxW armRow k ((P.getD (armFn - 1) default).core.body)
  let places ← pairs.mapM fun (tf, pf) => placeRow tf pf
  return {
    frameSizes := 0 :: pls.map (·.fn.frameSize)
    mainCells := ((pls.head?).map (·.fn.frameSize)).getD 0
    jtSlots := tables.len
    pmax := [] :: pairs.zipIdx.map fun ((_, pf), i) =>
      Complete.ofCnt (Complete.pmaxP (i + 1 == armFn) pf)
    armFn, armMax
    arms := arms.take (if armFn == 0 then 0 else armFn + 1)
    rets := 0 :: P.map (·.rets)
    registered := false :: P.map fun tf => ((loops[tf.core.name]?).any (·.registered))
    places := [] :: places }

/-- The place codes as the table holds them. -/
def Out.placeCodes (o : Out) : List (List Nat) := o.places.map (·.map (·.getD 0))

/-! ## The module -/

def listText (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"

def natsText (l : List Nat) : String := listText (l.map toString)

def dataText (o : Out) : String :=
  let armDefs := String.join ((o.arms.getD o.armFn []).zipIdx.map fun ((_, cs), k) =>
    s!"/-- Function {o.armFn}'s counted `match` {k}: its arms' counts. -/\ndef arms{o.armFn}_{k} : List (List Nat) :=\n  (" ++
      " ::\n    ".intercalate (cs.map natsText) ++ " :: [])\n\n")
  let armRow (r : List (Nat × List (List Nat))) (j : Nat) : String :=
    listText (r.zipIdx.map fun ((x, _), k) => s!"({x}, arms{j}_{k})")
  "/-\n  LeanVM.Guest.Deployed.Data\n\n  Generated by `lake exe guest-tables` (lean_vm/cli/GuestTables.lean); do not edit.\n" ++
  "  The back end's tables of the guest, by compiled function index.\n-/\n\nmodule\n\n" ++
  "/-!\nThe guest placed by the back end (`placeProgram guestTraced`), by compiled function index `j`:\n" ++
  "function `j` is entry `j - 1` of the back end's input, `0` is `__jump_tables`, which has no frame\n" ++
  "of its own (it runs in `main`'s).\n-/\n\n" ++
  "namespace LeanVM.Guest.Deployed.Data\n\nset_option maxRecDepth 100000\n\n@[expose] public section\n\n" ++
  "/-- Frame sizes by compiled function index: the back end's frame size of each function, `main`'s\n" ++
  "without the jump tables. -/\n" ++
  s!"def frameSizes : List Nat := {natsText o.frameSizes}\n\n" ++
  "/-- `main`'s cells, below the jump tables' slots. -/\n" ++
  s!"abbrev mainCells : Nat := {o.mainCells}\n\n" ++
  "/-- The jump tables' slots (`guestSlots.size`). -/\n" ++
  s!"abbrev jtSlots : Nat := {o.jtSlots}\n\n" ++
  "/-- The most instructions of each opcode (in the order of `Opcode`) a path through each function's\n" ++
  "body runs, its callees apart, by compiled function index (`Complete.pmaxP`), the arms of\n" ++
  "`armFn`'s `match`es counted apart. -/\n" ++
  "def pmax : List (List Nat) := [\n  " ++ ",\n  ".intercalate (o.pmax.map natsText) ++ "]\n\n" ++
  "/-- The function whose `match`es count their arms separately (`0`: none). -/\n" ++
  s!"def armFn : Nat := {o.armFn}\n\n" ++
  "/-- The most a path through its body passes of those arms, per opcode, in the order of `Opcode`. -/\n" ++
  s!"def armMax : List Nat := {natsText o.armMax}\n\n" ++
  armDefs ++
  "/-- The per-arm counts, by function (`Complete.armsP`): function `j`'s entry is a list of\n" ++
  "`(x, costs)`, the `match` on value `x` with arm `k` at most `costs[k]` instructions of each opcode\n" ++
  "from its segment to the join, the callees' apart. -/\n" ++
  "def arms : List (List (Nat × List (List Nat))) := " ++
  (if o.arms.isEmpty then "[]" else
    "[\n  " ++ ",\n  ".intercalate (o.arms.zipIdx.map fun (r, j) => armRow r j) ++ "]") ++
  "\n\nend\nend LeanVM.Guest.Deployed.Data\n"

def decoderText (o : Out) : String :=
  "rets " ++ " ".intercalate (o.rets.map toString) ++ "\n" ++
  "registered " ++ " ".intercalate (o.registered.map fun b => if b then "1" else "0") ++ "\n" ++
  String.join (o.placeCodes.zipIdx.map fun (r, j) =>
    s!"row {j}" ++ String.join (r.map (s!" {·}")) ++ "\n")

end GuestTables

open GuestTables in
def main (args : List String) : IO UInt32 := do
  let P ← input
  let o ← orThrow (tablesOf P)
  match args with
  | ["--decoder-inputs", path] =>
      IO.FS.writeFile path (decoderText o)
      IO.println s!"{o.places.length} functions -> {path}"
      return 0
  | [] | ["--check"] =>
      let text := dataText o
      if args.contains "--check" then
        if !(← outPath.pathExists) || (← IO.FS.readFile outPath) != text then
          IO.eprintln s!"{outPath} is stale: run lake exe guest-tables"
          return 1
      else
        if let some d := outPath.parent then IO.FS.createDirAll d
        IO.FS.writeFile outPath text
      IO.println s!"{outPath}: {o.frameSizes.length} functions, main's cells {o.mainCells}, {o.jtSlots} slots, arms of function {o.armFn}"
      return 0
  | _ =>
      IO.eprintln "usage: guest-tables [--check] | --decoder-inputs FILE"
      return 2
