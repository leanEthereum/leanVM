/-
  The input of `scripts/b2-locs`: for each entry of the guest's traced input named on the command
  line, the number of values each top-level statement of its body names, run with
  `lake env lean --run`.
-/
import LeanVM.Guest.Data.Source
import LeanVM.Guest.Backend.ExpandTrace
import LeanVM.Guest.Renumber

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend

def main (args : List String) : IO UInt32 := do
  match ExpandTrace.expandProgram Data.guest with
  | .error e => IO.eprintln e; return 1
  | .ok P =>
    let core := (P.map (·.core)).map Fn.renumber
    for a in args do
      let some j := a.toNat? | IO.eprintln s!"not an entry: {a}"; return 1
      let f := core.getD j default
      let ws := f.body.map fun s => (Stmt.valsList [s]).length + 1
      IO.println s!"entry {j} {f.name} {String.intercalate " " (ws.map toString)}"
    return 0
