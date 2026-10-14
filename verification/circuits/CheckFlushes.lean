import LeanVMCircuits.Bus.TableFlushes

/-!
`lake exe checkflushes <dump>` checks the instruction table dump written as `table-flushes.dump` by the `circuits` CLI behind `circuit-trace`. Column layouts and ordered tuples now come from this Lean source; the remaining native `ClassSpec` slot lists and `Columns::column` clock-port projection are checked here. The dump must agree line for line with `LeanVMCircuits.Bus.ClassTable.dump`; no pinned Rust copy is maintained.
-/

open LeanVMCircuits.Bus.ClassTable

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: checkflushes <dump>"
      return 2
  let lines := (← IO.FS.lines path).toList
  if lines == dump then
    IO.println s!"{path}: the {all.length} tables' flushes ({dump.length} lines) are the model's"
    return 0
  let i := ((lines.zip dump).findIdx? fun (a, b) => a != b).getD (min lines.length dump.length)
  IO.eprintln s!"{path}: line {i + 1} is `{lines.getD i "<end>"}`, the model's is `{dump.getD i "<end>"}`"
  return 1
