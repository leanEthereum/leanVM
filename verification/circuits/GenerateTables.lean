import LeanVMCircuits.Bus.TableEmit

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "usage: lake env lean --run GenerateTables.lean <destination.rs>")
  let generated ← match LeanVMCircuits.Bus.ClassTable.Emit.emit with
    | .ok generated => pure generated
    | .error reason => throw (IO.userError reason)
  IO.FS.writeFile destination generated
  let format ← IO.Process.output {
    cmd := "rustfmt", args := #["--edition", "2024", "--config-path", "../../rustfmt.toml", destination] }
  if format.exitCode != 0 then throw (IO.userError format.stderr)
