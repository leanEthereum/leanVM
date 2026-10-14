import LeanVMCircuits.Rec.Emit

def main (args : List String) : IO Unit := do
  let [destination] := args | throw (IO.userError "usage: lake env lean --run GenerateRec.lean <destination.rs>")
  IO.FS.writeFile destination LeanVMCircuits.Rec.Emit.emit
  let format ← IO.Process.output {
    cmd := "rustfmt", args := #["--config-path", "../../rustfmt.toml", destination] }
  if format.exitCode != 0 then throw (IO.userError format.stderr)
