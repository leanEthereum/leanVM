import NativeVm.Test.Phase7

/-!
# `vm-phase7-test`: phase 7's code on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`), or each directory given: the model up to phase 7,
then `phase7` against `phase7M`, honest, with a path digest of its first opening changed and with
its last scalar changed (`NativeVm.Test.Phase7Test`).
-/

def main (args : List String) : IO UInt32 := do
  let dirs ← match args with
    | [] =>
      let d := (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"
      pure ((← System.FilePath.readDir d).map (·.path) |>.qsort (·.toString < ·.toString)).toList
    | ds => pure (ds.map System.FilePath.mk)
  for d in dirs do
    let t0 ← IO.monoMsNow
    NativeVm.Test.Phase7Test.runDir d
    IO.println s!"  ({(← IO.monoMsNow) - t0} ms)"
  return 0
