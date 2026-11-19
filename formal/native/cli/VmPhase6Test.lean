import NativeVm.Test.Phase6

/-!
# `vm-phase6-test`: phase 6's code on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`), or each directory given: the model up to phase 6,
then `phase6` against `keccakPhase`, honest and with a scalar changed (`NativeVm.Test.Phase6Test`).
-/

def main (args : List String) : IO UInt32 := do
  let dirs ← match args with
    | [] =>
      let d := (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"
      pure ((← System.FilePath.readDir d).map (·.path) |>.qsort (·.toString < ·.toString)).toList
    | ds => pure (ds.map System.FilePath.mk)
  for d in dirs do NativeVm.Test.Phase6Test.runDir d
  return 0
