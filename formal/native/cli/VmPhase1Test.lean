import NativeVm.Test.Phase1

/-!
# `vm-phase1-test`: phase 1's code on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`): `phase1` against `readAnnouncedSizes` from the
state after the seed, honest and mutated (`NativeVm.Test.Phase1Test`).
-/

def main (args : List String) : IO UInt32 := do
  let dirs ← match args with
    | [] =>
      let d := (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"
      pure ((← System.FilePath.readDir d).map (·.path) |>.qsort (·.toString < ·.toString)).toList
    | ds => pure (ds.map System.FilePath.mk)
  for d in dirs do NativeVm.Test.Phase1Test.runDir d
  return 0
