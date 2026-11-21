import NativeVm.Test.Phase25

/-!
# `vm-phase25-test`: phases 2 and 5's code on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`): the model up to phase 2 and up to phase 5, then
`phase2` against `phase2M` and `phase5` against `publicInputPhase`, honest and mutated
(`NativeVm.Test.Phase25Test`).
-/

def main (args : List String) : IO UInt32 := do
  let dirs ← match args with
    | [] =>
      let d := (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"
      pure ((← System.FilePath.readDir d).map (·.path) |>.qsort (·.toString < ·.toString)).toList
    | ds => pure (ds.map System.FilePath.mk)
  for d in dirs do NativeVm.Test.Phase25Test.runDir d
  return 0
