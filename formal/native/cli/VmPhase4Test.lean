import NativeVm.Test.Phase4
import LeanVM.Cli.Common

/-!
# `vm-phase4-test`: phase 4's code on the verifier fixtures

For each fixture directory (`scripts/export-verifier-fixtures-rust.sh`) under the given directory
(default `$LEANVM_FIXTURES`, then `/tmp/vmfix`): the model up to phase 4, then phase 4's code
against `tablePhase` and `tableColumnClaims`, honest and with a scalar changed
(`NativeVm.Test.Phase4Test`).
-/

def main (args : List String) : IO UInt32 := do
  let dir ← match args with
    | [d] => pure (System.FilePath.mk d)
    | _ => return ← do
      let d := (← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix"
      let names := (← System.FilePath.readDir d).map (·.path) |>.qsort (·.toString < ·.toString)
      for n in names do NativeVm.Test.Phase4Test.runDir n
      return 0
  NativeVm.Test.Phase4Test.runDir dir
  return 0
