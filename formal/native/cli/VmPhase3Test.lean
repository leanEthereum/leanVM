import NativeVm.Test.Phase3

/-!
# `vm-phase3-test`: phase 3's code on the verifier fixtures

For the given fixture directory (`scripts/export-verifier-fixtures-rust.sh`), or each one under the
given directory (default `$LEANVM_FIXTURES`, then `/tmp/vmfix`): the model up to phase 3, then
`P3.code` against `verifyBusBalance`, honest and with a scalar changed (`NativeVm.Test.Phase3Test`).
-/

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath ← match args with
    | [d] => pure d
    | _ => pure ((← IO.getEnv "LEANVM_FIXTURES").getD "/tmp/vmfix")
  let dirs ← if ← (root / "stream.bin").pathExists then pure [root] else
    pure ((← root.readDir).map (·.path) |>.qsort (·.toString < ·.toString)).toList
  for d in dirs do NativeVm.Test.Phase3Test.t3_runDir d
  return 0
