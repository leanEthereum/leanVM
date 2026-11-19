import NativeVm.Test.Wire

/-!
# `wire-test FIXTURE...`: the wire decoder on the verifier fixtures

For each fixture directory (`export-verifier-fixtures-rust.sh`), runs `NativeVm.Wire.decode` on its
`proof.wire` and on altered copies (`WireTest.variants`) and checks it against `Proof.fromBytes`
(`WireTest.compare`); exits nonzero on any difference.
-/

open NativeVm.Test.WireTest

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: wire-test FIXTURE..."
    return 2
  let mut failed := 0
  for dir in args do
    let bytes ← IO.FS.readBinFile (System.FilePath.mk dir / "proof.wire")
    let vs := variants bytes
    let mut ok := 0
    let mut rejected := 0
    for (name, b) in vs do
      match compare b with
      | none =>
        ok := ok + 1
        unless decodes b do rejected := rejected + 1
      | some err =>
        failed := failed + 1
        IO.println s!"{dir}: {name}: {err}"
    IO.println s!"{dir}: {ok}/{vs.length} agree ({rejected} rejected by both)"
  return if failed = 0 then 0 else 1
