import LeanVMTests.Spec.NodeVectors

/-!
# `node-vectors`: the Rust vectors' costly checks, compiled

`lake exe node-vectors` checks the parts of `tests/LeanVMTests/Spec/NodeVectors.lean` that are
slow in the interpreter: the batching of the two children's claims (and that a hint off by one
makes it fail), `matrixValues` at the claims' points, and the DA roots' vector digests. The other
vectors are `#guard`s of `LeanVMTests.Spec.Node`. The exit code is `0` when every check passes.
-/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Node LeanVMTests.Spec

/-- The checks, each by name. -/
def checks : List (String × (Unit → Bool)) := [
  ("batch", fun _ ↦ (batch NodeVectors.children NodeVectors.hints).map DeferredClaim.cells ==
    some NodeVectors.batched.cells),
  ("batch, a bytecode value one off", fun _ ↦ (batch NodeVectors.children
    { NodeVectors.hints with bytecodeValue := NodeVectors.hints.bytecodeValue + 1 }).isNone),
  ("matrixValues", fun _ ↦ (NodeVectors.children.map (·.carried) ++ [NodeVectors.batched]).all
    fun c ↦ matrixValues c.matrixPoint == (c.matrixA, c.matrixB)),
  ("vectorDigest", fun _ ↦ NodeVectors.daRoots.map LeanVM.Da.vectorDigestOf ==
    NodeVectors.daVectorDigests.map LeanVM.Da.toBytes)]

/-- The driver. -/
def main : IO UInt32 := do
  let mut failed := false
  for (name, check) in checks do
    let ok := check ()
    IO.println s!"{name}: {if ok then "ok" else "FAILED"}"
    failed := failed || !ok
  return if failed then 1 else 0
