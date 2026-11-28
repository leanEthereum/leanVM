import LeanVM.Guest.Bytecode
import LeanVM.Facts.DaWith
import LeanVMTests.Guest.Manifest
import LeanVMTests.Spec.NodeVectors

/-!
# `node-vectors`: the Rust vectors' costly checks, compiled

`lake exe node-vectors` checks what is slow in the interpreter, of the data
`scripts/guest-export` writes from the deployed Rust:

* the seed of the node vectors (`NodeVectors.seed`) and the guest's Fiat-Shamir IV the Rust
  reports (`Manifest.fsSeed`, `fs_seed`) are `deployedSeed guestProgram`, the Keccak-256 IV of the assembled
  guest's `2^23` bytecode words: so the Lean `guestProgram` is the bytecode the Rust proves, every
  instruction (it is evaluated as `guestArray`, the same program, `guestArray_eq`);
* the DA root's membership challenge is the Rust's (`LeanVM.Da.membershipChallengeOf`);
* the guest's split table (`splitEntry`, `split_table`) is the Rust's: its first entry is a leaf's
  deferred value (`DeferredBytecodeClaim::leaf`), and its entries at the first instruction of each
  opcode and at the last are the split columns there (`FreshClaim::at` at those vertices of the
  instructions' cube). `splitValues` and `splitTable` at points off the cube, which the batching
  relates, are pinned on a small program by `LeanVMTests.Spec.Node`: summing over every
  instruction of the guest is too slow in the Statement's list form.

The other vectors are `#guard`s of `LeanVMTests.Spec.Node`. The exit code is `0` when every check
passes.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest LeanVMTests

/-- The guest's seed, evaluated once. -/
def guestSeed : Digest := deployedSeed guestArray

example : guestSeed = deployedSeed guestProgram := by rw [guestSeed, guestArray_eq]

/-- The guest's stacked bytecode, evaluated once. -/
def guestWords : List K := LeanVM.bytecodeWords guestArray

/-- `Manifest.fsSeed`, two cells, as a digest. -/
def manifestSeed : Option Digest :=
  match Guest.Manifest.fsSeed with
  | [(a0, a1), (b0, b1)] =>
      some #v[UInt64.ofNat a0, UInt64.ofNat a1, UInt64.ofNat b0, UInt64.ofNat b1]
  | _ => none

/-- The checks, each by name. -/
def checks : List (String × (Unit → Bool)) := [
  ("seed: the vectors' seed is deployedSeed guestProgram", fun _ ↦ guestSeed == Spec.NodeVectors.seed),
  ("seed: the manifest's fs_seed is deployedSeed guestProgram", fun _ ↦ manifestSeed == some guestSeed),
  ("membershipChallenge: the DA root's membership challenge is the Rust's", fun _ ↦
    let c := Spec.NodeVectors.daClaim
    LeanVM.Da.membershipChallengeOf c.daRoot == c.membershipChallenge),
  ("splitEntry: the split table's first entry is the leaf's deferred value", fun _ ↦
    ofK (splitEntry guestWords 0 0) == Spec.NodeVectors.leafValue),
  ("splitEntry: the split table's entries at instructions are the Rust's split columns there", fun _ ↦
    Spec.NodeVectors.vertices.all fun (k, values) ↦
      values.length == (splitColumns tables).length &&
        values == (List.range values.length).map fun j ↦ ofK (splitEntry guestWords j k))]

/-- The driver. -/
def main : IO UInt32 := do
  let mut failed := false
  for (name, check) in checks do
    let start ← IO.monoMsNow
    let ok := check ()
    IO.println s!"{name}: {if ok then "ok" else "FAILED"} ({(← IO.monoMsNow) - start} ms)"
    failed := failed || !ok
  return if failed then 1 else 0
