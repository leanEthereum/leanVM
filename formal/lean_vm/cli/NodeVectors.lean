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
* the DA root's membership challenge is the Rust's (`LeanVM.Da.membershipChallengeOf`).

The other vectors are `#guard`s of `LeanVMTests.Spec.Node`. The exit code is `0` when every check
passes.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Node LeanVM.Guest LeanVMTests

/-- The guest's seed, evaluated once. -/
def guestSeed : Digest := deployedSeed guestArray

example : guestSeed = deployedSeed guestProgram := by rw [guestSeed, guestArray_eq]

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
    LeanVM.Da.membershipChallengeOf c.daRoot == c.membershipChallenge)]

/-- The driver. -/
def main : IO UInt32 := do
  let mut failed := false
  for (name, check) in checks do
    let ok := check ()
    IO.println s!"{name}: {if ok then "ok" else "FAILED"}"
    failed := failed || !ok
  return if failed then 1 else 0
