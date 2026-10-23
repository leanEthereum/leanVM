import LeanVM.Protocol.EndToEnd.Sound.Moves

/-!
# The prover moves' tests

* **Statement locks** of `grindBits_le_of_reachable` and `movesOK_ringSwitch`.
* **The trust audit**: `grindBits_le_of_reachable` depends on `propext`, `Classical.choice` and `Quot.sound` only.
* **What is load-bearing.** The bound on the bits is the predicate's: a proof of work of `65` bits
  is not allowed at `64`, while WHIR's `17` is; a commitment is not allowed where commitments are
  excluded.
-/

namespace LeanVMTests.Protocol.EndToEnd.Sound.Moves

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.EndToEnd.Sound

/-! ## Statement locks -/

example (bytecode : List K) (publicInput : Digest) {h : List Ev}
    (hh : (leanVmProgram bytecode publicInput).Reachable h) : grindBits h ≤ 64 :=
  grindBits_le_of_reachable bytecode publicInput hh

example (point s : List E) : MovesOK (fun _ ↦ False) False (ringSwitch point s) :=
  movesOK_ringSwitch point s

/-! ## The trust audit -/

/--
info: 'LeanVM.Protocol.EndToEnd.Sound.grindBits_le_of_reachable' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms grindBits_le_of_reachable

/-! ## What is load-bearing -/

/-- A proof of work of `65` bits is not allowed at `64`. -/
example : ¬ MovesOK (· ≤ 64) True (Prog.grindP 65) := fun h ↦ absurd h.1 (by decide)

/-- WHIR's query proof of work is allowed at `64`. -/
example : MovesOK (· ≤ 64) True (Prog.grindP Whir.queryGrindingBits) :=
  MovesOK.grindP (by decide)

/-- A commitment is not allowed where commitments are excluded. -/
example : ¬ MovesOK (fun _ ↦ False) False (Prog.commitP 1 1) := fun h ↦ h.1

/-- The stack's root is a commitment: `commitStack` is not commitment-free on an admissible
stack. -/
example : ¬ MovesOK (fun _ ↦ False) False (commitStack 28 1) := by
  intro h
  obtain ⟨level, rest, hd⟩ : ∃ level rest, deriveConfig 28 1 = some (level :: rest) := by
    cases hd : deriveConfig 28 1 with
    | none => exact absurd hd (by decide)
    | some l =>
      cases l with
      | nil => exact absurd hd (by decide)
      | cons level rest => exact ⟨level, rest, rfl⟩
  unfold commitStack at h
  rw [hd] at h
  exact h.1

end LeanVMTests.Protocol.EndToEnd.Sound.Moves
