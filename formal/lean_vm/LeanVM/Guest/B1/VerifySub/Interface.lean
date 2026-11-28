/-
  LeanVM.Guest.B1.VerifySub.Interface

  B1 of `verify_sub`, the child verifier: what its callers establish, its meaning (the deferring
  verifier accepting a proof of the child's statement, the fresh claim at `defer_out`), and the
  statement of its soundness.
-/

module

public import LeanVM.Guest.B1.Common.Basic
public import LeanVM.Guest.CoreData
public import Statement.LeanVmGuestBatching

/-!
# `verify_sub`: the interface

`verify_sub(pi_0, pi_1, seed_0, seed_1, g_squares, defer_out)` runs the deferring verifier
(`verifyDeferred`) on one child's proof: the seed `keccakF (seedInput iv pi)`, the announced sizes,
the stack's root, the link (`verify_link`'s sum-checks and their terminal), the Keccak reduction
(`verify_keccak`), ring switching, the stacked opening (`open_stacked`) and its terminal
(`check_stack_terminal`); it stores the fresh claim the link raises at `defer_out`
(`FreshClaim.cells`: the link point's instruction coordinates, then the split columns' values
there).

* `VerifySubPre`: `g_squares` holds the exponent table and its window section (`ExpTables`,
  `ExpWinTab`), which `main` establishes (`exponent_tables`);
* `MeaningVerifySub bytecode`: the cells are a seed and a public input, and for some fresh claim of
  the shape `ChildHasBytecodeShape` asks (`instructionVariableCount bytecode` coordinates, one value
  per split column) and some proof `π`, the deferring verifier accepts `π` for the public input
  under the seed, with the fresh claim's cells at `defer_out`;
* `verify_sub_Spec bytecode`: on a memory image of at most `2^32` words, under `VerifySubPre`, the
  relation gives the meaning, for a stacked program of `2^23` words (`2^19` instructions of
  `2^BYTECODE_SLOT_BITS` slots).

`main`'s soundness (`B1.Main.main_sound_V_of_sub`) takes this statement as a hypothesis, with the
proof named (`B1.Main.SubSoundW`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-- **`verify_sub`'s meaning** on `[pi_0, pi_1, seed_0, seed_1, g_squares, defer_out]`: the cells
of a seed `seed` and a public input `pi`, and for some fresh claim at a point over the instructions
with one value per split column and some proof `π`, the deferring verifier accepts `π` for `pi`
under `seed` (`verifyDeferred`), with the fresh claim's cells at `defer_out`; it returns nothing. -/
def MeaningVerifySub (bytecode : List K) (rd : Reader) : List E → List E → Prop
  | [pi0, pi1, s0, s1, _, out], rets =>
      rets = [] ∧ ∃ (seed pi : Digest) (fresh : FreshClaim) (π : Proof),
        (s0, s1) = digestHalves seed ∧ (pi0, pi1) = digestHalves pi ∧
        fresh.point.length = instructionVariableCount bytecode ∧
        fresh.values.length = (splitColumns tables).length ∧
        ReadsAt rd out fresh.cells ∧ verifyDeferred bytecode seed pi fresh π = true
  | _, _ => False

/-- What `verify_sub`'s callers establish: the exponent table at `g_squares` with its window
section (`exponent_tables`, `ExpTables` and `ExpWinTab`). -/
def VerifySubPre (rd : Reader) : List E → Prop
  | [_, _, _, _, sq, _] => ExpTables rd sq ∧ ExpWinTab rd sq
  | _ => False

/-- **`verify_sub` is sound**: on a memory image of at most `2^32` words holding the exponent
tables, for a stacked program of `2^(19 + BYTECODE_SLOT_BITS)` words. -/
def verify_sub_Spec (bytecode : List K) : Prop :=
  bytecode.length = 2 ^ (19 + bytecodeSlotBits) →
    ∀ {κ : ℕ}, κ ≤ 32 → ∀ (L : MemoryImage κ) (args rets : List E), VerifySubPre L.read args →
      coreProgram.Rel L.read "verify_sub" args rets → MeaningVerifySub bytecode L.read args rets

end
end LeanVM.Guest.B1.VerifySub
