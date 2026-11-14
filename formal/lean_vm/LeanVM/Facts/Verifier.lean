/-
  LeanVM.Facts.Verifier

  Facts about the verifier's definitions (`Statement/LeanVmVerifier.lean`), proved:
  the `q_keccak` spare slots and the `KECCAK` slot layout, and `pack`; and the verifier's
  definitions no end statement reaches, moved here from the statement, names kept: `yE`,
  `packBits`, `pack`, the deployed seed `seed` and the deployed verifier `verify`.
-/

module

public import Statement.Field
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import Statement.Fast.Keccak
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Statement.LeanVmVerifier
public import LeanVM.Protocol.RunWithHash

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The two cases of `qkeccak_slot` (`layout.rs`) are disjoint: no spare-carrying committed
column is an input lane. -/
theorem keccakSlotOf_disjoint :
    ∀ l ∈ keccakCommitted.take qkeccakSpare, ¬ (keccakIn ≤ l ∧ l < keccakIn + 25) := by
  decide +kernel

/-- Dropping the low `v` coordinates of a selector point leaves the selector point of the
selector shifted by `v`. -/
theorem selectorPoint_drop (selector length v : ℕ) :
    (selectorPoint selector length).drop v = selectorPoint (selector >>> v) (length - v) := by
  apply List.ext_getElem (by simp [selectorPoint])
  intro i _ _
  simp [selectorPoint, Nat.shiftRight_add]

/-- `stack_point` as the point, then the selector point's coordinates above the window. -/
theorem Placement.stackPoint_eq_drop (p : Placement) (point : List E) (stackLog : ℕ) :
    p.stackPoint point stackLog =
      point ++ (selectorPoint p.index stackLog).drop p.variableCount := by
  rw [selectorPoint_drop, Placement.stackPoint]

open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash

/-- `E(0, 1)`, the generator `y` of `E` over `K`, `y^2 = x·y + 1`. -/
def yE : E := E.ofLimbs 0 1

/-- `PACK_BITS` (`crates/verifier/src/keccak.rs`): a pack is `2 ^ PACK_BITS` consecutive
steps. -/
def packBits : ℕ := 4

/-- The steps of a pack, `2 ^ PACK_BITS = 16`. -/
def pack : ℕ := 16

/-- The deployed seed, with Keccak. -/
def seed (bytecode : List K) (publicInput : Digest) : KeccakState :=
  Id.run (seedWithHash (m := Id) keccak256 keccakF1600 bytecode publicInput)

/-- **The deployed leanVM verifier**: the program's compiled reading with Keccak-256 and
Keccak-f[1600], from the deployed seed. -/
def verify (bytecode : List K) (publicInput : Digest) (π : Proof) : Bool :=
  Id.run (runProofWithHash (m := Id) keccak256 keccakF1600 (leanVmVerifierProgram bytecode
      publicInput)
    (seed bytecode publicInput) π)

end
end LeanVM.Protocol.Verifier
