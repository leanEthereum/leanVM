/-
  LeanVM.Prover.Complete.Truth

  When the verifier's claims on the committed stack hold: the interface between the phases of the
  honest prover's completeness proof.
-/

module

public import Statement.Prover.Mle
public import Statement.Verifier.Lib

/-!
# Claims that hold of the stack

Each phase of `verify_execution` before the stacked opening leaves claims on the committed stack
(`Statement/Verifier/Lib.lean`): column claims (`ColumnClaim`, a column's multilinear extension at a
point), the link's memory term, and ring-switching claims on the bit slices of columns
(`RingClaim`). The honest prover's phases are proved to leave claims that hold of the honest stack
(`Witness.stack`); the stacked opening is proved to accept such claims. Here is what holding means,
on the stack itself: a column's values are the stack's block at its placement (`stackBlock`).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Prover

/-- The block of the stack at a placement: `2^variableCount` cells from its offset. -/
def stackBlock (stack : Array K) (p : Placement) : Array K :=
  stack.extract p.index (p.index + 2 ^ p.variableCount)

/-- **A column claim holds of the stack**: where the column has a placement, the claimed value is
the multilinear extension of the stack's block there, at the claim's point (low coordinate
first, `mleK`). A column without a placement never reaches the stack, and its claim says
nothing. -/
def ColumnClaim.HoldsOn (layout : Layout) (stack : Array K) (c : ColumnClaim) : Prop :=
  ∀ p, layout.placements.getD c.column none = some p → c.value = mleK (stackBlock stack p) c.point

/-- Bit `i` of every word of a column, in `E`. -/
def bitSlice (column : Array K) (i : ℕ) : Array E :=
  column.map fun a ↦ if a.toBitVec.getLsbD i then 1 else 0

/-- The column a ring piece reads: the stack's block at its placement, the whole stack for
`none`. -/
def RingPiece.column (stack : Array K) (piece : RingPiece) : Array K :=
  match piece.placement with
  | some p => stackBlock stack p
  | none => stack

/-- A piece's part of slice `i`: its scale times the multilinear extension of bit `i` of its
column at its point. -/
def RingPiece.sliceValue (stack : Array K) (piece : RingPiece) (i : ℕ) : E :=
  piece.scale * mleA (bitSlice (piece.column stack) i) piece.point

/-- **A ring-switching claim holds of the stack**: its `64` slices are the sums of its pieces'
parts, `s[i] = Σ_p scale_p · ẑ_p(i, point_p)` (`RingClaim`, `ring_switch.rs`). -/
def RingClaim.HoldsOn (stack : Array K) (rc : RingClaim) : Prop :=
  rc.slices.length = 64 ∧
    ∀ i < 64, rc.slices.getD i 0 = sumE (rc.pieces.map fun piece ↦ piece.sliceValue stack i)

/-- **The link's memory term holds of the stack**: its value is the two memory columns' extensions
at its point, weighed by its scales (`memoryTermClaim`, `lib.rs`). -/
def LinkEnd.MemoryHoldsOn (layout : Layout) (stack : Array K) (link : LinkEnd) : Prop :=
  ∀ p0 p1, layout.placements.getD memory0 none = some p0 →
    layout.placements.getD memory1 none = some p1 →
    link.memoryValue = link.memoryScales.1 * mleK (stackBlock stack p0) link.memoryPoint +
      link.memoryScales.2 * mleK (stackBlock stack p1) link.memoryPoint

/-! ## On the columns

The same claims on the columns by global number (`Witness.cols`), before the stack lays them out:
the form the link's and the Keccak reduction's proofs leave them in. -/

/-- **A column claim holds of the columns**: the claimed value is the column's multilinear
extension at the claim's point. -/
def ColumnClaim.HoldsIn (cols : Array (Array K)) (c : ColumnClaim) : Prop :=
  c.value = mleK (cols.getD c.column #[]) c.point

/-- **Bit slices that hold of a column**: `64` of them, slice `i` the multilinear extension of the
column's bit `i` at `point`. -/
def SlicesHoldIn (column : Array K) (point slices : List E) : Prop :=
  slices.length = 64 ∧ ∀ i < 64, slices.getD i 0 = mleA (bitSlice column i) point

end LeanVM.Protocol.Verifier

end
