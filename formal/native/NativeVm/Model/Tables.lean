module

public import NativeVm.Model.Bus

/-!
# Phase 4: the table sumcheck

Models `tablePhase`, `tableSumcheck`, `tableWeights`, `tableTerms` and `tableColumnClaims`
(`Statement/Verifier/Bus.lean`, `Statement/Verifier/Lib.lean`, `bus.rs`, `lib.rs`).

**Takes** the layout and the bus's result. **Reads** a grind and `ξ`, a plain sumcheck of degree
three over the tallest table's log-height (its challenges reversed the point), then every table's
row of evaluations, in opcode order. **Returns** each table's point (the point's first
log-height coordinates) and evaluations, `Array (Array EW × Array EW)`, which `tableColumnClaims`
turns into column claims on the tables' global columns, and from which phase 6 takes `KECCAK`'s.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `tableWeights`: coordinate `v` contributes `1 + equality_point[v] + r_v` to a table taller
than `v`, `r_v` to the others. -/
def tableWeights (heights : Array Nat) (equalityPoint point : Array EW) : Array EW :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    Array.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- One table of `tableTerms`: its evaluations read, its weighted terms added to `final`, its
point and evaluations appended; the constraint cursor moved past its constraints. -/
def tableTermsStep (constraintPowers formPowers point : Array EW)
    (acc : Nat × EW × Array (Array EW × Array EW)) :
    TableW × Nat × Array FormW × EW → VM (Nat × EW × Array (Array EW × Array EW))
  | (table, height, forms, weight) => do
    let (cursor, final, out) := acc
    let evaluations ← readScalars table.width
    let summand := dot (constraintPowers.extract cursor (cursor + table.nConstraints))
      (constraintsW table.opcode evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate evaluations)))
    pure (cursor + table.nConstraints, final, out.push (point.extract 0 height, evaluations))

/-- `tableTerms`: each table's evaluations read, its weighted terms added to `final`; the final
sum and each table's point and evaluations. -/
def tableTerms (constraintPowers formPowers point : Array EW)
    (rows : Array (TableW × Nat × Array FormW × EW)) : VM (EW × Array (Array EW × Array EW)) := do
  let (_, final, out) ← rows.foldlM (tableTermsStep constraintPowers formPowers point) (0, 0, #[])
  pure (final, out)

/-- `tableSumcheck`. -/
def tableSumcheck (heights : Array Nat) (busForms : Array (Array FormW))
    (constraintPowers formPowers equalityPoint : Array EW) (target : EW) :
    VM (Array (Array EW × Array EW)) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheckPlain target 4 nRounds
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := tablesW.zip (heights.zip (busForms.zip weights))
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows
  require (final == claim)
  pure evaluations

/-- **Phase 4** (`tablePhase`). -/
def tablePhase (layout : LayoutW) (bus : BusResultW) : VM (Array (Array EW × Array EW)) := do
  let nConstraints := (tablesW.map (·.nConstraints)).sum
  let nPowers := nConstraints + nTrees
  grind (grindingBits (nPowers - 1))
  let xi ← sampleChallenge
  let xiPowers := powers xi nPowers
  let constraintPowers := xiPowers.extract 0 nConstraints
  let formPowers := xiPowers.extract nConstraints xiPowers.size
  let target := dot formPowers bus.totals
  tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers bus.point target

/-- `tableColumnClaims`: each table's evaluations at its point, on its global columns. -/
def tableColumnClaims (evaluations : Array (Array EW × Array EW)) : Array ColumnClaimW :=
  (globalColumnBasesW.zip evaluations).flatMap fun (base, point, values) ↦
    values.zipIdx.map fun (value, column) ↦ ⟨base + column, point, value⟩

end NativeVm.Model
