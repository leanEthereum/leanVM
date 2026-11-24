module

public import Statement.Verifier.Layout
public import Statement.Verifier.Transcript

/-!
# Sumcheck, the bus and the table sumcheck (`transcript.rs`, `bus.rs`)

## Sumcheck rounds (`transcript.rs`)

A round polynomial of `count` coefficients is sent with one coefficient left out, which the
verifier derives from the running claim: in plain mode (`eq_factor = None`) `q(0) + q(1) = claim`
fixes `c1`; in equality mode (`eq_factor = r`) `(1 + r)·q(0) + r·q(1) = claim` fixes `c0`
(characteristic two). Each round's challenge follows a grind for the degree of the whole round
polynomial, the equality factor included: `grindingBits (count - 1 + [eq])`, zero bits at every
round the verifier runs (`count ≤ 5`).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-- Fail on `none`: a pure step that returns a `Result` in the Rust. -/
def liftOption {α : Type} : Option α → VerifierProgram α
  | none => VerifierProgram.fail
  | some a => VerifierProgram.ret a

/-- `Transcript::sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes, then grind for its degree; its coefficients,
constant first (`transcript.rs`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → VerifierProgram (List E)
  | none => do
    let constant ← VerifierProgram.readScalar
    let tail ← VerifierProgram.readScalars (count - 2)
    VerifierProgram.grindProofOfWork (grindingBits (count - 1))
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← VerifierProgram.readScalars (count - 1)
    VerifierProgram.grindProofOfWork (grindingBits (count - 1 + 1))
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`transcript.rs`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → VerifierProgram (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← VerifierProgram.sampleChallenge
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase (`bus.rs`)

After a grind for the push tree's depth, the fingerprint is sixteen independent slot weights and
`β`. The three GKR trees (push, pull, count) are batched, their roots read as `shared, count`
(push and pull share their root, which is the balance), the layers walked two at a time, one first
when the depth is odd. The bytecode's share of the bytecode leaf is then reduced by a sumcheck over
the tuple slot to one value of the stacked bytecode, at a point the verifier checks it at (or, an
aggregate's verifier, defers). The leaf decomposition is pure (`accumulateSide`): every side's
framework blocks are evaluated outright, its table blocks accumulate into the owner's form for that
side, and the side's total is the GKR value less the framework and the padding.
-/

/-- `N_TREES`: the trees the bus GKR batches, push, pull and count (`bus.rs`). -/
def nTrees : ℕ := 3

/-- `bus_grinding_bits(mu)`: the grind before the fingerprint, unequal push and pull multisets
passing the product check with probability at most `2^mu / |E|`, `mu` the push depth
(`bus.rs`). -/
def busGrindingBits (mu : ℕ) : ℕ := grindingBits (2 ^ mu)

/-- The state of the GKR walk: the push, pull and count trees' values at `point`. -/
structure GkrState where
  /-- The push, pull and count trees' values. -/
  values : List E
  /-- The point they are at. -/
  point : List E

/-- One step of `step` levels of the GKR walk (`bus.rs`): a grind and the combiner, the
sumcheck, every tree's children, then a grind for the children's degree `step` in `y`, doubled on
the `last` layer, whose `y` the table sumcheck's zerocheck reads too. -/
def gkrStep (step : ℕ) (last : Bool) (state : GkrState) : VerifierProgram GkrState := do
  VerifierProgram.grindProofOfWork (grindingBits (nTrees - 1))
  let combiner ← VerifierProgram.sampleChallenge
  let claim := polyEval state.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (state.point.map some)
  let child0 ← VerifierProgram.readScalars (2 ^ step)
  let child1 ← VerifierProgram.readScalars (2 ^ step)
  let child2 ← VerifierProgram.readScalars (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  VerifierProgram.require (claim = polyEval products combiner)
  VerifierProgram.grindProofOfWork (grindingBits (if last then 2 * step else step))
  let y ← VerifierProgram.sampleChallenges step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise; the
step that ends the walk is the last. -/
def gkrLayers : ℕ → GkrState → VerifierProgram GkrState
  | 0, s => return s
  | 1, s => do
    let s ← gkrStep 1 true s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 false s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 (n = 0) s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the GKR point, and the three trees'
values there (`bus.rs`). -/
def verifyGkrGrandProducts (depth : ℕ) : VerifierProgram (E × List E × List E) := do
  let shared ← VerifierProgram.readScalar
  let count ← VerifierProgram.readScalar
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-- `BusResult` (`bus.rs`): the framework columns' claims, the point the bytecode sumcheck
leaves the stacked bytecode at (the summary's `bytecode_point`, the claim an aggregate defers), the
GKR point (which the table sumcheck reuses), each table's form per side (`forms[table][side]`), and
the three sides' totals. -/
structure BusResult where
  /-- The framework columns' claims. -/
  claims : List ColumnClaim
  /-- The bytecode's point: the GKR point's low coordinates, then the slot sumcheck's. -/
  bytecodePoint : List E
  /-- The GKR point. -/
  point : List E
  /-- Each table's form per side. -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List E
  deriving Inhabited

/-- The three framework fingerprints of a side (`framework`, `bus.rs`; the Rust hoists
`memory_index` and `bytecode_index`, `bus.rs`, pure values inlined here), each its tuple's
coordinates weighted by the slot weights: the boundary state, the memory cell (the two limbs of
`memory`), and the bytecode tuple, the program's share of it `bytecodeShare`. -/
def fingerprints (weights memory memoryLow bytecodeLow : List E) (bytecodeShare : E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 5) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] + bytecodeShare]

/-- One table block's form on a side: `side_beta` plus the block's fingerprint, one tuple slot at
a time (`bus.rs`). -/
def blockForm (block : BusBlock) (sideWeights : List E) (sideBeta : E) : Form :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (Form.const sideBeta)

/-- One side of the leaf decomposition (`bus.rs`): the forms with the side's table
blocks added, and the side's total. A table's form is summed over its padding rows too, whose
leaves hold `1` instead: the difference, `padding_rows`, is public. -/
def accumulateSide (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (point : List E) (treeValue : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let (forms, paddingRows) := (List.zip tableSelectors blocks).foldl
    (fun (forms, paddingRows) (selector, block) ↦
      let form := blockForm block sideWeights sideBeta
      let padding := (tables.getD block.owner default).padding
      (forms.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        paddingRows + selector * paddingWeight (point.take block.logRows) block.rows *
          (form.evaluate (padding.getD · 0) + 1))) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding + paddingRows)

/-- The bytecode's share and its sumcheck (`bus.rs`): the program's share of a bytecode
leaf, `Σ_x weights[x]·P(bytecode_low, x)` over the stacked bytecode's slots, reduced by a
sumcheck over `x`, its low bit first, to one value of `P`, read from the proof. The share, the
point `(bytecode_low, x)` and the value; the sumcheck's end is checked here (`BytecodeShare`), the
value against `P` by the caller's `bytecodeValue` (`BytecodeValue`). -/
def bytecodeShare (weights bytecodeLow : List E) : VerifierProgram (E × List E × E) := do
  let share ← VerifierProgram.readScalar
  let (slotPoint, claim) ← sumcheck share 3 (List.replicate busBits none)
  let value ← VerifierProgram.readScalar
  VerifierProgram.require (claim = dot (eqKernel slotPoint) weights * value)
  return (share, bytecodeLow ++ slotPoint, value)

/-- `verify_bus_balance(layout, transcript)` (`bus.rs`). **Where the verifier meets the
fixed polynomial**, the stacked bytecode's multilinear extension: the proof claims its value at the
point the bytecode sumcheck leaves (`bus.rs`), and `bytecodeValue` checks the claim. The
deployed verifier evaluates the polynomial (`computedBytecodeValue`); the verifier inside an
aggregate holds the point and the value to a claim it hands on (`claimedBytecodeValue`). -/
def verifyBusBalance (bytecodeValue : List K → List E → E → VerifierProgram Unit)
    (layout : Layout) : VerifierProgram BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  VerifierProgram.require (pushLayout.depth < 64)
  VerifierProgram.grindProofOfWork (busGrindingBits pushLayout.depth)
  let weights ← VerifierProgram.sampleChallenges (2 ^ busBits)
  let beta ← VerifierProgram.sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  VerifierProgram.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← VerifierProgram.readScalars 2
  let memoryFinal ← VerifierProgram.readScalar
  let bytecodeFinal ← VerifierProgram.readScalar
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1] memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let (share, bytecodePoint, value) ← bytecodeShare weights bytecodeLow
  bytecodeValue layout.bytecode bytecodePoint value
  let fp := fingerprints weights memory memoryLow bytecodeLow share
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, bytecodePoint, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck (`bus.rs`)

One plain-mode sumcheck over `max` of the tables' log-heights, its challenges reversed the point;
the terminal claim is `Σ weight · (constraints + forms)`, and a table of log-height `h` has its
evaluations at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`bus.rs`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loops of `table_sumcheck` (`bus.rs`): read each table's row
evaluations, add its weighted terms to `final`, and collect its point and evaluations. The Rust
reads every table's evaluations before it sums the terms: the same reads, in the same order. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → VerifierProgram (E × List (List E × List E))
  | [], _, final => return (final, [])
  | (table, height, forms, weight) :: rest, cursor, final => do
    let evaluations ← VerifierProgram.readScalars table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let (final, rows) ← tableTerms constraintPowers formPowers point rest
      (cursor + table.nConstraints) final
    return (final, (point.take height, evaluations) :: rows)

/-- `table_sumcheck(tables, table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target, transcript)` (`bus.rs`): each table's point and its columns'
evaluations there. -/
def tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) : VerifierProgram
    (List (List E × List E)) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, evaluations) ← tableTerms constraintPowers formPowers point rows 0 0
  VerifierProgram.require (final = claim)
  return evaluations

end LeanVM.Protocol.Verifier

end
