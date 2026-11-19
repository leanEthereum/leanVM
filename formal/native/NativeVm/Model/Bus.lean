module

public import NativeVm.Model.Gkr

/-!
# Phase 3: the bus

Models `verifyBusBalance computedBytecodeValue` (`Statement/LeanVmVerifier.lean`, `bus.rs`), with
`busLayout`, `fingerprints`, `blockForm`, `accumulateSide`, `bytecodeShare` and
`computedBytecodeValue`.

**Takes** the layout. **Reads** a grind, the slot weights and `β`, the GKR walk
(`verifyGkrGrandProducts`, at the push side's depth), the memory's two limbs and final counters,
the bytecode's final counter, the bytecode share's sumcheck over the tuple slot and its value, which
is checked against the bytecode's multilinear extension (`computedBytecodeValue`).
**Returns** `BusResultW`: the four framework column claims, the bytecode point, the GKR point, each
table's form per side (`forms[table][side]`, each `FormW`), and the three sides' totals.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- A side's placements (`BusLayout`): its depth, the framework blocks', the table blocks'. -/
structure BusLayoutW where
  depth : Nat
  framework : Array Placement
  tables : Array Placement
  deriving Inhabited

/-- `bus_layout(framework_log_rows, blocks)`. -/
def busLayout (frameworkLogRows : Array Nat) (blocks : Array BusBlockW) : BusLayoutW :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := Array.zipWith (fun size offset ↦
    ({ variableCount := size, index := offset } : Placement)) sizes offsets
  ⟨depth, placements.extract 0 frameworkLogRows.size,
    placements.extract frameworkLogRows.size placements.size⟩

/-- `BusResult`. -/
structure BusResultW where
  claims : Array ColumnClaimW
  bytecodePoint : Array EW
  point : Array EW
  forms : Array (Array FormW)
  totals : Array EW
  deriving Inhabited

/-- `SEP_STATE`, `SEP_MEM`, `SEP_BYTECODE`: `1`, `g`, `g²`. -/
def sepStateW : EW := 1
def sepMemW : EW := gen
def sepBytecodeW : EW := gpow 2

/-- `fingerprints`: the boundary state's, the memory cell's and the bytecode tuple's. -/
def fingerprints (weights memory memoryLow bytecodeLow : Array EW) (bytecodeShare : EW)
    (pc memoryCount bytecodeCount : EW) : Array EW :=
  #[dot (weights.extract 0 3) #[sepStateW, pc, gpow 0],
    dot (weights.extract 0 5) (#[sepMemW, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.extract 0 3) #[sepBytecodeW, indexMle bytecodeLow, bytecodeCount] +
      bytecodeShare]

/-- `blockForm`: `side_beta` plus the block's fingerprint, a tuple slot at a time. -/
def blockForm (block : BusBlockW) (sideWeights : Array EW) (sideBeta : EW) : FormW :=
  block.coordinates.zipIdx.foldl
    (fun form (coordinate, slot) ↦ form.addScaled coordinate (sideWeights.getD slot 0))
    (FormW.const sideBeta)

/-- `accumulateSide`: the forms with the side's table blocks added, and the side's total. -/
def accumulateSide (forms : Array (Array FormW)) (side : Nat) (blocks : Array BusBlockW)
    (sideLayout : BusLayoutW) (frameworkFingerprints sideWeights : Array EW) (sideBeta : EW)
    (point : Array EW) (treeValue : EW) : Array (Array FormW) × EW :=
  let frameworkSelectors := sideLayout.framework.map (eqAbove · point)
  let tableSelectors := sideLayout.tables.map (eqAbove · point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let (forms, paddingRows) := (tableSelectors.zip blocks).foldl
    (fun (acc : Array (Array FormW) × EW) (selector, block) ↦
      let form := blockForm block sideWeights sideBeta
      let padding := (tablesW.getD block.owner default).padding
      (acc.1.modify block.owner fun row ↦ row.modify side fun f ↦ f.addScaled form selector,
        acc.2 + selector * paddingWeight (point.extract 0 block.logRows) block.rows *
          (form.evaluate padding + 1))) (forms, 0)
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding + paddingRows)

/-- `bytecodeShare`: the share, its sumcheck over the slot, the value; the share, the bytecode
point and the value. -/
def bytecodeShare (weights bytecodeLow : Array EW) : VM (EW × Array EW × EW) := do
  let share ← readScalar
  let (slotPoint, claim) ← sumcheckPlain share 3 busBits
  let value ← readScalar
  require (claim == dot (eqKernel slotPoint) weights * value)
  pure (share, bytecodeLow ++ slotPoint, value)

/-- `computedBytecodeValue`: the bytecode's multilinear extension at the point is the value. -/
def computedBytecodeValue (words : Array UInt64) (point : Array EW) (value : EW) : VM Unit :=
  require (multilinearEval (words.map EW.ofK) point == value)

/-- **Phase 3** (`verifyBusBalance computedBytecodeValue`). -/
def verifyBusBalance (layout : LayoutW) : VM BusResultW := do
  let frameworkLogRows := #[0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout #[] layout.count
  require (pushLayout.depth < 64)
  grind (busGrindingBits pushLayout.depth)
  let weights ← sampleChallenges (2 ^ busBits)
  let beta ← sampleChallenge
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  require (countRoot != 0)
  let memoryLow := point.extract 0 layout.logMemory
  let bytecodeLow := point.extract 0 layout.logBytecode
  let memory ← readScalars 2
  let memoryFinal ← readScalar
  let bytecodeFinal ← readScalar
  let claims : Array ColumnClaimW :=
    #[⟨memory0, memoryLow, memory.getD 0 0⟩, ⟨memory1, memoryLow, memory.getD 1 0⟩,
      ⟨memoryFinalCounters, memoryLow, memoryFinal⟩,
      ⟨bytecodeFinalCounters, bytecodeLow, bytecodeFinal⟩]
  let (share, bytecodePoint, value) ← bytecodeShare weights bytecodeLow
  computedBytecodeValue layout.bytecode bytecodePoint value
  let fp := fingerprints weights memory memoryLow bytecodeLow share
  let pcFinal := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : Array (Array FormW) := tablesW.map fun _ ↦ #[#[], #[], #[]]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp pcFinal memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout #[] #[1] 0 point
    (treeValues.getD 2 0)
  pure ⟨claims, bytecodePoint, point, forms3, #[total0, total1, total2]⟩

end NativeVm.Model
