module

public import NativeVm.Model.PublicInput

/-!
# Phase 6: `KECCAK`'s validity, by GKR over its rounds

Models `keccakPhase` and `verifyKeccak` (`Statement/LeanVmVerifier.lean`, `keccak.rs`), with
`verifyKeccakLayer`, `keccakLayers`, `keccakSlotWeights`, `keccakOpen`, `keccakFirstClaim`,
`keccakLinearTranspose` and `keccakInstanceWeights`.

**Takes** the layout and the tables' evaluations; `KECCAK`'s point (`inst`) and its 25 output
lanes' evaluations. **Reads** a grind, the segment and lane challenges, the committed outputs'
claim, `KECCAK_DEPTH` layers (each: 47 product coefficients, a grind, `s`, an equality-mode
sumcheck over the claim's point, a plain one over the 11 bit-position variables, three values, a
grind, `β`), the opening of the committed outputs (a slot sumcheck and one word), a sumcheck over
the pack's instances, the opening of the inputs (a slot sumcheck and 64 slices). **Returns**
`(outputs, point, slices)`: the column claim on `q_keccak` of the committed outputs, and the point
and the 64 slices of `q_keccak` that ring switching takes.

The embedding's tables `RMFE_EMBED` and `RMFE_PROJECT` are the statement's `rmfeEmbed` and
`rmfeProject` as words (`rmfeEmbedW`, `rmfeProjectW`).
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-- `RMFE_EMBED`, as words. -/
def rmfeEmbedW : Array UInt64 := rmfeEmbed.toArray.map (·.toUInt64)

/-- `RMFE_PROJECT`, as words. -/
def rmfeProjectW : Array UInt64 := rmfeProject.toArray.map (·.toUInt64)

/-- `KECCAK_RC`. -/
def keccakRCW : Array UInt64 := keccakRC.toArray

/-- `KECCAK_RHO`. -/
def keccakRhoW : Array Nat := keccakRho.toArray

/-- Bit `b` of a word. -/
def testBitW (w : UInt64) (b : Nat) : Bool := (w >>> b.toUInt64) &&& 1 == 1

/-- `Claim` (`KeccakClaim`): the value, the instance weights, the point, the bit weights. -/
structure KeccakClaimW where
  value : EW
  mu : Array EW
  point : Array EW
  weights : Array EW
  deriving Inhabited

/-- `linear_transpose(w)`: the transpose of θ, ρ, π on weight vectors. -/
def keccakLinearTranspose (w : Array EW) : Array EW :=
  let g : Array EW := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRhoW.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array EW := (Array.range 5).flatMap fun x ↦ (Array.range 64).map fun z ↦
    sumE ((Array.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)
  (Array.range 25).flatMap fun lane ↦ (Array.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `instance_weights(s)`: each unit vector's embedding at `s`. -/
def keccakInstanceWeights (s : EW) : Array EW :=
  let sPowers := powers s embedBits
  rmfeEmbedW.map fun e ↦
    sumE ((Array.range embedBits).filterMap fun b ↦
      if testBitW e b then some (sPowers.getD b 0) else none)

/-- `verify_layer(transcript, shape, step, claim)`. -/
def verifyKeccakLayer (logSteps step : Nat) (claim : KeccakClaimW) : VM KeccakClaimW := do
  let packBits := logSteps - 4
  let product ← readScalars productBits
  let projected := sumE ((Array.range productBits).map fun c ↦
    sumE ((claim.mu.zip rmfeProjectW).filterMap fun (m, mask) ↦
      if testBitW mask c then some m else none) * product.getD c 0)
  let segments := eqKernel (claim.point.extract packBits claim.point.size)
  let iota := sumE ((Array.range keccakSegments).map fun segment ↦
    let constant := keccakRCW.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((Array.range 64).filterMap fun z ↦
      if testBitW constant z then some (claim.weights.getD z 0) else none))
  require (projected + iota * sumE claim.mu == claim.value)
  grind (grindingBits (productBits - 1))
  let s ← sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  let (point, value) ← sumcheck (polyEval product s) 3 (claim.point.map some)
  let (localPoint, value) ← sumcheckPlain value 4 keccakLocalBits
  let t ← readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  require (dot (eq.extract 0 keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) == value)
  grind (grindingBits 2)
  let beta ← sampleChallenge
  let weights := (Array.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  pure ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` from `0` to `KECCAK_DEPTH - 1`. -/
def keccakLayers (logSteps : Nat) (claim : KeccakClaimW) : VM KeccakClaimW :=
  (List.range keccakDepth).foldlM (fun claim step ↦ verifyKeccakLayer logSteps step claim) claim

/-- `keccakSlotWeights`: the weight a claim puts on each `(slot, z)`. -/
def keccakSlotWeights (logSteps : Nat) (claim : KeccakClaimW) (first count : Nat) :
    Array (Array EW) :=
  let segments := eqKernel (claim.point.extract (logSteps - 4) claim.point.size)
  (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * claim.weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))

/-- `open(transcript, shape, claim, first, count, value)`: a sumcheck over the slot; the slot
point, the weight on each slice there, and what is left to match. -/
def keccakOpen (logSteps : Nat) (claim : KeccakClaimW) (first count : Nat) (value : EW) :
    VM (Array EW × Array EW × EW) := do
  let (slot, value) ← sumcheckPlain value 3 qkeccakSlotBits
  let rows := slot.foldl (fun rows challenge ↦
    (Array.range (rows.size / 2)).map fun i ↦
      Array.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) #[])
        (rows.getD (2 * i + 1) #[])) (keccakSlotWeights logSteps claim first count)
  pure (slot, rows.getD 0 #[], value)

/-- `keccakFirstClaim`: the claim on every segment's output at `inst` and `segment`. -/
def keccakFirstClaim (inst segment lanePoint output : Array EW) (committed : EW) : KeccakClaimW :=
  let lanes := eqKernel lanePoint
  let weights := (Array.range keccakBits).map fun j ↦
    lanes.getD (j / 64) 0 * EW.ofK ((1 : UInt64) <<< (j % 64).toUInt64)
  let last := (eqKernel segment).getD (keccakSegments - 1) 0 * dot (lanes.extract 0 25) output
  ⟨committed + last, eqKernel (inst.extract 0 4), inst.extract 4 inst.size ++ segment, weights⟩

/-- `verify_keccak(transcript, shape, instance, output)`. -/
def verifyKeccak (logSteps : Nat) (inst output : Array EW) :
    VM (Array ColumnClaimW × Array EW × Array EW) := do
  let packBits := logSteps - 4
  let rLow := inst.extract 0 4
  grind (grindingBits (keccakSegmentBits + keccakLaneBits))
  let segment ← sampleChallenges keccakSegmentBits
  let lanePoint ← sampleChallenges keccakLaneBits
  let committed ← if 1 < keccakSegments then readScalar else pure 0
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← keccakLayers logSteps first
  let outputs ← if 1 < keccakSegments then do
      let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
      let word ← readScalar
      require (weights.getD 0 0 * word == value)
      pure #[(⟨qkeccak, rLow ++ inst.extract 4 inst.size ++ slot, word⟩ : ColumnClaimW)]
    else pure #[]
  let (low, value) ← sumcheckPlain claim.value 3 4
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← readScalars kBits
  require (multilinearEval claim.mu low * dot weights slices == value)
  pure (outputs, low ++ claim.point.extract 0 packBits ++ slot, slices)

/-- **Phase 6** (`keccakPhase`): `KECCAK`'s point and output lanes into `verifyKeccak`. -/
def keccakPhase (layout : LayoutW) (evaluations : Array (Array EW × Array EW)) :
    VM (Array ColumnClaimW × Array EW × Array EW) :=
  let (point, values) := evaluations.getD opKeccak (#[], #[])
  verifyKeccak (layout.tableLogHeights.getD opKeccak 0) point
    ((Array.range 25).map fun lane ↦ values.getD (keccakOut + lane) 0)

end NativeVm.Model
