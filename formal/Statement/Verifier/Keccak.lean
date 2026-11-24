module

public import Statement.Verifier.Bus

/-!
# Keccak, by GKR over its rounds (`keccak.rs`)

The protocol is `doc/leanvm/body/c-keccak-gkr.tex`; `KECCAK_RC`, `KECCAK_RHO`, `KECCAK_PI`
(`crates/verifier/src/hash.rs`) are `keccakRC`, `keccakRho`, `keccakPi` of `Keccak.lean`.
A claim is a weighted sum of the bits of one state per segment, the weight of bit `j` of instance
`i` of pack `y` (sixteen consecutive steps) in segment `m` being
`eq(point, (y, m)) · weights[j] · mu[i]`; each layer turns a claim on the states after a round into
one on the states before it.

The weight array `g` of `linear_transpose` is an array here, set where the Rust sets it.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-! ### Constants (`keccak.rs`) -/

/-- `EMBED_BITS`: a pack's bits embed in a polynomial of `24` coefficients (`keccak.rs`). -/
def embedBits : ℕ := 24

/-- `PRODUCT_BITS = 2 · EMBED_BITS − 1`: the product of two embeddings has `47` coefficients
(`keccak.rs`). -/
def productBits : ℕ := 2 * embedBits - 1

/-! ### The embedding (`RMFE_EMBED`, `RMFE_PROJECT`, `keccak.rs`) -/

/-- `RMFE_EMBED` (`keccak.rs`): sixteen bits embed in a binary polynomial of degree at most `23`,
bit `i` of a number the coefficient of `x^i`; entry `i` is the embedding of unit vector `i`. -/
def rmfeEmbed : List ℕ :=
  [0x40c50b, 0x7f79f2, 0x4b4e0a, 0x72740c, 0x5357da, 0x1d1c9e, 0x04be6e, 0x785246, 0x097cdc,
    0x109e7e, 0x1f1454, 0x213cfc, 0x4cfcc8, 0x775770, 0x187386, 0x818a16]

/-- `RMFE_PROJECT` (`keccak.rs`): a product of two embeddings projects to the AND of what they
embed; bit `i` of the projection is the parity of the product's coefficients in mask `i`. -/
def rmfeProject : List ℕ :=
  [0x1, 0x7fffffffffff, 0x274e9d3a74e9, 0x1d3a74e9d3a7, 0x65cb972e5cb9, 0x5cb972e5cb97,
    0x6690aec7cd21, 0x5d8f9a42bb1f, 0x73485763e690, 0x3750967c6ea1, 0x12cf8dd4259f,
    0x1ba84b3e3750, 0x0ad0c9f715a1, 0x064fb8ad0c9f, 0x456864fb8ad0, 0x400000000000]

/-- The loop of `carryless`: while `b ≠ 0`, add `a` if `b`'s low bit is set, then shift. -/
def carrylessAux : (fuel a b out : ℕ) → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
    if b = 0 then out
    else carrylessAux fuel (a <<< 1) (b >>> 1) (if b % 2 = 1 then out ^^^ a else out)

/-- `carryless a b`: the product of two binary polynomials, the cost machine's carry-less
product (`CostMachine.lean`). -/
def carryless (a b : ℕ) : ℕ := carrylessAux b a b 0

/-! ### Claims and the round's linear map (`keccak.rs`) -/

/-- `Claim` (`keccak.rs`): a claim's value, the weight of each instance of a pack, its point
(a pack index, then a segment index), and the weight of each bit position. -/
structure KeccakClaim where
  /-- The claimed value. -/
  value : E
  /-- The weight of each instance of a pack. -/
  mu : List E
  /-- Its point: a pack index, then a segment index. -/
  point : List E
  /-- The weight of each bit position. -/
  weights : List E
  deriving Inhabited

/-- `along(j, k)`: the position `k` columns along from `j`, in the same row and slice
(`keccak.rs`). -/
def keccakAlong (j k : ℕ) : ℕ :=
  let lane := j / 64
  let z := j % 64
  64 * ((lane % 5 + k) % 5 + 5 * (lane / 5)) + z

/-- `linear_transpose(w)` (`keccak.rs`): the transpose of θ, ρ, π on weight
vectors, `⟨w, L(a)⟩ = ⟨Lᵀ(w), a⟩`. `g` is the weight each position of θ's output carries. -/
def keccakLinearTranspose (w : List E) : List E :=
  let w := w.toArray
  let g : Array E := (List.range 25).foldl (fun g lane ↦ (List.range 64).foldl (fun g z ↦
    g.setIfInBounds (64 * lane + z)
      (w.getD (64 * keccakPi lane + (z + keccakRho.getD lane 0) % 64) 0)) g)
    (Array.replicate keccakBits 0)
  let columns : Array E := ((List.range 5).flatMap fun x ↦ (List.range 64).map fun z ↦
    sumE ((List.range 5).map fun y ↦ g.getD (64 * (x + 5 * y) + z) 0)).toArray
  (List.range 25).flatMap fun lane ↦ (List.range 64).map fun z ↦
    g.getD (64 * lane + z) 0 + columns.getD (64 * ((lane % 5 + 1) % 5) + z) 0 +
      columns.getD (64 * ((lane % 5 + 4) % 5) + (z + 1) % 64) 0

/-- `instance_weights(s)` (`keccak.rs`): the instance weights of a claim made
at the polynomial point `s`, each unit vector's embedding at `s`. -/
def keccakInstanceWeights (s : E) : List E :=
  let sPowers := powers s embedBits
  rmfeEmbed.map fun e ↦
    sumE ((List.range embedBits).filterMap fun b ↦
      if e.testBit b then some (sPowers.getD b 0) else none)

/-! ### A layer (`keccak.rs`) -/

/-- `verify_layer(transcript, shape, step, claim)` (`keccak.rs`): a claim on the states
`step` layers below the committed outputs becomes one on the states a layer further down. The Rust
splits `eq(local, j)`, `j = 64 · lane + z`, into `eq_z[z] · eq_lane[lane]` (`keccak.rs`);
here it is the one kernel `eqKernel localPoint`, the same values. -/
def verifyKeccakLayer (logSteps step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim := do
  let packBits := logSteps - 4
  -- 1] The product polynomial: the claim's weighted sum of the packs' unprojected chi.
  let product ← VerifierProgram.readScalars productBits
  let projected := sumE ((List.range productBits).map fun c ↦
    sumE ((List.zip claim.mu rmfeProject).filterMap fun (m, mask) ↦
      if mask.testBit c then some m else none) * product.getD c 0)
  -- iota flips known positions of lane 0 in every instance.
  let segments := eqKernel (claim.point.drop packBits)
  let iota := sumE ((List.range keccakSegments).map fun segment ↦
    let constant := keccakRC.getD (keccakDepth * (segment + 1) - step - 1) 0
    segments.getD segment 0 * sumE ((List.range 64).filterMap fun z ↦
      if constant.toNat.testBit z then some (claim.weights.getD z 0) else none))
  VerifierProgram.require (projected + iota * sumE claim.mu = claim.value)
  -- 2] At a random point a pack is one field element, and the polynomial's value a sumcheck
  -- claim. The polynomial has degree `PRODUCT_BITS - 1`.
  VerifierProgram.grindProofOfWork (grindingBits (productBits - 1))
  let s ← VerifierProgram.sampleChallenge
  let mu := keccakInstanceWeights s
  let kappa := sumE mu
  -- 3] The pack and the segment: an equality-mode round per coordinate of the claim's point.
  let (point, value) ← sumcheck (polyEval product s) 3 (claim.point.map some)
  -- 4] The bit position: `Σ_j w[j] (κ T[j] + (κ + T[j + 1]) T[j + 2])`.
  let (localPoint, value) ← sumcheck value 4 (List.replicate keccakLocalBits none)
  let t ← VerifierProgram.readScalars 3
  let eq := eqKernel localPoint
  let t0 := t.getD 0 0
  let t1 := t.getD 1 0
  let t2 := t.getD 2 0
  VerifierProgram.require
    (dot (eq.take keccakBits) claim.weights * (kappa * t0 + (kappa + t1) * t2) = value)
  -- 5] `t[k] = Σ_j eq[j] T[j + k]`: one claim on the state before chi, then on the round's
  -- input through the linear map. The next claim is quadratic in `beta`.
  VerifierProgram.grindProofOfWork (grindingBits 2)
  let beta ← VerifierProgram.sampleChallenge
  let weights := (List.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)
  return ⟨t0 + beta * (t1 + beta * t2), mu, point, keccakLinearTranspose weights⟩

/-- The layers, `step` from `0` to `KECCAK_DEPTH - 1` (`keccak.rs`). -/
def keccakLayers (logSteps : ℕ) : List ℕ → KeccakClaim → VerifierProgram KeccakClaim
  | [], claim => return claim
  | step :: steps, claim => do
    let claim ← verifyKeccakLayer logSteps step claim
    keccakLayers logSteps steps claim

/-! ### Opening `q_keccak` (`keccak.rs`) -/

/-- The weights of `open` (`keccak.rs`): the weight a claim puts on each
`(slot, z)`, its position weights on the slots of the states it speaks of, scaled by the segment;
`first` is the state segment `0` claims, and only the first `count` segments' states are committed.
The slots above the states (`qkeccakSlots …`), which carry `KECCAK` columns, weigh nothing. -/
def keccakSlotWeights (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) : List (List E) :=
  let segments := eqKernel (claim.point.drop (logSteps - 4))
  let weights := claim.weights.toArray
  let rows : Array (Array E) := (List.range count).foldl (fun rows segment ↦
    (List.range keccakBits).foldl (fun rows j ↦
      rows.modify (25 * (first + segment) + j / 64) fun row ↦
        row.setIfInBounds (j % 64) (segments.getD segment 0 * weights.getD j 0)) rows)
    (Array.replicate (2 ^ qkeccakSlotBits) (Array.replicate 64 0))
  rows.toList.map Array.toList

/-- `open(transcript, shape, claim, first, count, value)` (`keccak.rs`): a sumcheck over
the slot; the point it ends on, the weight the claim puts on each slice there, and what is left to
match. The sumcheck draws nothing from the weights, so computing them after it, as the Rust does,
or before is the same. The Rust sums each slot's row scaled by `eq(slot, ·)` (`eq_kernel(&slot)`);
here the table of rows is folded by the slot's challenges, the same values. -/
def keccakOpen (logSteps : ℕ) (claim : KeccakClaim) (first count : ℕ) (value : E) :
    VerifierProgram (List E × List E × E) := do
  let (slot, value) ← sumcheck value 3 (List.replicate qkeccakSlotBits none)
  let rows := slot.foldl (fun rows challenge ↦
    (List.range (rows.length / 2)).map fun i ↦
      List.zipWith (fun lo hi ↦ lo + challenge * (lo + hi)) (rows.getD (2 * i) [])
        (rows.getD (2 * i + 1) [])) (keccakSlotWeights logSteps claim first count)
  return (slot, rows.headD [], value)

/-- The first claim of `verify_keccak` (`keccak.rs`), on every segment's output at
`instance` and the segment `segment`: the last segment's output is the permutation's, claimed by
the table's lanes `output`, the others' `committed`; the lanes are combined as words at
`lanePoint`, bit `z` of a word weighing `x^z`. -/
def keccakFirstClaim (inst segment lanePoint output : List E) (committed : E) : KeccakClaim :=
  let lanes := eqKernel lanePoint
  let weights := (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eOfNat (2 ^ (j % 64))
  let last := (eqKernel segment).getD (keccakSegments - 1) 0 * dot (lanes.take 25) output
  ⟨committed + last, eqKernel (inst.take 4), inst.drop 4 ++ segment, weights⟩

/-- `verify_keccak(transcript, shape, instance, output)` (`keccak.rs`): the reduction, a
random claim on every segment's output at `instance`, `KECCAK_DEPTH` layers down to the committed
inputs. The last segment's output is the permutation's, claimed by the table's lanes `output` at
`instance`; the others are committed. It leaves openings of `q_keccak`: the committed outputs as
words at one point (column claims), and the column's 64 slices at another (the point and the
slices, for ring switching). The Rust first checks the shape (`keccak.rs`), which the
`KECCAK` table's point and lanes always meet, its log-height at least `keccakMinStepsLog`. -/
def verifyKeccak (logSteps : ℕ) (inst output : List E) : VerifierProgram
    (List ColumnClaim × List E × List E) := do
  let packBits := logSteps - 4
  let rLow := inst.take 4
  -- One message, the segment then the lane: the first claim is multilinear in them.
  VerifierProgram.grindProofOfWork (grindingBits (keccakSegmentBits + keccakLaneBits))
  let segment ← VerifierProgram.sampleChallenges keccakSegmentBits
  let lanePoint ← VerifierProgram.sampleChallenges keccakLaneBits
  let committed ← if 1 < keccakSegments then VerifierProgram.readScalar else pure 0
  let first := keccakFirstClaim inst segment lanePoint output committed
  let claim ← keccakLayers logSteps (List.range keccakDepth) first
  -- The committed outputs, whose instance weights are an eq already: slice 0 holds the slot's
  -- weight, the others `x^z` times it.
  let outputs ← if 1 < keccakSegments then do
      let (slot, weights, value) ← keccakOpen logSteps first 1 (keccakSegments - 1) committed
      let word ← VerifierProgram.readScalar
      VerifierProgram.require (weights.headD 0 * word = value)
      pure [(⟨qkeccak, rLow ++ inst.drop 4 ++ slot, word⟩ : ColumnClaim)]
    else pure []
  -- The inputs: the instances of a pack first, then the slot.
  let (low, value) ← sumcheck claim.value 3 (List.replicate 4 none)
  let (slot, weights, value) ← keccakOpen logSteps claim 0 keccakSegments value
  let slices ← VerifierProgram.readScalars kBits
  VerifierProgram.require (multilinearEval claim.mu low * dot weights slices = value)
  return (outputs, low ++ claim.point.take packBits ++ slot, slices)

end LeanVM.Protocol.Verifier

end
