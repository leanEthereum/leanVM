import Rv64Verifier.Proofs.Gkr.LayerModel

/-!
# `keccak::verify_keccak`: the mirror in the code's order

`verifyKeccakRust` at `KECCAK_DEPTH = 12` (two segments, one segment bit), cut where the code
calls into the transcript or into `verify_layer` and `open`: the first claim (`kFirst`, its
position weights `kWeights`), the eleven layers after the first (`kLayers`), the outputs' opening
(`kTail`) and the inputs' (`kInputs`).
-/

namespace Rv64Verifier.Gkr.Keccak
open LeanVM.Parameters LeanVM.Protocol.Verifier Rv64Verifier.Model Rv64Verifier.Model.Gkr
  Rv64Verifier.Transcript

/-- The first claim's position weights: bit `z` of lane `l` weighs `lanes[l] x^z`. -/
def kWeights (lanes : List E) : List E :=
  (List.range keccakBits).map fun j ↦ lanes.getD (j / 64) 0 * eNew (1#64 <<< (j % 64))

/-- The first claim. -/
def kFirst (inst segment lanePoint output : List E) (committed : E) : KeccakClaim :=
  ⟨committed + (eqKernelRust segment).getD 1 0 *
      dotRust ((eqKernelRust lanePoint).take 25) output,
    eqKernelRust (inst.take 4), inst.drop 4 ++ segment, kWeights (eqKernelRust lanePoint)⟩

/-- The inputs' opening, from the last layer's claim. -/
def kInputs (l : Nat) (claim : KeccakClaim) (outputs : Option (List E × E)) :
    TM KeccakOpenings := do
  let (low, value) ← TM.sumcheck claim.value 3 (List.replicate 4 none)
  let (slot, row, value) ← openRust ⟨l, 12⟩ claim 0 2 value
  let slices ← TM.nextScalars kBits
  let atLow ← TM.ofOption (multilinearEvalRust claim.mu low)
  TM.require (atLow * dotRust row slices = value)
  pure ⟨outputs, (low ++ claim.point.take (l - 4) ++ slot, slices)⟩

/-- The committed outputs' opening, then the inputs'. -/
def kTail (l : Nat) (inst : List E) (first : KeccakClaim) (committed : E) (claim : KeccakClaim) :
    TM KeccakOpenings := do
  let (slot, row, value) ← openRust ⟨l, 12⟩ first 1 1 committed
  let word ← TM.nextScalar
  TM.require (row.getD 0 0 * word = value)
  kInputs l claim (some (inst ++ slot, word))

/-- The layers after the first, from `step` on. -/
def kLayers (l step : Nat) (claim : KeccakClaim) : TM KeccakClaim :=
  (List.range' step (12 - step)).foldlM (fun claim step ↦ verifyLayerRust ⟨l, 12⟩ step claim)
    claim

/-- After the first layer. -/
def kLayered (l : Nat) (inst : List E) (first : KeccakClaim) (committed : E) (claim : KeccakClaim) :
    TM KeccakOpenings :=
  kLayers l 1 claim >>= kTail l inst first committed

/-- After the committed outputs' value is read. -/
def kCommitted (l : Nat) (inst output segment lanePoint : List E) (committed : E) :
    TM KeccakOpenings :=
  verifyLayerRust ⟨l, 12⟩ 0 (kFirst inst segment lanePoint output committed) >>=
    kLayered l inst (kFirst inst segment lanePoint output committed) committed

/-- After the lanes' point is sampled. -/
def kLanes (l : Nat) (inst output segment lanePoint : List E) : TM KeccakOpenings :=
  TM.nextScalar >>= kCommitted l inst output segment lanePoint

/-- After the segment's point is sampled. -/
def kSeg (l : Nat) (inst output segment : List E) : TM KeccakOpenings :=
  TM.samples keccakLaneBits >>= kLanes l inst output segment

/-- After the sizes' check. -/
def kMain (l : Nat) (inst output : List E) : TM KeccakOpenings :=
  TM.samples 1 >>= kSeg l inst output

theorem verifyKeccakRust_eq (l : Nat) (inst output : List E) :
    verifyKeccakRust ⟨l, 12⟩ inst output =
      (TM.require (inst.length = l ∧ output.length = 25 ∧ 4 ≤ l) >>= fun _ ↦
        kMain l inst output) := by
  unfold verifyKeccakRust kMain kSeg kLanes kCommitted kLayered kTail kInputs kFirst kWeights kLayers
  simp only [shape_segments, shape_packBits, show (1 : Nat) < 2 from by decide, ↓reduceIte,
    pure_bind, Nat.add_one_sub_one]
  rfl

theorem kLayers_succ (l step : Nat) (h : step < 12) (claim : KeccakClaim) :
    kLayers l step claim = (verifyLayerRust ⟨l, 12⟩ step claim >>= kLayers l (step + 1)) := by
  unfold kLayers
  rw [show 12 - step = (12 - (step + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem kLayers_end (l : Nat) (claim : KeccakClaim) : kLayers l 12 claim = pure claim := rfl

end Rv64Verifier.Gkr.Keccak
