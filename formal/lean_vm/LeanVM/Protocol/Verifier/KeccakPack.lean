/-
  LeanVM.Protocol.Verifier.KeccakPack

  A Keccak layer's pack and segment rounds as their own recursion.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# A Keccak layer's pack rounds

`verifyKeccakLayer` (`Statement/LeanVmVerifier.lean`) runs its pack and segment rounds as the
generic `sumcheck` in equality mode, as `crates/verifier/src/keccak.rs` does. The proofs read them
as `keccakPackRounds`, the same rounds returning the value first (`sumcheck_eq_keccakPackRounds`),
and the layer as `verifyKeccakLayerPacked`, the same program through it
(`verifyKeccakLayer_packed`).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Protocol.Compile

@[expose] public section

/-- Step 3 of a layer, the pack and the segment: an equality-mode round per coordinate of the
claim's point, each keeping the normalized polynomial evaluation as its value. The new value and
the challenges. -/
def keccakPackRounds : List E → E → VerifierProgram (E × List E)
  | [], value => return (value, [])
  | r :: rs, value => do
    let message ← sumcheckRoundPoly 3 value (some r)
    let challenge ← VerifierProgram.sampleChallenge
    let (value, point) ← keccakPackRounds rs (polyEval message challenge)
    return (value, challenge :: point)

theorem sumcheck_eq_keccakPackRounds : ∀ (rs : List E) (value : E),
    sumcheck value 3 (rs.map some) =
      (keccakPackRounds rs value).bind fun res ↦ VerifierProgram.ret (res.2, res.1)
  | [], _ => rfl
  | r :: rs, value => by
    simp only [List.map_cons, sumcheck, keccakPackRounds, VerifierProgram.bind_eq,
      VerifierProgram.pure_eq, VerifierProgram.bind_assoc, VerifierProgram.ret_bind,
      sumcheck_eq_keccakPackRounds rs]

/-- `verifyKeccakLayer` with its pack and segment rounds as `keccakPackRounds`, the value first:
`verifyKeccakLayer_packed`. -/
def verifyKeccakLayerPacked (logSteps step : ℕ) (claim : KeccakClaim) : VerifierProgram KeccakClaim := do
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
  -- 3] The pack and the segment.
  let (value, point) ← keccakPackRounds claim.point (polyEval product s)
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

theorem verifyKeccakLayer_packed (logSteps step : ℕ) (claim : KeccakClaim) :
    verifyKeccakLayer logSteps step claim = verifyKeccakLayerPacked logSteps step claim := by
  unfold verifyKeccakLayer verifyKeccakLayerPacked
  simp only [sumcheck_eq_keccakPackRounds, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
    VerifierProgram.bind_assoc, VerifierProgram.ret_bind]

end

end LeanVM.Protocol.Verifier
