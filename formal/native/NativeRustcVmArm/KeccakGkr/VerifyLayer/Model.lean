module

public import NativeVm.Model.KeccakGkr

/-!
# `verifyKeccakLayer` step by step

The layer's run from a transcript state (`run_eq`): the product's read, the first check
(`checkA`: the claim against the product's projection and ι), a grind, `s` (`sqS`), the
equality-mode sumcheck, the plain one, the three values, the second check (`checkB`), a grind,
`β`, the new claim (`newClaim`).
-/

namespace NativeRustcVmArm.KeccakGkr.VerifyLayer

open NativeVm.Model LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- A squeeze of the transcript's sponge: the challenge and the next state. -/
def sqS (s : TState) : EW × TState := (s.sponge.squeeze.1, { s with sponge := s.sponge.squeeze.2 })

/-- The instance weights' part `mask` selects at bit `i`. -/
def maskedOf (mu : Array EW) (i : Nat) : EW :=
  sumE ((mu.zip rmfeProjectW).filterMap fun (m, mask) ↦ if testBitW mask i then some m else none)

/-- The product's projection. -/
def projectedOf (mu product : Array EW) : EW :=
  sumE ((Array.range productBits).map fun i ↦ maskedOf mu i * product.getD i 0)

/-- The bit weights the round constant `k` selects. -/
def bitsOf (weights : Array EW) (k : UInt64) : EW :=
  sumE ((Array.range 64).filterMap fun z ↦ if testBitW k z then some (weights.getD z 0) else none)

/-- ι's part of the claim. -/
def iotaOf (logSteps step : Nat) (c : KeccakClaimW) : EW :=
  let segments := eqKernel (c.point.extract (logSteps - 4) c.point.size)
  sumE ((Array.range keccakSegments).map fun segment ↦
    segments.getD segment 0 *
      bitsOf c.weights (keccakRCW.getD (keccakDepth * (segment + 1) - step - 1) 0))

/-- The first check. -/
def checkA (logSteps step : Nat) (c : KeccakClaimW) (product : Array EW) : Bool :=
  projectedOf c.mu product + iotaOf logSteps step c * sumE c.mu == c.value

/-- The second check: `t` the three values, `kappa` the instance weights' sum. -/
def checkB (c : KeccakClaimW) (kappa : EW) (localPoint t : Array EW) (value : EW) : Bool :=
  dot ((eqKernel localPoint).extract 0 keccakBits) c.weights *
      (kappa * t.getD 0 0 + (kappa + t.getD 1 0) * t.getD 2 0) == value

/-- The layer's weights before the transpose. -/
def layerWeights (eq : Array EW) (beta : EW) : Array EW :=
  (Array.range keccakBits).map fun j ↦
    eq.getD j 0 + beta * (eq.getD (keccakAlong j 4) 0 + beta * eq.getD (keccakAlong j 3) 0)

/-- The new claim. -/
def newClaim (s : EW) (point localPoint t : Array EW) (beta : EW) : KeccakClaimW :=
  ⟨t.getD 0 0 + beta * (t.getD 1 0 + beta * t.getD 2 0), keccakInstanceWeights s, point,
    keccakLinearTranspose (layerWeights (eqKernel localPoint) beta)⟩

theorem pure_bind' {β : Type} (x : TState) (f : Unit × TState → Option β) :
    (StateT.pure () x : Option (Unit × TState)).bind f = f ((), x) := rfl

theorem sampleChallenge_run (s : TState) : sampleChallenge.run s = some (sqS s) := rfl

/-- **The layer, step by step.** -/
theorem run_eq (logSteps step : Nat) (c : KeccakClaimW) (s : TState) :
    (verifyKeccakLayer logSteps step c).run s =
      ((readScalars productBits).run s).bind fun p ↦
        if checkA logSteps step c p.1 then
          ((grind (grindingBits (productBits - 1))).run p.2).bind fun q ↦
            ((sumcheck (polyEval p.1 (sqS q.2).1) 3 (c.point.map some)).run (sqS q.2).2).bind
              fun r ↦
              ((sumcheckPlain r.1.2 4 keccakLocalBits).run r.2).bind fun u ↦
                ((readScalars 3).run u.2).bind fun v ↦
                  if checkB c (sumE (keccakInstanceWeights (sqS q.2).1)) u.1.1 v.1 u.1.2 then
                    ((grind (grindingBits 2)).run v.2).bind fun w ↦
                      some (newClaim (sqS q.2).1 r.1.1 u.1.1 v.1 (sqS w.2).1, (sqS w.2).2)
                  else none
        else none := by
  delta checkA checkB newClaim sqS projectedOf maskedOf iotaOf bitsOf layerWeights
  simp only [NativeVm.Model.verifyKeccakLayer, StateT.run, bind, StateT.bind, pure, StateT.pure,
    require,
    sampleChallenge, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, MonadStateOf.set]
  cases readScalars productBits s with
  | none => rfl
  | some p =>
    simp only [Option.bind_some]
    split
    · simp only [pure_bind']
      cases grind (grindingBits (productBits - 1)) p.2 with
      | none => rfl
      | some q =>
        simp only [Option.bind_some]
        cases sumcheck (polyEval p.1 q.2.sponge.squeeze.1) 3 (c.point.map some)
          { q.2 with sponge := q.2.sponge.squeeze.2 } with
        | none => rfl
        | some r =>
          simp only [Option.bind_some]
          cases sumcheckPlain r.1.2 4 keccakLocalBits r.2 with
          | none => rfl
          | some u =>
            simp only [Option.bind_some]
            cases readScalars 3 u.2 with
            | none => rfl
            | some v =>
              simp only [Option.bind_some]
              split
              · simp only [pure_bind']
              · rfl
    · rfl

end

end NativeRustcVmArm.KeccakGkr.VerifyLayer
