import Rv64Verifier.Proofs.Pcs.VsoKeeps

/-!
# A level of `whirLevelsRust`, split at its fold rounds

`afterFolds` is a level's body after `TM.loopN foldRoundRust`, so that a level is the fold rounds
bound to it (`whirLevels_cons`), and one fold round is a sample, then `roundK`
(`loopN_fold_succ`).
-/

namespace Rv64Verifier.Model.Pcs
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- A level of `whirLevelsRust` after its fold rounds. -/
def afterFolds (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E)
    (level foldCount levelRate : ℕ) (rest : List (ℕ × ℕ)) :
    WhirLocals × List E → TM Unit
  | (s, levelFolds) => do
    let messageLog := logN - s.folds.length
    let finalLevel := level = config.folds.length - 1
    let (residual, pending) ← if finalLevel then do
        let residual ← TM.nextScalars (2 ^ (messageLog % 64))
        pure (residual, ([] : List (List E × GluedWeightRust)))
      else do
        let shape := match rest with
          | (nextFold, nextRate) :: _ => (messageLog - nextFold + nextRate, 3 * 2 ^ nextFold)
          | [] => (0, 0)
        let _ ← TM.commit shape.1 shape.2
        let oodPoint ← TM.samples messageLog
        let oodValue ← TM.nextScalar
        let intro ← TM.sumcheckRoundPoly 3 oodValue none
        pure ([], [(intro, GluedWeightRust.ood oodPoint)])
    TM.grind queryGrindingBitsRust
    let blockLength : BitVec 64 := 1#64 <<< ((messageLog + levelRate) % 64)
    let count ← TM.ofOption config.queries[level]?
    let queries ← sampleQueriesRust blockLength count
    let lam ← TM.sample
    let queryWeights := powers lam queries.length
    let lanes := 2 ^ (foldCount % 64)
    let leafWords := if level = 0 then lanes else 3 * lanes
    let words ← TM.merkleLeaves level queries leafWords
    let laneWeights := eqKernelRust levelFolds
    let enforced := dotRust (rowValuesRust level words laneWeights) queryWeights
    let intro ← TM.sumcheckRoundPoly 3 enforced none
    let pending := pending ++ [(intro, GluedWeightRust.queries messageLog queries queryWeights)]
    let s := glueRust lam s pending
    if finalLevel then do
      let (_, tailFolds, runningTarget) ←
        TM.forRange (tailRoundRust messageLog) 0 messageLog (s.runningQuad, [], 0)
      let point := s.folds ++ tailFolds
      let laneFolds ← TM.ofOption config.folds[0]?
      let weight ← TM.ofOption (terminalWeightRust basis laneFolds s.glued point)
      let residualValue ← TM.ofOption (multilinearEvalRust residual tailFolds)
      TM.require (weight * residualValue = runningTarget)
    else whirLevelsRust logN config basis (level + 1) rest s

theorem whirLevels_cons (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E)
    (level foldCount levelRate : ℕ) (rest : List (ℕ × ℕ)) (s : WhirLocals) :
    whirLevelsRust logN config basis level ((foldCount, levelRate) :: rest) s =
      TM.loopN foldRoundRust foldCount (s, []) >>=
        afterFolds logN config basis level foldCount levelRate rest := by
  rw [whirLevelsRust]
  congr 1

/-- The fold rounds' state after `lf` were drawn, the running quadratic `q`. -/
def foldSt (Wl : WhirLocals) (lf q : List E) : WhirLocals × List E :=
  ({ Wl with folds := Wl.folds ++ lf, runningQuad := q }, lf)

/-- A fold round after its challenge `c`: the round polynomial, then the rounds left. -/
def roundK (Wl : WhirLocals) (lf q : List E) (n : ℕ) (k : WhirLocals × List E → TM Unit) (c : E) :
    TM Unit :=
  TM.sumcheckRoundPoly 3 (polyEvalRust q c) none >>= fun q' ↦
    TM.loopN foldRoundRust n (foldSt Wl (lf ++ [c]) q') >>= k

theorem loopN_fold_succ (Wl : WhirLocals) (lf q : List E) (n : ℕ)
    (k : WhirLocals × List E → TM Unit) :
    TM.loopN foldRoundRust (n + 1) (foldSt Wl lf q) >>= k = TM.sample >>= roundK Wl lf q n k := by
  simp only [TM.loopN, foldRoundRust, foldSt, bind_assoc, pure_bind, List.append_assoc]
  rfl

end Rv64Verifier.Model.Pcs
