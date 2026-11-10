import Rv64Verifier.Proofs.Pcs.VsoFoldModel

/-!
# A level of `whirLevelsRust` after its fold rounds, in the machine's stages

`afterFolds` split where the compiled level's stages meet: the residual or the commitment
(`afterFolds_eq`), the grinding (`afterCommit`), the queries (`afterGrind`), `lam`
(`afterQueries`), the Merkle checks (`afterLam`), the intro message (`afterWords`) and the glue
(`afterIntro`). `TM.commit` is the machine's `next_scalars(2)` and `Digest::from_halves`
(`commit_run`); `sampleQueriesLoop` runs out of positions before it runs out of fuel
(`sampleQueriesLoop_step`, `sampleQueriesLoop_done`).
-/

namespace Rv64Verifier.Model.Pcs
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Verifier

variable (logN : ℕ) (config : WhirConfigRust) (basis : List E → Option E)
  (level foldCount levelRate : ℕ) (rest : List (ℕ × ℕ)) (s : WhirLocals) (levelFolds : List E)
  (residual : List E) (pending : List (List E × GluedWeightRust))

/-- After the glue, the level's message log `ml`. -/
def afterGlue (ml : ℕ) (s : WhirLocals) : TM Unit :=
  if level = config.folds.length - 1 then do
    let (_, tailFolds, runningTarget) ←
      TM.forRange (tailRoundRust ml) 0 ml (s.runningQuad, [], 0)
    let point := s.folds ++ tailFolds
    let laneFolds ← TM.ofOption config.folds[0]?
    let weight ← TM.ofOption (terminalWeightRust basis laneFolds s.glued point)
    let residualValue ← TM.ofOption (multilinearEvalRust residual tailFolds)
    TM.require (weight * residualValue = runningTarget)
  else whirLevelsRust logN config basis (level + 1) rest s

/-- After the level's intro message. -/
def afterIntro (lam : E) (queries : List (BitVec 64)) (intro : List E) : TM Unit :=
  afterGlue logN config basis level rest residual (logN - s.folds.length) (glueRust lam s (pending ++
    [(intro, GluedWeightRust.queries (logN - s.folds.length) queries
      (powers lam queries.length))]))

/-- After the Merkle checks. -/
def afterWords (lam : E) (queries : List (BitVec 64)) (words : List (List K)) : TM Unit := do
  let enforced := dotRust (rowValuesRust level words (eqKernelRust levelFolds))
    (powers lam queries.length)
  let intro ← TM.sumcheckRoundPoly 3 enforced none
  afterIntro logN config basis level rest s residual pending lam queries intro

/-- After `lam`. -/
def afterLam (lam : E) (queries : List (BitVec 64)) : TM Unit := do
  let words ← TM.merkleLeaves level queries
    (if level = 0 then 2 ^ (foldCount % 64) else 3 * 2 ^ (foldCount % 64))
  afterWords logN config basis level rest s levelFolds residual pending lam queries words

/-- After the queries. -/
def afterQueries (queries : List (BitVec 64)) : TM Unit := do
  let lam ← TM.sample
  afterLam logN config basis level foldCount rest s levelFolds residual pending lam queries

/-- After the grinding. -/
def afterGrind : TM Unit := do
  let count ← TM.ofOption config.queries[level]?
  let queries ← sampleQueriesRust (1#64 <<< ((logN - s.folds.length + levelRate) % 64)) count
  afterQueries logN config basis level foldCount rest s levelFolds residual pending queries

/-- After the residual or the commitment. -/
def afterCommit : List E × List (List E × GluedWeightRust) → TM Unit
  | (residual, pending) => do
    TM.grind queryGrindingBitsRust
    afterGrind logN config basis level foldCount levelRate rest s levelFolds residual pending

/-- The residual (the final level) or the commitment. -/
def levelOpen : TM (List E × List (List E × GluedWeightRust)) :=
  if level = config.folds.length - 1 then do
    let residual ← TM.nextScalars (2 ^ ((logN - s.folds.length) % 64))
    pure (residual, ([] : List (List E × GluedWeightRust)))
  else do
    let shape := match rest with
      | (nextFold, nextRate) :: _ =>
        (logN - s.folds.length - nextFold + nextRate, 3 * 2 ^ nextFold)
      | [] => (0, 0)
    let _ ← TM.commit shape.1 shape.2
    let oodPoint ← TM.samples (logN - s.folds.length)
    let oodValue ← TM.nextScalar
    let intro ← TM.sumcheckRoundPoly 3 oodValue none
    pure ([], [(intro, GluedWeightRust.ood oodPoint)])

theorem afterFolds_eq :
    afterFolds logN config basis level foldCount levelRate rest (s, levelFolds) =
      levelOpen logN config level rest s >>=
        afterCommit logN config basis level foldCount levelRate rest s levelFolds := by
  by_cases h : level = config.folds.length - 1 <;>
    simp only [afterFolds, levelOpen, afterCommit, afterGrind, afterQueries, afterLam, afterWords,
      afterIntro, afterGlue, h, ite_true, ite_false, bind_assoc, pure_bind]
  rfl

/-- `TM.commit` is `next_scalars(2)` followed by `Digest::from_halves`, the root appended to the
ghost roots. -/
theorem commit_run (height width : ℕ) (T : TState) :
    (TM.commit height width).run T =
      ((TM.nextScalars 2).run T).bind fun p ↦
        (digestFromHalves (p.1.getD 0 0, p.1.getD 1 0)).map fun root ↦
          (root, { p.2 with roots := T.roots ++ [(root, height, width)] }) := by
  simp only [TM.commit, TM.nextScalars, TM.nextScalar, StateT.run, bind, StateT.bind, pure,
    StateT.pure]
  rcases h0 : T.proof.stream[T.streamOffset]? with _ | x0
  · simp
  rcases h1 : T.proof.stream[T.streamOffset + 1]? with _ | x1
  · simp [h1]
  rcases hd : digestFromHalves (x0, x1) with _ | root
  · simp [h1, hd]
  · simp [h1, hd]

/-! ## `sample_queries`' loop -/

/-- One more sample: its chunks appended. -/
theorem sampleQueriesLoop_step (bl : BitVec 64) (depth count fuel : ℕ) (r : List (BitVec 64))
    (h : r.length < count) :
    sampleQueriesLoop bl depth count (fuel + 1) r = TM.sample >>= fun sample ↦
      sampleQueriesLoop bl depth count fuel (r ++ (List.range (min (192 / depth)
        (count - r.length))).map (queryWindow [(sample.limb 0).toBitVec,
          (sample.limb 1).toBitVec, (sample.limb 2).toBitVec, 0#64] bl depth)) := by
  rw [sampleQueriesLoop, ite_eq_left h]

/-- Once `count` positions are drawn, the loop returns them, whatever fuel is left. -/
theorem sampleQueriesLoop_done (bl : BitVec 64) (depth count fuel : ℕ) (r : List (BitVec 64))
    (h : count ≤ r.length) : sampleQueriesLoop bl depth count fuel r = pure r := by
  cases fuel with
  | zero => rfl
  | succ f => rw [sampleQueriesLoop, ite_eq_right (by omega)]

end Rv64Verifier.Model.Pcs
