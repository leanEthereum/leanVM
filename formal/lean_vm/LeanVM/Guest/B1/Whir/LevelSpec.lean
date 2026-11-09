/-
  LeanVM.Guest.B1.Whir.LevelSpec

  A level of the Spec's stacked opening as the guest runs it: its head (folds, claims, proof of
  work, queries, glue) then the next level or the tail.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Run

/-!
# A level's head (V:1791-1823)

`levelHead logN index level rest s` is a level of `whirLevelsOpen` up to its glued state: the
fold rounds, the claims (`levelMid`), the proof of work, the query positions, the batching
challenge, the openings, the intro and the glue (`levelRest`); it returns the residual (read at
the last level) and the glued state. `whirLevelsOpen_head`: a level is its head, then the tail
(the last level) or the next level.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A level's queries and glue after its proof of work (V:1812-1823). -/
def levelRest (messageLog index : ℕ) (level : Whir.Level) (levelFolds : List E)
    (s : WhirStateT) (pending : List (E × List E × (List E → E))) : VerifierProgram WhirStateT := do
  let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
  let lam ← VerifierProgram.sampleChallenge
  let queryWeights := powers lam queries.length
  let words ← VerifierProgram.queryOpenings index queries
  let rows : List (List E) :=
    if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
  let enforced := enforcedSum rows levelFolds queryWeights
  let intro ← sumcheckRoundPoly 3 enforced none
  return glueT lam s (pending ++
    [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)])

theorem levelQueries_eq (messageLog index : ℕ) (level : Whir.Level) (levelFolds : List E)
    (s : WhirStateT) (pending : List (E × List E × (List E → E))) :
    levelQueries messageLog index level levelFolds s pending =
      (VerifierProgram.grindProofOfWork Whir.queryGrindingBits).bind fun _ ↦
        levelRest messageLog index level levelFolds s pending := rfl

/-- A level up to its glued state: the residual (read at the last level), the message log after
the level's folds and the state. -/
def levelHead (logN index : ℕ) (level : Whir.Level) (rest : List Whir.Level) (s : WhirStateT) :
    VerifierProgram (List E × ℕ × WhirStateT) := do
  let (s, levelFolds) ← foldRoundsT level.fold s []
  let (residual, pending) ← levelMid (logN - s.folds.length) rest
  VerifierProgram.grindProofOfWork Whir.queryGrindingBits
  let s' ← levelRest (logN - s.folds.length) index level levelFolds s pending
  return (residual, logN - s.folds.length, s')

/-- **A level is its head, then the tail or the next level.** -/
theorem whirLevelsOpen_head (logN laneFolds index : ℕ) (level : Whir.Level)
    (rest : List Whir.Level) (s : WhirStateT) :
    whirLevelsOpen logN laneFolds index (level :: rest) s =
      (levelHead logN index level rest s).bind fun r ↦ match rest with
        | [] => levelTail laneFolds r.2.1 r.1 r.2.2
        | _ :: _ => whirLevelsOpen logN laneFolds (index + 1) rest r.2.2 := by
  rw [whirLevelsOpen_cons]
  rcases rest with _ | ⟨next, rest⟩ <;>
    simp only [levelHead, levelQueries_eq, VerifierProgram.bind_eq, VerifierProgram.pure_eq,
        VerifierProgram.bind_assoc,
      VerifierProgram.ret_bind]

end
end LeanVM.Guest.B1.Whir
