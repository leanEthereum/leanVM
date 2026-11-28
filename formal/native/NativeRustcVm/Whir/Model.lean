module

public import NativeRustcVm.Whir.Rep

/-!
# `whirLevels` as `whir.rs` splits it

`whir_levels` runs a level's fold rounds (`fold_rounds`), then hands the level to `next_level`
(before the last) or `final_level` (the last), `μ` the variables left. Their models are
`whirLevels`' two branches after the fold rounds: `nextLevelM` (the next commitment, the
out-of-domain sample, the queries batched, `glueLevel`) and `finalLevelM` (the folded lane, the
queries checked, the last sumcheck and the end check), the queries' work by `each_row`:
`batchedOf` for a non-final level, `finalOk` for the final one. `whirLevels_nil_cons`,
`whirLevels_cons_cons`: the model is the fold rounds then these.
-/

namespace NativeRustcVm.Whir

open NativeVm.Model LeanVM.Parameters

@[expose] public section

/-- A non-final level's batched value: each opened row folded, corrected by the high part's
`novelEval` at its `What`s, weighted by its query's weight, summed. -/
def batchedOf (index mu : Nat) (rounds : Array FoldRoundW) (high : Array EW) (queries : Array UInt64)
    (words : Array (Array UInt64)) (queryWeights : Array EW) : EW :=
  let table := subspaceTable mu
  sumE (Array.zipWith (fun (query, row) queryWeight ↦
    let what := subspaceAtTable table query
    queryWeight * (foldRow (lanesOf index row) query rounds +
      EW.scale (what.getD mu 0) (novelEval high what))) (queries.zip words) queryWeights)

/-- The final level's check of its opened rows against the folded lane. -/
def finalOk (index mu : Nat) (rounds : Array FoldRoundW) (folded : Array EW)
    (queries : Array UInt64) (words : Array (Array UInt64)) : Bool :=
  let table := subspaceTable mu
  (queries.zip words).all fun (query, row) ↦
    foldRow (lanesOf index row) query rounds == novelEval folded (subspaceAtTable table query)

/-- The final weight at the sumcheck's point `alphas ++ tail`. -/
def finalWeight (laneFolds : Nat) (basis : BasisW) (s : WhirStateW) (tail : Array EW) : EW :=
  let point := s.alphas ++ tail
  s.glued.foldl
    (fun weight glued ↦
      weight + glued.scalar * glued.weight.eval (point.extract glued.foldStart point.size))
    (basis.eval (point.extract laneFolds point.size ++ point.extract 0 laneFolds))

/-- **`next_level`**: level `index` (`level`, then `next`) after its fold rounds `rounds`, `μ`
variables left; the glued state. -/
def nextLevelM (index : Nat) (level next : Whir.Level) (mu : Nat) (s : WhirStateW)
    (rounds : Array FoldRoundW) : VM WhirStateW := do
  let depth := mu + level.logInvRate
  let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
  readCommitment height width
  let high ← readScalars level.fold
  grind Whir.oodGrindingBits
  let oodPoint ← sampleChallenges mu
  let oodValue ← readScalar
  grind Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  let lam ← sampleChallenge
  let queryWeights := powers lam queries.size
  let words ← queryOpenings index queries
  pure (glueLevel s lam mu oodPoint oodValue queries queryWeights
    (batchedOf index mu rounds high queries words queryWeights))

/-- **`final_level`**: the last level `index` after its fold rounds `rounds`, `μ` variables
left. -/
def finalLevelM (index : Nat) (level : Whir.Level) (mu laneFolds : Nat) (basis : BasisW)
    (s : WhirStateW) (rounds : Array FoldRoundW) : VM Unit := do
  let depth := mu + level.logInvRate
  let folded ← readScalars (2 ^ mu + level.fold)
  grind Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  let words ← queryOpenings index queries
  require (finalOk index mu rounds folded queries words)
  let (tail, claim) ← sumcheckPlain s.claim 3 mu
  require (finalWeight laneFolds basis s tail * multilinearEval (folded.extract 0 (2 ^ mu)) tail
    == claim)

/-- The last level: its fold rounds, then `final_level`. -/
theorem whirLevels_single (logN laneFolds : Nat) (basis : BasisW) (index : Nat)
    (level : Whir.Level) (s : WhirStateW) :
    whirLevels logN laneFolds basis index [level] s =
      (foldRounds level.fold s >>= fun r ↦
        finalLevelM index level (logN - r.1.alphas.size) laneFolds basis r.1 r.2) := by
  simp only [whirLevels, finalLevelM]
  rfl

/-- A level before the last: its fold rounds, `next_level`, the levels after it. -/
theorem whirLevels_cons_cons (logN laneFolds : Nat) (basis : BasisW) (index : Nat)
    (level next : Whir.Level) (rest : List Whir.Level) (s : WhirStateW) :
    whirLevels logN laneFolds basis index (level :: next :: rest) s =
      (foldRounds level.fold s >>= fun r ↦
        nextLevelM index level next (logN - r.1.alphas.size) r.1 r.2 >>=
          whirLevels logN laneFolds basis (index + 1) (next :: rest)) := by
  simp only [whirLevels, nextLevelM, bind_assoc, pure_bind]
  rfl

end

end NativeRustcVm.Whir
