/-
  LeanVM.Guest.B1.Whir.LevelSpec

  A level of `whirLevelsOpen`, split as the guest runs it: the fold rounds, then the level's
  claims, queries and glue (a non-final level) or its lane, queries and closing rounds (the
  final one); and the guest's chain of the queries' folds in closed form.
-/

module

public import LeanVM.Guest.B1.Whir.Split
public import LeanVM.Guest.B1.Opening.Interface

/-!
# A level of `whirLevelsOpen` (V: `whirLevels`)

* `levelNext`: a non-final level after its folds: the next commitment, the high part, the
  out-of-domain points and values, the query grind, the positions, the batching grind and `λ`, the
  openings, the glue; `levelLast`: the final level after its folds.
* `whirLevelsOpen_next`, `whirLevelsOpen_last`: a level is its folds, then `levelNext` and the
  next level, or `levelLast`.
* `oqChain_mul_pow`: the guest's chain of the queries' folds `h ← (h + d)·μ` (`oqChain`), times
  `λ^Q`, `λ·μ = 1`, is `Σ_k λ^k d_k`, the Spec's batch with the weights `powers λ Q`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- A non-final level after its folds (V: `whirLevels`, the `next :: _` arm): from the state `s`
and the rounds, up to the glued state. -/
def levelNext (logN index : ℕ) (level next : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : VerifierProgram WhirState := do
  let mu := logN - s.gammas.length
  let depth := mu + level.logInvRate
  let lanesOf : List K → List E := fun row ↦
    if index = 0 then row.reverse.map ofK else extRow row
  let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
  VerifierProgram.readCommitment height width
  let high ← VerifierProgram.readScalars level.fold
  let oodPoints ← sampleOodPoints mu Whir.oodSamples
  let oodValues ← VerifierProgram.readScalars Whir.oodSamples
  VerifierProgram.grindProofOfWork Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  VerifierProgram.grindProofOfWork Whir.batchGrindingBits
  let lam ← VerifierProgram.sampleChallenge
  let queryWeights := powers lam queries.length
  let words ← VerifierProgram.queryOpenings index queries
  let batched := sumE (List.zipWith (fun (query, row) queryWeight ↦
    let what := subspaceAt mu (K.ofBits query)
    queryWeight * (foldRow (lanesOf row) (K.ofBits query) rounds +
      novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)
  return glueLevel s lam mu oodPoints oodValues queries queryWeights batched

/-- The final level after its folds (V: `whirLevels`, the `[]` arm), up to the terminal. -/
def levelLast (logN laneFolds index : ℕ) (level : Whir.Level) (s : WhirState)
    (rounds : List FoldRound) : VerifierProgram WhirEnd := do
  let mu := logN - s.gammas.length
  let depth := mu + level.logInvRate
  let lanesOf : List K → List E := fun row ↦
    if index = 0 then row.reverse.map ofK else extRow row
  let folded ← VerifierProgram.readScalars (2 ^ mu + level.fold)
  VerifierProgram.grindProofOfWork Whir.queryGrindingBits
  let queries ← sampleQueries depth level.queries
  let words ← VerifierProgram.queryOpenings index queries
  VerifierProgram.require ((List.zip queries words).all fun (query, row) ↦
    foldRow (lanesOf row) (K.ofBits query) rounds =
      novelEval folded (subspaceAt mu (K.ofBits query)))
  let (tail, claim) ← sumcheck s.claim 3 (List.replicate mu none)
  let point := s.gammas ++ tail
  let inner := s.glued.foldl
    (fun weight glued ↦ weight + glued.scalar * glued.weightAt (point.drop glued.foldStart)) 0
  return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
    multilinearEval (folded.take (2 ^ mu)) tail, claim⟩

/-- **A non-final level**: its folds, `levelNext`, then the next level. -/
theorem whirLevelsOpen_next (logN laneFolds index : ℕ) (level next : Whir.Level)
    (rest : List Whir.Level) (s : WhirState) :
    whirLevelsOpen logN laneFolds index (level :: next :: rest) s =
      (foldRounds level.fold s).bind fun p ↦
        (levelNext logN index level next p.1 p.2).bind fun s ↦
          whirLevelsOpen logN laneFolds (index + 1) (next :: rest) s := by
  rw [whirLevelsOpen]
  simp only [levelNext, VerifierProgram.bind_eq, VerifierProgram.pure_eq, VerifierProgram.bind_assoc,
    VerifierProgram.ret_bind]

/-- **The final level**: its folds, then `levelLast`. -/
theorem whirLevelsOpen_last (logN laneFolds index : ℕ) (level : Whir.Level) (s : WhirState) :
    whirLevelsOpen logN laneFolds index [level] s =
      (foldRounds level.fold s).bind fun p ↦ levelLast logN laneFolds index level p.1 p.2 := by
  rw [whirLevelsOpen]
  simp only [levelLast, VerifierProgram.bind_eq, VerifierProgram.pure_eq]

/-! ## The chain of the queries' folds -/

/-- `Σ_(k < n) λ^k d_k`. -/
def powSum (lam : E) (ds : ℕ → E) (n : ℕ) : E := ∑ k ∈ Finset.range n, lam ^ k * ds k

theorem powSum_succ (lam : E) (ds : ℕ → E) (n : ℕ) :
    powSum lam ds (n + 1) = powSum lam ds n + lam ^ n * ds n := Finset.sum_range_succ _ _

/-- **The guest's chain of the queries' folds** (`oqChain`, `h ← (h + d)·μ`), times `λ^Q`
(`Q = oqCount odd base N` queries, `λ·μ = 1`), is `Σ_k λ^k d_k`. -/
theorem oqChain_mul_pow {lam mu : E} (hlm : lam * mu = 1) {odd base : ℕ} (hodd : odd ≤ 1)
    (hob : base = 1 ∨ odd = 0) (ds : ℕ → E) : ∀ N, lam ^ oqCount odd base N *
      oqChain odd base mu ds N = powSum lam ds (oqCount odd base N)
  | 0 => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hodd with h | h
    · subst h
      by_cases hb : base = 1 <;> simp [oqChain, oqCount, hb, powSum]
    · have hb : base = 1 := hob.resolve_right (by omega)
      subst h hb
      simp only [oqChain, oqCount, ↓reduceIte, Nat.mul_zero, Nat.add_zero, pow_one]
      rw [show (1 : ℕ) = 0 + 1 from rfl, powSum_succ]
      simp only [powSum, Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add]
      rw [mul_left_comm, hlm, mul_one]
  | N + 1 => by
    have ih := oqChain_mul_pow hlm hodd hob ds N
    by_cases hb : base = 1
    · subst hb
      simp only [oqChain, oqCount, ↓reduceIte] at ih ⊢
      rw [show odd + 2 * (N + 1) = odd + 2 * N + 1 + 1 by ring, powSum_succ, powSum_succ, ← ih]
      linear_combination (lam ^ (odd + 2 * N) * (oqChain odd 1 mu ds N + ds (odd + 2 * N)) *
        (lam * mu + 1) + lam ^ (odd + 2 * N + 1) * ds (odd + 2 * N + 1)) * hlm
    · simp only [oqChain, oqCount, hb, ↓reduceIte] at ih ⊢
      rw [powSum_succ, ← ih]
      linear_combination (lam ^ N * (oqChain odd base mu ds N + ds N)) * hlm

end
end LeanVM.Guest.B1.Whir
