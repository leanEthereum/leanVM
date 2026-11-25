module

public import NativeVm.Model.RingSwitch

/-!
# Phase 7b: the stacked opening

Models `verifyStackedOpening`, `verifyWhir` and `whirLevels` (`Statement/Verifier/Whir.lean`,
`lib.rs`, `whir.rs`), with `sampleQueries`, `extRow`, `subspaceRoots`, `subspaceAt`, `novelBasis`,
`novelEval`, `foldRound`, `foldLanes`, `foldRow`, `inducedWeight` and `glueLevel`.

**Takes** the stack's log-size, the rate exponent and the stack claims (the ring-switched one,
every column claim with a placement, the stack's out-of-domain one). **Samples** the batching
challenge, then runs the ladder (`Whir.ladder`, the statement's parameter table): per level its
fold rounds (four scalars, a grind, `α`, `β`), then either (non-final) the next commitment, the
high part, the out-of-domain sample, a grind, the query positions, `λ`, the openings of the
level's commitment, or (final) the folded lane, a grind, the query positions, the openings and a
sumcheck over the remaining variables. **Returns** nothing: the last check is the final level's.

The statement's functions become data:

* `evaluateBasis` (`fun point ↦ dot scales (claims.map (·.1 point))`) is `BasisW`, the scales and
  the stack claims, applied by `BasisW.eval`;
* a `GluedClaim`'s `weightAt` is `GluedWeight`: `eq p` for the out-of-domain claim
  (`eqEval p`), `induced μ queries weights` for the query batch (`inducedWeight μ queries
  weights`), applied by `GluedWeight.eval`.

A query position is a word (`< 2^64`); `subspaceAt μ` takes its roots and their inverses from a
table computed per call (`subspaceTable`), the statement's `(subspaceRoots μ).map fun r ↦ (r,
r⁻¹)`.
-/

@[expose] public section

namespace NativeVm.Model

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Query positions -/

/-- `(bits >>> shift) % 2^depth` of the 128-bit integer of a challenge's limbs, on words. -/
def queryBits (c : EW) (shift depth : Nat) : UInt64 :=
  let v : UInt64 :=
    if shift = 0 then c.c0
    else if shift < 64 then (c.c0 >>> shift.toUInt64) ||| (c.c1 <<< (64 - shift).toUInt64)
    else if shift < 128 then c.c1 >>> (shift - 64).toUInt64
    else 0
  if 64 ≤ depth then v else v &&& (((1 : UInt64) <<< depth.toUInt64) - 1)

/-- The loop of `sample_queries`. -/
def sampleQueriesAux (depth : Nat) : Nat → Nat → VM (Array UInt64)
  | 0, _ => pure #[]
  | fuel + 1, remaining =>
    if remaining = 0 then pure #[]
    else do
      let c ← sampleChallenge
      let n := min (128 / depth) remaining
      let chunk := (Array.range n).map fun i ↦ queryBits c (i * depth) depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      pure (chunk ++ rest)

/-- `sample_queries(transcript, 2^depth, count)`. -/
def sampleQueries (depth count : Nat) : VM (Array UInt64) := sampleQueriesAux depth count count

/-! ## Rows, the subspace polynomials, the novel basis -/

/-- `ext_row(words)`: words regrouped into `E` values, two per lane. -/
def extRow (row : Array UInt64) : Array EW :=
  (Array.range (row.size / 2)).map fun i ↦ ⟨row.getD (2 * i) 0, row.getD (2 * i + 1) 0⟩

/-- `subspace_roots(log_n)`: `1`, then the normalizers of the subspace polynomials. -/
def subspaceRoots (logN : Nat) : Array UInt64 :=
  let layer0 := (Array.range logN).map fun i ↦ (2 ^ (i + 1) : Nat).toUInt64
  let (roots, _, _) := (List.range logN).foldl (fun (acc : Array UInt64 × UInt64 × Array UInt64) _ ↦
    let (roots, last, layer) := acc
    match (layer.map fun v ↦ kmul v v ^^^ kmul last v).toList with
    | [] => (roots, last, #[])
    | root :: rest => (roots.push root, root, rest.toArray)) (#[1], 1, layer0)
  roots

/-- The roots of `subspace_roots(μ)` with their inverses. -/
def subspaceTable (mu : Nat) : Array (UInt64 × UInt64) :=
  (subspaceRoots mu).map fun root ↦ (root, kinv root)

/-- `Subspace::at(x)` from a table: `What_i(x)`, then `W_(i+1) = W_i² + W_i(β_i)·W_i`. -/
def subspaceAtTable (table : Array (UInt64 × UInt64)) (x : UInt64) : Array UInt64 :=
  (table.foldl (fun (acc : Array UInt64 × UInt64) (root, inverse) ↦
    (acc.1.push (kmul acc.2 inverse), kmul acc.2 acc.2 ^^^ kmul root acc.2)) (#[], x)).1

/-- `Subspace::new(mu).at(x)`. -/
def subspaceAt (mu : Nat) (x : UInt64) : Array UInt64 := subspaceAtTable (subspaceTable mu) x

/-- `novel_basis(what, count)`. -/
def novelBasis (what : Array UInt64) (count : Nat) : Array UInt64 :=
  (what.foldl (fun basis value ↦
    if count ≤ basis.size then basis else basis ++ basis.map (kmul · value)) #[1]).extract 0 count

/-- `novel_eval(coefficients, what)`: `Σ_c p_c·X_c(x)`. -/
def novelEval (coefficients : Array EW) (what : Array UInt64) : EW :=
  sumE (Array.zipWith (fun p b ↦ EW.scale b p) coefficients
    (novelBasis what coefficients.size))

/-! ## Folding -/

/-- `FoldRound`: `α`, `β`. -/
structure FoldRoundW where
  alpha : EW
  beta : EW
  deriving Inhabited

/-- `foldLanes`: adjacent lanes `(f, g)` become `g + (α + β·x)·f`. -/
def foldLanes (x : UInt64) (round : FoldRoundW) (values : Array EW) : Array EW :=
  let factor := round.alpha + EW.scale x round.beta
  (Array.range (values.size / 2)).map fun i ↦
    values.getD (2 * i + 1) 0 + factor * values.getD (2 * i) 0

/-- `fold_row(values, x, rounds)`. -/
def foldRow (values : Array EW) (x : UInt64) (rounds : Array FoldRoundW) : EW :=
  (rounds.foldl (fun values round ↦ foldLanes x round values) values).getD 0 0

/-- `induced_weight(message_log, queries, query_weights, point)`. -/
def inducedWeight (messageLog : Nat) (queries : Array UInt64) (queryWeights point : Array EW) :
    EW :=
  (queryWeights.zip queries).foldl (fun total (weight, query) ↦
    let what := subspaceAt messageLog query
    total + (point.zip what).foldl
      (fun product (challenge, value) ↦ product * (1 + EW.scale (1 ^^^ value) challenge)) weight) 0

/-! ## Weights as data -/

/-- A glued claim's weight function (`GluedClaim.weightAt`). -/
inductive GluedWeight where
  /-- `eqEval p`, the out-of-domain claim's. -/
  | eq (p : Array EW)
  /-- `inducedWeight μ queries weights`, the query batch's. -/
  | induced (mu : Nat) (queries : Array UInt64) (weights : Array EW)
  deriving Inhabited

/-- The weight at a point. -/
def GluedWeight.eval : GluedWeight → Array EW → EW
  | .eq p, x => eqEval p x
  | .induced mu queries weights, x => inducedWeight mu queries weights x

/-- `GluedClaim`: the power of `λ`, the fold rounds before its level, its weight. -/
structure GluedClaimW where
  scalar : EW
  foldStart : Nat
  weight : GluedWeight
  deriving Inhabited

/-- `evaluateBasis` of the stacked opening: the batching scales and the stack claims. -/
structure BasisW where
  scales : Array EW
  claims : Array StackClaimW
  deriving Inhabited

/-- `fun point ↦ dot scales (claims.map fun c ↦ c.1 point)`. -/
def BasisW.eval (b : BasisW) (point : Array EW) : EW :=
  dot b.scales (b.claims.map (·.weight.eval point))

/-! ## The level loop -/

/-- `WhirState`: the running claim, every fold round's `α`, the glued claims. -/
structure WhirStateW where
  claim : EW
  alphas : Array EW
  glued : Array GluedClaimW
  deriving Inhabited

/-- `foldRound`. -/
def foldRound (s : WhirStateW) : VM (WhirStateW × FoldRoundW) := do
  let u0 ← readScalar
  let w ← readScalar
  let c0 ← readScalar
  let c1 ← readScalar
  grind Whir.foldGrindingBits
  let alpha ← sampleChallenge
  let beta ← sampleChallenge
  let claim := u0 + alpha * (u0 + s.claim) + alpha * alpha * w + beta * c0 +
    alpha * beta * (c0 + c1)
  pure ({ s with claim := claim, alphas := s.alphas.push alpha }, ⟨alpha, beta⟩)

/-- `foldRounds n`. -/
def foldRounds (n : Nat) (s : WhirStateW) : VM (WhirStateW × Array FoldRoundW) :=
  (List.range n).foldlM (fun (acc : WhirStateW × Array FoldRoundW) _ ↦ do
    let (s, round) ← foldRound acc.1
    pure (s, acc.2.push round)) (s, #[])

/-- `glueLevel`. -/
def glueLevel (s : WhirStateW) (lam : EW) (mu : Nat) (oodPoint : Array EW) (oodValue : EW)
    (queries : Array UInt64) (queryWeights : Array EW) (batched : EW) : WhirStateW :=
  { s with claim := s.claim + lam * oodValue + lam * lam * batched,
           glued := s.glued ++ #[⟨lam, s.alphas.size, .eq oodPoint⟩,
             ⟨lam * lam, s.alphas.size, .induced mu queries queryWeights⟩] }

/-- `whirLevels`: level `index` and every level after it. -/
def whirLevels (logN laneFolds : Nat) (basis : BasisW) :
    Nat → List Whir.Level → WhirStateW → VM Unit
  | _, [], _ => reject
  | index, level :: rest, s => do
    let (s, rounds) ← foldRounds level.fold s
    let mu := logN - s.alphas.size
    let depth := mu + level.logInvRate
    let lanesOf : Array UInt64 → Array EW := fun row ↦
      if index = 0 then row.reverse.map EW.ofK else extRow row
    match rest with
    | [] => do
      let folded ← readScalars (2 ^ mu + level.fold)
      grind Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      let words ← queryOpenings index queries
      let table := subspaceTable mu
      require ((queries.zip words).all fun (query, row) ↦
        foldRow (lanesOf row) query rounds == novelEval folded (subspaceAtTable table query))
      let (tail, claim) ← sumcheckPlain s.claim 3 mu
      let point := s.alphas ++ tail
      let weight := s.glued.foldl
        (fun weight glued ↦
          weight + glued.scalar * glued.weight.eval (point.extract glued.foldStart point.size))
        (basis.eval (point.extract laneFolds point.size ++ point.extract 0 laneFolds))
      require (weight * multilinearEval (folded.extract 0 (2 ^ mu)) tail == claim)
    | next :: _ => do
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
      let table := subspaceTable mu
      let batched := sumE (Array.zipWith (fun (query, row) queryWeight ↦
        let what := subspaceAtTable table query
        queryWeight * (foldRow (lanesOf row) query rounds +
          EW.scale (what.getD mu 0) (novelEval high what))) (queries.zip words) queryWeights)
      let s := glueLevel s lam mu oodPoint oodValue queries queryWeights batched
      whirLevels logN laneFolds basis (index + 1) rest s

/-- `verifyWhir`: the ladder from commitment `0`. -/
def verifyWhir (logN logInvRate : Nat) (target : EW) (basis : BasisW) : VM Unit := do
  let config ← liftOpt (Whir.ladder logN logInvRate)
  whirLevels logN ((config.head?.map (·.fold)).getD 0) basis 0 config ⟨target, #[], #[]⟩

/-- **Phase 7b** (`verifyStackedOpening`): at most `maxStackedClaims` claims, batched by the
powers of one challenge into one opening. -/
def verifyStackedOpening (stackLog logInvRate : Nat) (claims : Array StackClaimW) : VM Unit := do
  require (claims.size ≤ maxStackedClaims)
  let scales := powers (← sampleChallenge) claims.size
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.value))) ⟨scales, claims⟩

end NativeVm.Model
