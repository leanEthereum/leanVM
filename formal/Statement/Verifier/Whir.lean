module

public import Statement.Verifier.Sumcheck

/-!
# The WHIR opening (`whir.rs`, `lib.rs`)

The opening of [CWYZ26]'s affine folds (Annex B, `fig:protocol`): a level's rounds fold its
lanes by the affine combiner `G + (α + β·X)·F`, the claim carried by four scalars a round
and the weight folded by the same `α`, so the `α`s are the weight's point. A non-final level then commits
the folded lane's low part, sends its high part, and glues its out-of-domain claim and its queries,
each opened row folded as the lanes were and corrected by the high part. The final level sends the
whole folded lane, checks the queries against it, and closes with a sumcheck over the low part.

**Commitments.** The Rust reads a Merkle root as two scalars (`Digest::from_halves` of
`next_scalars(2)`, `whir.rs`) and opens it a level later with
`transcript.merkle(current_root, block_length, &queries, leaf_words)` (`whir.rs`). The
language's `commit height width` fixes the matrix shape when the root is read, so the shape is
computed from the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the link, `commitStack`)
  is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(μ_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `2 · 2^folds[ℓ+1]` words, `μ_ℓ` the variables left
  after level `ℓ`'s folds.

Level `ℓ` therefore opens commitment `ℓ` (`VerifierProgram.queryOpenings ℓ`). The rows come back as
raw words; the level-0 reversal and the regrouping of deeper rows into `E` (`ext_row`) are the
program's.

`derive_config` is `LeanVM.Parameters.Whir.ladder`. `induced_weight` requires
`point.len() == message_log` (`InducedBasisDimensions`, `whir.rs`); every glued claim is
evaluated at `point[fold_start..]`, the `α`s from `fold_start` on and then the tail's, of length
`log_n − fold_start = μ` of its level, so the check always holds and is not repeated. The error
after the level loop (`WhirNoTerminalLevel`, `whir.rs`) is `VerifierProgram.fail` on an empty
ladder, which `derive_config` never returns. `novel_basis` asserts it has a basis element for every
coefficient (`whir.rs`): on the final level `2^μ + fold` coefficients against `2^(μ+1)`
elements, which holds as the ladder leaves the final level `μ ≥ 2` variables and folds at most `4`;
here a missing element would leave its coefficient out.
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-- The loop of `sample_queries`: each sample yields up to `128 / depth` positions of `depth`
bits, low bits first, from the 128-bit integer of its two limbs (`whir.rs`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → VerifierProgram (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← VerifierProgram.sampleChallenge)
      let n := min (128 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`whir.rs`), from the block's log-length
`depth` (the Rust recovers it from the length by `log2_strict`, which cannot fail).
`count` rounds of fuel suffice: each yields `min(128 / depth, remaining) ≥ 1` positions, as
`depth ≤ 64`. -/
def sampleQueries (depth count : ℕ) : VerifierProgram (List ℕ) := sampleQueriesAux depth count count

/-- `ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode, two
per lane (`whir.rs`). A trailing odd word, which the leaf width rules out, is dropped, as
the Rust drops it. -/
def extRow : List K → List E
  | c0 :: c1 :: rest => E.ofLimbs c0 c1 :: extRow rest
  | _ => []

/-- The layers of `subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`whir.rs`). -/
def subspaceRootsAux : ℕ → K → List K → List K
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value * value + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomials' normalizers, the
subspaces spanned by powers of `x`, so in `K` (`whir.rs`). -/
def subspaceRoots (logN : ℕ) : List K :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ K.ofBits (2 ^ (i + 1)))

/-- The loop of `Subspace::at`: `What_i(x)` from `W_i(x)`, then `W_(i+1) = W_i^2 + W_i(β_i)·W_i`. -/
def subspaceAtAux : List (K × K) → K → List K
  | [], _ => []
  | (root, inverse) :: rest, basis =>
    basis * inverse :: subspaceAtAux rest (basis * basis + root * basis)

/-- `Subspace::new(mu).at(x)`: the normalized subspace polynomials `What_i(x) = W_i(x) / W_i(β_i)`
for `i ≤ mu` (`whir.rs`; `K::inv` maps zero to zero, as `⁻¹` does). -/
def subspaceAt (mu : ℕ) (x : K) : List K :=
  subspaceAtAux ((subspaceRoots mu).map fun root ↦ (root, root⁻¹)) x

/-- `novel_basis(what, count)`: `X_c(x) = Π_{c_i = 1} What_i(x)` for every `c < count`, doubling
the basis by each `What_i` until it has `count` elements (`whir.rs`; Annex D's novel
basis). -/
def novelBasis (what : List K) (count : ℕ) : List K :=
  (what.foldl (fun basis value ↦
    if count ≤ basis.length then basis else basis ++ basis.map (· * value)) [1]).take count

/-- `novel_eval(coefficients, what)`: `P(x) = Σ_c p_c·X_c(x)` (`whir.rs`). -/
def novelEval (coefficients : List E) (what : List K) : E :=
  sumE (List.zipWith (fun p b ↦ p * ofK b) coefficients (novelBasis what coefficients.length))

/-- The challenges of one fold round that act on the oracle, `P = G + (α + β·X)·F`
(`FoldRound`, `whir.rs`). -/
structure FoldRound where
  /-- `α`, the combiner's constant term. -/
  alpha : E
  /-- `β`, the combiner's coefficient of `X`. -/
  beta : E

/-- One fold of `fold_row`: adjacent lanes `(f, g)` become `g + (α + β·x)·f`. -/
def foldLanes (x : K) (round : FoldRound) : List E → List E
  | f :: g :: rest => (g + (round.alpha + round.beta * ofK x) * f) ::
    foldLanes x round rest
  | _ => []

/-- `fold_row(values, x, rounds)`: an opened row, its lanes in `eq_kernel` order, folded at its
domain point `x` round by round as the prover folds the lanes (`whir.rs`; the pairing of
[CWYZ26], Theorem 5.2). The Rust asserts one value is left, one round per lane variable, which
the level's shape always gives; `0` otherwise. -/
def foldRow (values : List E) (x : K) (rounds : List FoldRound) : E :=
  (rounds.foldl (fun values round ↦ foldLanes x round values) values).headD 0

/-- `induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + What_k(x_q)))`, the novel-basis
column weight of Annex D, Lemma `lem:colweight` (`whir.rs`). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let what := subspaceAt messageLog (K.ofBits query)
    total + (List.zip point what).foldl
      (fun product (challenge, value) ↦ product * (1 + challenge * ofK (1 + value))) weight) 0

/-- `GluedClaim`: a claim glued into the running claim, and the weight it owes back
(`whir.rs`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold rounds preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`whir.rs`) -/

/-- The running state of `verify_whir`: the running `claim`, every fold round's `α` so far, and
the glued claims so far. -/
structure WhirState where
  /-- `claim`: the running claim. -/
  claim : E
  /-- `alphas`: every fold round's `α` so far, the coordinates the weight is folded at. -/
  alphas : List E
  /-- `glued`: the glued claims so far. -/
  glued : List GluedClaim

/-- One fold round (`whir.rs`): the four scalars `u0, w, c0, c1`
(`⟨W₀, G⟩, ⟨W₀ + W₁, F⟩, ⟨W₀, XF⟩, ⟨W₁, XF⟩`); a grind and `α, β`; the claim folded at `α`,
`u0 + α (u0 + claim) + α² w + β c0 + α β (c0 + c1)`. -/
def foldRound (s : WhirState) : VerifierProgram (WhirState × FoldRound) := do
  let u0 ← VerifierProgram.readScalar
  let w ← VerifierProgram.readScalar
  let c0 ← VerifierProgram.readScalar
  let c1 ← VerifierProgram.readScalar
  VerifierProgram.grindProofOfWork Whir.foldGrindingBits
  let alpha ← VerifierProgram.sampleChallenge
  let beta ← VerifierProgram.sampleChallenge
  let claim := u0 + alpha * (u0 + s.claim) + alpha * alpha * w + beta * c0 +
    alpha * beta * (c0 + c1)
  return ({ s with claim := claim, alphas := s.alphas ++ [alpha] }, ⟨alpha, beta⟩)

/-- A level's fold rounds, in order. -/
def foldRounds : ℕ → WhirState → VerifierProgram (WhirState × List FoldRound)
  | 0, s => return (s, [])
  | n + 1, s => do
    let (s, round) ← foldRound s
    let (s, rounds) ← foldRounds n s
    return (s, round :: rounds)

/-- The shape of the commitment a level opens: `2^(μ + rate)` leaves of `width` words, `μ` the
variables left after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- Glue a non-final level's claims into the running claim (`whir.rs`): the
out-of-domain claim with `λ`, its weight `eq(point, ·)`, then the query batch with `λ²`, its
weight the induced one. -/
def glueLevel (s : WhirState) (lam : E) (mu : ℕ) (oodPoint : List E) (oodValue : E)
    (queries : List ℕ) (queryWeights : List E) (batched : E) : WhirState :=
  { s with claim := s.claim + lam * oodValue + lam * lam * batched,
           glued := s.glued ++ [⟨lam, s.alphas.length, fun x ↦ eqEval oodPoint x⟩,
             ⟨lam * lam, s.alphas.length, inducedWeight mu queries queryWeights⟩] }

/-- One level of `verify_whir` and every level after it (`whir.rs`). `index` is the
level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → VerifierProgram Unit
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, rounds) ← foldRounds level.fold s
    let mu := logN - s.alphas.length
    let depth := mu + level.logInvRate
    -- The opened rows' lanes in `eq_kernel` order: level 0's leaf image reversed, a deeper
    -- level's regrouped (`whir.rs`).
    let lanesOf : List K → List E := fun row ↦
      if index = 0 then row.reverse.map ofK else extRow row
    match rest with
    | [] => do
      -- The final level (`whir.rs`).
      let folded ← VerifierProgram.readScalars (2 ^ mu + level.fold)
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      let words ← VerifierProgram.queryOpenings index queries
      VerifierProgram.require ((List.zip queries words).all fun (query, row) ↦
        foldRow (lanesOf row) (K.ofBits query) rounds =
          novelEval folded (subspaceAt mu (K.ofBits query)))
      let (tail, claim) ← sumcheck s.claim 3 (List.replicate mu none)
      let point := s.alphas ++ tail
      let weight := s.glued.foldl
        (fun weight glued ↦ weight + glued.scalar * glued.weightAt (point.drop glued.foldStart))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      VerifierProgram.require (weight * multilinearEval (folded.take (2 ^ mu)) tail = claim)
    | next :: _ => do
      -- A non-final level (`whir.rs`).
      let (height, width) := levelShape mu next (2 * 2 ^ next.fold)
      VerifierProgram.readCommitment height width
      let high ← VerifierProgram.readScalars level.fold
      -- Its out-of-domain point (`read_ood`, `lib.rs`).
      VerifierProgram.grindProofOfWork Whir.oodGrindingBits
      let oodPoint ← VerifierProgram.sampleChallenges mu
      let oodValue ← VerifierProgram.readScalar
      VerifierProgram.grindProofOfWork Whir.queryGrindingBits
      let queries ← sampleQueries depth level.queries
      let lam ← VerifierProgram.sampleChallenge
      let queryWeights := powers lam queries.length
      let words ← VerifierProgram.queryOpenings index queries
      -- Each row folds to the folded lane at its point; less the high part,
      -- `What_μ(x) Σ_j p_(2^μ + j) X_j(x)`, it is the low part's value there.
      let batched := sumE (List.zipWith (fun (query, row) queryWeight ↦
        let what := subspaceAt mu (K.ofBits query)
        queryWeight * (foldRow (lanesOf row) (K.ofBits query) rounds +
          novelEval high what * ofK (what.getD mu 0))) (List.zip queries words) queryWeights)
      let s := glueLevel s lam mu oodPoint oodValue queries queryWeights batched
      whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(transcript, log_n, log_inv_rate, target, root, evaluate_basis)`, the root being
commitment `0` (`whir.rs`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : VerifierProgram
    Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config ⟨target, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `lib.rs`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : VerifierProgram Unit := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  match config with
  | [] => VerifierProgram.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    VerifierProgram.readCommitment height width

/-- `read_ood(transcript, stack_log, OOD_GRINDING_BITS)`: the stack commitment's out-of-domain
sample, read right after its root, outside the PCS: a grind, a point `z` of the stack's variables,
then the stack's multilinear at `z`; its claim `eq(z, ·)` is the last of the stacked opening's
(`lib.rs`). A later level reads its point the same way, inline in `whirLevels`. -/
def readOod (stackLog : ℕ) : VerifierProgram StackClaim := do
  VerifierProgram.grindProofOfWork Whir.oodGrindingBits
  let z ← VerifierProgram.sampleChallenges stackLog
  let value ← VerifierProgram.readScalar
  return (fun x ↦ eqEval z x, value)

end LeanVM.Protocol.Verifier

end
