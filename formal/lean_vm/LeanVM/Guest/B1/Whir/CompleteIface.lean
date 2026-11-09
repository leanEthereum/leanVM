/-
  LeanVM.Guest.B1.Whir.CompleteIface

  The completeness interface of `open_stacked` (B1-b): the run it completes on, the two
  hypotheses on that run (no zero challenge, openings that agree in the caps), and the statement.
-/

module

public import LeanVM.Protocol.Verifier.WhirTarget
public import LeanVM.Guest.B1.Whir.Interface
public import LeanVM.Guest.B1.Opening.Meaning
public import LeanVM.Protocol.WithHash
public import LeanVM.Guest.AcceptableChild

/-!
# `open_stacked`'s completeness: the interface

**The run.** An honest child's stacked WHIR opening is an accepting run of `whirOpen μ r target`
(`RunsWith`) from the sponge `⟨capOf S, []⟩` (the state `S` of the caller's sponge, nothing
waiting), the words `xs` and the openings `os`, the stack's root committed with its shape.

**Two hypotheses on the run**, without which the statement is false (DESIGN §5.2):

* `NoZeroChallenge μ r target S xs os root` (DESIGN §5.2.1): the same run passes
  `whirOpenNZ`, which is `whirOpen` refusing a zero fold challenge (`foldRoundsNZ`), a zero tail
  challenge (`tailRoundsNZ`) and a zero batching challenge `λ` of a level. The guest divides by
  them: `μ = 1/λ` (`opening_queries`, G:1400) and the basis coefficients `(1 + c)/(c·inv)`
  (G:1709, 1714). It fails with probability about `(number of challenges)·2^-192` per proof.
* `CapsAgree μ r target S xs os root` (DESIGN §5.2.3): at every query step of the run
  (`queryStepsOf`, `Fs`-level `Compile.run`), two openings giving one node of the tree a digest
  (`NodeIs`: on their climb or as a sibling) give it the same (`BatchAgrees`). The guest writes
  each level's Merkle cap once (write-once memory), so openings meeting in the cap must agree
  there; the Spec checks each opening alone against the root. One tree's openings agree; two that
  disagree would collide the root's preimages.

**The statement** (`open_stacked_complete_Spec`, placed in the style the completeness of the
whole guest consumes): for every base `b`, the function's own memory is one layout `L` of
`(exponent, words)` runs within `[b, b + n)` (`LayoutWithin`), its two point buffers among them;
on every memory holding `L` (`HoldsLayout`) and the words `xs` at the cursor, the call of the
candidate's specialization on `(capOf S, target, root's two cells, cursor)` returns the run's
claim, the pointers of the point buffers, its glued weight and its residual's value. Proved as
`open_stacked_complete_holds`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## No zero challenge -/

/-- `foldRounds` refusing a zero challenge. -/
def foldRoundsNZ : ℕ → WhirStateT → List E → VerifierProgram (WhirStateT × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← VerifierProgram.sampleChallenge
    VerifierProgram.require (challenge ≠ 0)
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRoundsNZ n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- `tailRounds` refusing a zero challenge. -/
def tailRoundsNZ : ℕ → E → List E → VerifierProgram (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← VerifierProgram.sampleChallenge
    VerifierProgram.require (challenge ≠ 0)
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRoundsNZ n target quad
      return (challenge :: rest, target)

/-- `whirLevelsOpen` refusing a zero fold, tail or batching challenge. -/
def whirLevelsOpenNZ (logN laneFolds : ℕ) : ℕ → List Whir.Level → WhirStateT → VerifierProgram
    WhirEnd
  | _, [], _ => VerifierProgram.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRoundsNZ level.fold s []
    let messageLog := logN - s.folds.length
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← VerifierProgram.readScalars (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        VerifierProgram.readCommitment height width
        let oodPoint ← VerifierProgram.sampleChallenges messageLog
        let oodValue ← VerifierProgram.readScalar
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    VerifierProgram.grindProofOfWork Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← VerifierProgram.sampleChallenge
    VerifierProgram.require (lam ≠ 0)
    let queryWeights := powers lam queries.length
    let words ← VerifierProgram.queryOpenings index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glueT lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRoundsNZ messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let inner := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds)) 0
      return ⟨point.drop laneFolds ++ point.take laneFolds, inner,
        multilinearEval residual tailFolds, target⟩
    | _ :: _ => whirLevelsOpenNZ logN laneFolds (index + 1) rest s

/-- `whirOpen` refusing a zero fold, tail or batching challenge. -/
def whirOpenNZ (logN logInvRate : ℕ) (target : E) : VerifierProgram WhirEnd := do
  let config ← liftOption (Whir.ladder logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevelsOpenNZ logN ((config.head?.map (·.fold)).getD 0) 0 config ⟨target, quad, [], []⟩

/-- **No zero challenge** (DESIGN §5.2.1): the run of `whirOpen μ r target` from the sponge
`⟨capOf S, []⟩` on the words `xs` and the openings `os`, the root committed, passes
`whirOpenNZ`: no fold challenge, tail challenge or level's batching challenge `λ` is zero. -/
def NoZeroChallenge (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E)
    (os : List (List Opening)) (root : Digest) : Prop :=
  ∃ (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
    RunsWith (whirOpenNZ μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots'

/-! ## Openings that agree in the caps -/

/-- The state of an `Fs`-level run: the carried sponge, the words and openings left, the roots. -/
structure FSt where
  sponge : Fs
  stream : List E
  openings : List (List Opening)
  roots : List (Digest × ℕ × ℕ)

/-- **The query steps of a run** (`Compile.run` on the carried sponge, Keccak-256): each `query`
step as its tree's height and its positions, each with the opening it consumes. -/
def queryStepsOf {α : Type} : VerifierProgram α → FSt → List (ℕ × List (ℕ × Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, s => match s.stream with
    | [] => []
    | x :: xs => queryStepsOf (k x) { s with sponge := s.sponge.absorb x dsObserve, stream := xs }
  | .sample k, s => queryStepsOf (k s.sponge.squeeze.1) { s with sponge := s.sponge.squeeze.2 }
  | .grind bits k, s => match s.stream with
    | [] => []
    | n :: xs =>
      let sq := (s.sponge.absorb n dsPowNonce).squeeze
      if powOk bits n sq.1 then queryStepsOf k { s with sponge := sq.2, stream := xs } else []
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs =>
      match digestFromHalves (x0, x1) with
      | some root =>
        queryStepsOf k { s with
          sponge := (s.sponge.absorb x0 dsObserve).absorb x1 dsObserve
          stream := xs
          roots := s.roots ++ [(root, height, width)] }
      | none => []
    | _ => []
  | .query i ps k, s => match s.roots[i]?, s.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (Compile.openPhaseWithHash (m := Id) keccak256 root height width ps phase) with
      | some rows => (height, ps.zip phase) :: queryStepsOf (k rows) { s with openings := rest }
      | none => []
    | _, _ => []

/-- The heap index of the node at level `l` (the leaves at `0`) above the leaf `q` of a tree of
height `depth`. -/
def heapNode (depth q l : ℕ) : ℕ := 2 ^ (depth - l) + q / 2 ^ l

/-- The heap index of the sibling of the node at level `l < depth` above the leaf `q`. -/
def sibNode (depth q l : ℕ) : ℕ := 2 * heapNode depth q (l + 1) + (!q.testBit l).toNat

/-- **The opening `o` at `q` gives the heap node `v` the digest `d`**: `v` is on its climb, with
the climb's digest there, or is the sibling it carries at a level. -/
def NodeIs (depth : ℕ) (a : ℕ × Opening) (v : ℕ) (d : Digest) : Prop :=
  (∃ l ≤ depth, v = heapNode depth a.1 l ∧ d = climbD (merkleLeafDigest a.2.leaf) a.1 (a.2.path.take l)) ∨
    ∃ l < depth, v = sibNode depth a.1 l ∧ d = a.2.path.getD l default

/-- The openings of one step agree wherever they meet. -/
def BatchAgrees (depth : ℕ) (qs : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ qs, ∀ b ∈ qs, ∀ v d d', NodeIs depth a v d → NodeIs depth b v d' → d = d'

/-- **The openings agree in the caps** (DESIGN §5.2.3): at every query step of the run of
`whirOpen μ r target` from `⟨capOf S, []⟩` on `xs` and `os`, the root committed, the step's
openings agree wherever they meet. -/
def CapsAgree (μ r : ℕ) (target : E) (S : KeccakState) (xs : List E)
    (os : List (List Opening)) (root : Digest) : Prop :=
  ∀ b ∈ queryStepsOf (whirOpen μ r target) ⟨⟨capOf S, []⟩, xs, os, [(root, stackShape μ r)]⟩,
    BatchAgrees b.1 b.2

/-! ## Memory layouts -/

/-- A layout of words: runs `(e, ws)`, word `j` at the address `g^(e + j)`. -/
abbrev OsLayout : Type := List (ℕ × List E)

/-- The memory holds the layout. -/
def HoldsLayout (rd : Reader) (L : OsLayout) : Prop :=
  ∀ q ∈ L, ∀ j (h : j < q.2.length), rd (addressOfIndex (q.1 + j)) = some q.2[j]

/-- The layout lies in the exponents `[b, b + n)`. -/
def LayoutWithin (L : OsLayout) (b n : ℕ) : Prop :=
  ∀ q ∈ L, b ≤ q.1 ∧ q.1 + q.2.length ≤ b + n

/-! ## The statement -/

/-- **`open_stacked` is complete** at every candidate: on an accepting run of `whirOpen μ r target`
from the caller's sponge state `S` (nothing waiting), the words `xs` and the openings `os`, with
no zero challenge and openings that agree in the caps, for every base `b` the function's own
memory is a layout `L` within `[b, b + n)` holding its two point buffers (the run's point,
zero-padded, and one plus each of its coordinates, one-padded); on every memory holding `L` and the
words `xs` at the cursor, the call returns the run's claim, the point buffers' pointers, its
glued weight and its residual's value. Proved as `open_stacked_complete_holds`. -/
def open_stacked_complete_Spec : Prop :=
  ∀ (μ r : ℕ), 22 ≤ μ → μ ≤ 28 → 1 ≤ r → r ≤ 4 →
    ∀ (S : KeccakState) (root : Digest) (target cur : E) (xs : List E) (os : List (List Opening))
      (w : WhirEnd) (s' : Fs) (roots' : List (Digest × ℕ × ℕ)),
      RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots' →
      NoZeroChallenge μ r target S xs os root → CapsAgree μ r target S xs os root →
      ∀ b : ℕ, ∃ (n : ℕ) (L : OsLayout) (pt pt1 : ℕ), LayoutWithin L b n ∧
        (pt, w.point ++ List.replicate (pointCap - μ) 0) ∈ L ∧
        (pt1, w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1) ∈ L ∧
        ∀ rd : Reader, HoldsLayout rd L → ReadsAt rd cur xs →
          coreProgram.Rel rd (openName μ r)
            (capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur])
            [w.target, ofK (addressOfIndex pt), ofK (addressOfIndex pt1), w.inner, w.residual]

end
end LeanVM.Guest.B1.Whir
