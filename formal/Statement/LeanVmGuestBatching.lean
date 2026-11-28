module

public import Statement.LeanVm

/-!
# The leanISA guest program: the batching of the children's claims

A node folds its children's claims on the bytecode into the one claim it defers (`batch`): a
Fiat-Shamir transcript draws `λ`, whose powers weigh the claims, then a sumcheck reduces their
combination to one point. It is written once over any permutation (`batchWith`): `batch` runs it
over Keccak-f[1600], `BatchingSound` (`LeanVmGuest.lean`) over the model's `π`.

Transcribed from `aggregate_claims` (`guests/lean_ethereum.py`) and `aggregate_deferred_claims`
(`crates/aggregation/src/deferred.rs`).
-/

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The claims -/

/-- The claim a statement defers on the stacked bytecode: its value at a point
(`DeferredBytecodeClaim`, `crates/aggregation/src/deferred.rs`), the shape of a proof's claim. -/
abbrev DeferredBytecodeClaim : Type := BytecodeClaim

/-- A claim's cells: the point, then the value (`DeferredBytecodeClaim::cells`). -/
def DeferredBytecodeClaim.cells (claim : DeferredBytecodeClaim) : List E :=
  claim.bytecodePoint ++ [claim.bytecodeValue]

/-- What a node knows of one child. -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- The claim the child's proof makes. -/
  freshClaim : DeferredBytecodeClaim
  /-- The claim the child's statement defers. -/
  carriedClaim : DeferredBytecodeClaim

/-- A child's words: its public input's two cells, then its two claims (`AGG_CHILD_WORDS`). -/
def ChildClaims.words (child : ChildClaims) : List E :=
  [(digestHalves child.publicInput).1, (digestHalves child.publicInput).2] ++
    child.freshClaim.cells ++ child.carriedClaim.cells

/-- The prover's part of a batching (`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchingHints where
  /-- The nonce of the proof of work before `λ`. -/
  lambdaGrindNonce : E
  /-- Each round's message `(g(1), g(∞))`. -/
  sumcheckMessages : List (E × E)
  /-- The bytecode's value at the sumcheck's final point. -/
  finalBytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`). -/
def batchingLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

end LeanVM.Node

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- The most children a node has (`MAX_RECURSIONS`). -/
def maxRecursions : ℕ := 16

/-- The bits of the proof of work before `λ`, which weighs at most `2 · maxRecursions` claims:
`grinding_bits(2 · MAX_RECURSIONS - 1)` (`BATCH_LAM_GRIND_BITS`), `2`. Nonzero, so the hints always
carry a nonce (the guest and the Rust skip it at zero bits). -/
def batchLambdaGrindBits : ℕ := grindingBits (2 * maxRecursions - 1)

/-- The zeros that pad `wordCount` words to a whole rate. -/
def zerosToWholeRate (wordCount : ℕ) : ℕ := (rateScalars - wordCount % rateScalars) % rateScalars

/-- Words padded with zeros to a whole rate (`pad`). -/
def padToRate (words : List E) : List E :=
  words ++ List.replicate (zerosToWholeRate words.length) 0

/-- The weights of `λ`: child `i`'s pair `(λ^(2i), λ^(2i+1))`, for its fresh and carried claims. -/
def lambdaPowers (challenge : E) (childCount : ℕ) : List (E × E) :=
  (List.range childCount).map fun i ↦ (challenge ^ (2 * i), challenge ^ (2 * i + 1))

/-- The children's claimed values, weighted. -/
def batchedClaim (children : List ChildClaims) (lambdas : List (E × E)) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * child.freshClaim.bytecodeValue + l.2 * child.carriedClaim.bytecodeValue) children lambdas)

/-- The `λ`-weighted sum of `eq(p, point)` over the children's claim points `p`. -/
def batchedBytecodeWeight (children : List ChildClaims) (lambdas : List (E × E))
    (point : List E) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * eqEval child.freshClaim.bytecodePoint point +
      l.2 * eqEval child.carriedClaim.bytecodePoint point) children lambdas)

/-- **A round's polynomial**, of degree two, from the claim before it and its message
`(g(1), g(∞))`: `g(0) = claim + g(1)`, `g(x) = (g(∞)·x + g(0) + g(1) + g(∞))·x + g(0)`. -/
def sumcheckRoundPolynomial (claim : E) (g : E × E) (x : E) : E :=
  let g1 := g.1
  let gInf := g.2
  let g0 := claim + g1
  (gInf * x + (g0 + g1 + gInf)) * x + g0

/-! ## The transcript -/

section Transcript

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- Absorb a scalar (`observe`). -/
def observe (x : E) : StateT Sponge m Unit :=
  fun sp ↦ (fun sp' ↦ ((), sp')) <$> Compile.absorb π sp x dsObserve

/-- Squeeze a challenge (`sample`). -/
def sample : StateT Sponge m E := Compile.squeeze π

/-- A proof of work of `bits ≥ 1` bits on `nonce` (`Sponge::absorb_nonce`, `grind_check`): whether
the permutation's third lane has `bits` low zero bits. -/
def grind (bits : ℕ) (nonce : E) : StateT Sponge m Bool :=
  fun sp ↦ (fun p ↦ (powOk bits p.1, p.2)) <$> Compile.absorbNonce π sp nonce

/-- The sumcheck's rounds from `claim`: each absorbs `g(1)` and `g(∞)`, squeezes `r`, and moves to
`g(r)` (a round grinds `grindingBits 2 = 0` bits). The challenges and the final claim. -/
def batchRounds : E → List (E × E) → StateT Sponge m (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observe (m := m) π g1
    observe (m := m) π gInf
    let r ← sample (m := m) π
    let (rs, final) ← batchRounds (sumcheckRoundPolynomial claim (g1, gInf) r) rest
    return (r :: rs, final)

/-- **The batching over `π`**, for points of `vars` coordinates: at most `maxRecursions` children
with claims of `vars` coordinates and hints of `vars` rounds, else nothing. From `π` of the label's
hash, absorb the count and the padded children, check the proof of work, squeeze `λ`, run the
sumcheck; the claim deferred at its challenges if the final check passes. -/
def batchWith (vars : ℕ) (children : List ChildClaims) (h : BatchingHints) :
    m (Option DeferredBytecodeClaim) :=
  if children.length ≤ maxRecursions ∧ h.sumcheckMessages.length = vars ∧
      ∀ c ∈ children, c.freshClaim.bytecodePoint.length = vars ∧
        c.carriedClaim.bytecodePoint.length = vars then do
    let seed ← π (seedInput (← keccak256With π batchingLabel) (Vector.replicate 4 0))
    go.run' ⟨seed, [], none⟩
  else pure none
where
  /-- The transcript. -/
  go : StateT Sponge m (Option DeferredBytecodeClaim) := do
    for x in padToRate [gpow children.length] do observe (m := m) π x
    for c in children do
      for x in padToRate c.words do observe (m := m) π x
    if ← grind (m := m) π batchLambdaGrindBits h.lambdaGrindNonce then
      let lambdas := lambdaPowers (← sample (m := m) π) children.length
      let (r, final) ← batchRounds (m := m) π (batchedClaim children lambdas) h.sumcheckMessages
      if final = h.finalBytecodeValue * batchedBytecodeWeight children lambdas r then
        return some ⟨r, h.finalBytecodeValue⟩
      else return none
    else return none

end Transcript

/-- **The deployed batching**: `batchWith` over Keccak-f[1600]. -/
def batch (vars : ℕ) (children : List ChildClaims) (h : BatchingHints) :
    Option DeferredBytecodeClaim :=
  Id.run (batchWith keccakF1600 vars children h)

end LeanVM.Guest.Batch

end
