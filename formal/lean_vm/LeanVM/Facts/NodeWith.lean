/-
  LeanVM.Facts.NodeWith

  The batching's transcript with any permutation `F : KState → m KState` in any monad (`…With`),
  from a parameter state `s0` (deployed: `batchSeed`), and at `m = Id` and Keccak-f[1600] the
  deployed one: the `*_id` lemmas.
-/

module

public import LeanVM.Guest.Batch.Def
public import Statement.Fast.Keccak
public import FastFields.QuadExt
public import FastFields.FieldWords
public import LeanVM.Guest.WithHashBridge

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (F : KeccakState → m KeccakState)

/-- A Fiat-Shamir chain with the permutation `F`. -/
abbrev ChainWith : Type → Type := StateT Sponge m

/-- `observe` with the permutation `F`. -/
def observeWith (x : E) : ChainWith (m := m) Unit := do
  set (← (Compile.absorb F (← get) x dsObserve : m Sponge))

/-- `sample` with the permutation `F`. -/
def sampleWith : ChainWith (m := m) E := do
  let (c, sp) ← (Compile.squeeze F (← get) : m (E × Sponge))
  set sp
  return c

/-- `grind` with the permutation `F`. -/
def grindWith (bits : ℕ) (nonce : E) : ChainWith (m := m) Bool := do
  let r ← (Compile.absorbNonce F (← get) nonce : m (UInt64 × Sponge))
  set r.2
  return powOk bits r.1

/-- `batchRounds` with the permutation `F`. -/
def batchRoundsWith : E → List (E × E) → ChainWith (m := m) (List E × E)
  | claim, [] => return ([], claim)
  | claim, (g1, gInf) :: rest => do
    observeWith F g1
    observeWith F gInf
    let r ← sampleWith F
    let (rs, final) ← batchRoundsWith (Guest.Batch.sumcheckRoundPolynomial claim (g1, gInf) r) rest
    return (r :: rs, final)

/-- **`batch` with the permutation `F`, from the sponge state `s0`** (deployed: `batchSeed`). -/
def batchWith (s0 : KeccakState) (children : List ChildClaims) (h : BatchingHints) :
    m (Option DeferredBytecodeClaim) :=
  go.run' ⟨s0, [], none⟩
where
  /-- The transcript. -/
  go : ChainWith (m := m) (Option DeferredBytecodeClaim) := do
    for x in padToRate [gpow children.length] do observeWith F x
    for c in children do
      for x in padToRate c.words do observeWith F x
    if ← grindWith F Guest.Batch.batchLambdaGrindBits h.lambdaGrindNonce then
      let lam ← sampleWith F
      let mut column : List E := []
      for _ in List.range splitLog do
        column := column ++ [← sampleWith F]
      let lambdas := Guest.Batch.lambdaPowers lam children.length
      let (r, final) ← batchRoundsWith F (Guest.Batch.batchedClaim children lambdas column)
        h.sumcheckMessages
      if final = h.finalBytecodeValue * Guest.Batch.batchedBytecodeWeight children lambdas column r then
        return some ⟨r, h.finalBytecodeValue⟩
      else return none
    else return none

end With

/-- Absorbing with Keccak-f is `observe`. -/
theorem observeWith_id (x : E) : observeWith (m := Id) keccakF1600 x = observe x := rfl

/-- Squeezing with Keccak-f is `sample`. -/
theorem sampleWith_id : sampleWith (m := Id) keccakF1600 = sample := rfl

/-- The batching's rounds with Keccak-f are `batchRounds`. -/
theorem batchRoundsWith_id : ∀ (claim : E) (rounds : List (E × E)),
    batchRoundsWith (m := Id) keccakF1600 claim rounds = batchRounds claim rounds
  | _, [] => rfl
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith, batchRounds, observeWith_id, sampleWith_id, batchRoundsWith_id]

end
end LeanVM.Node
