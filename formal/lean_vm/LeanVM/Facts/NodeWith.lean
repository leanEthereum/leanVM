/-
  LeanVM.Facts.NodeWith

  The node's hashing functions with any hash `H : Bytes → m Digest` and permutation
  `F : KState → m KState` in any monad (`…With`), as the verifier is (`verifier H F`): moved here
  from `Statement/LeanVmGuest.lean`, names kept (no end statement names them), and at `m = Id`,
  Keccak-256 and Keccak-f[1600] the deployed ones: the `*_id` lemmas. The digests and leanXMSS use
  only `H` (the statement's leanSPHINCS is written over the permutation alone); the batching's
  transcript only `F`, from a parameter state `s0` (deployed: `batchSeed`).
-/

module

public import Statement.LeanVmGuest
public import LeanVM.Guest.Batch.Def
public import LeanXmss.Scheme
public import Statement.LeanSphincs
public import Statement.Fast.Schemes
public import LeanDa.Scheme
public import Statement.Fast.Keccak
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Facts.Verifier
public import LeanVM.Facts.DaWith
public import Common.WithHash
public import LeanVM.Guest.WithHashBridge
public import LeanVM.Guest.WithHash

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

section With

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest) (F : KeccakState → m KeccakState)

/-! ### The signature schemes -/

/-- leanXMSS verification with the hash `H`. -/
def xmssVerifyWith (pk : HashSig.PublicKey) (message : HashSig.Message)
    (σ : LeanXmss.Signature) : m Bool :=
  letI : HasQuery LeanXmss.HashSpec m := ⟨fun x ↦ digestBits <$> H x⟩
  LeanXmss.Verification.verifyWithHash pk message σ

/-! ### The statement's digest -/

/-- `claimListDigest` with the hash `H`. -/
def xmssListDigestWith (claims : List LeanXmssClaim) : m Digest :=
  H (claimListPreimage xmssPublicKeyBytes claims)

/-- `claimListDigest` with the hash `H`. -/
def sphincsListDigestWith (claims : List LeanSphincsClaim) : m Digest :=
  H (claimListPreimage Sphincs.PublicKey.toBytes claims)

/-- **`statementDigest` with the hash `H`.** -/
def statementDigestWith (seed : Digest) (s : NodeStatement) : m Digest := do
  let xd ← xmssListDigestWith H s.claims.xmss
  let sd ← sphincsListDigestWith H s.claims.sphincs
  H (digestBytes seed ++ digestBytes xd ++ digestBytes sd ++ digestBytes s.claims.daDigest ++
    s.deferredClaim.cells.flatMap E.toBytes)

/-! ### The batching -/

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

/-- `batchSeed` with the hash `H` and the permutation `F`. -/
def batchSeedWith : m KeccakState := do
  F (seedInput (← H batchingLabel) (Vector.replicate 4 0))

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
      let lambdas := Guest.Batch.lambdaPowers lam children.length
      let (r, final) ← batchRoundsWith F (Guest.Batch.batchedClaim children lambdas)
        h.sumcheckMessages
      if final = h.finalBytecodeValue * Guest.Batch.batchedBytecodeWeight children lambdas r then
        return some ⟨r, h.finalBytecodeValue⟩
      else return none
    else return none

end With

/-- Absorbing with Keccak-f is `observe`. -/
theorem observeWith_id (x : E) : observeWith (m := Id) keccakF1600 x = observe x := rfl

/-- Squeezing with Keccak-f is `sample`. -/
theorem sampleWith_id : sampleWith (m := Id) keccakF1600 = sample := rfl

/-- A proof of work with Keccak-f is `grind`. -/
theorem grindWith_id (bits : ℕ) (nonce : E) :
    grindWith (m := Id) keccakF1600 bits nonce = grind bits nonce := rfl

/-- The batching's rounds with Keccak-f are `batchRounds`. -/
theorem batchRoundsWith_id : ∀ (claim : E) (rounds : List (E × E)),
    batchRoundsWith (m := Id) keccakF1600 claim rounds = batchRounds claim rounds
  | _, [] => rfl
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith, batchRounds, observeWith_id, sampleWith_id, batchRoundsWith_id]

end
end LeanVM.Node
