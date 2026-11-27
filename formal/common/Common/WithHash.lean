module

public import Statement.SufCma
public import Common.Defs

/-!
# The SUF-CMA game with a hash oracle

The statement's SUF-CMA game is over the permutation `π` alone (`Statement/RandomPermutation.lean`):
every hash is Keccak-256 over `π`. The proofs reason with the hash a query of its own (the game's
`SufCma.SchemeHashSpec`), which a random oracle answers in the random-oracle steps and Keccak-256
over `π` in the random-permutation model (`SufCma.schemeHashOverPermutation`): the game with a hash
query (`SufCma.SchemeWithHash`, `forgeryGameWithHash`). `Common.WithHashBridge` proves the
statement's game the hash-query one with the hash Keccak-256 over `π`.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace Common

open LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash

/-- **Keccak-256 in the model**: the sponge over `π` (`keccak256With`), one call of `π` per block
of the padded message (`⌊n / 136⌋ + 1` for `n` bytes), its digest's 32 bytes. -/
def keccak256OverPermutation (m : List UInt8) : OracleComp RandomPermutationOracles DigestBytes :=
  Digest.toBytes <$> keccak256With queryPermutation m

namespace SufCma


/-- The hash of a signature scheme, `H : List UInt8 → BitVec 256`: in the model Keccak-256, its
digest read as a little-endian number (`digestBytesEquivBitVec`). -/
abbrev SchemeHashSpec := List UInt8 →ₒ BitVec 256

/-- **A signature scheme** with the hash `H` (`SchemeHashSpec`): a seed sampler, key generation from
a seed, the signer answering a request `Req` with `Resp`, the verifier of a claimed forgery `F`, and
the winning condition on the signing transcript and the forgery. -/
structure SchemeWithHash (Seed PK SK Req Resp F : Type) where
  /-- Sample the secret seed. -/
  sample : ProbComp Seed
  /-- Generate the keys from the seed. -/
  keygen : Seed → OracleComp SchemeHashSpec (PK × SK)
  /-- Answer a signing request. -/
  sign : SK → Req → OracleComp SchemeHashSpec Resp
  /-- Verify a claimed forgery. -/
  verify : PK → F → OracleComp SchemeHashSpec Bool
  /-- The transcript and the forgery make a win (when the forgery verifies). -/
  win : QueryLog (Req →ₒ Resp) → F → Bool

variable {Seed PK SK Req Resp F : Type}

/-- **A kept-key form of a scheme**: key generation derives `D` from the seed (`derive`, hash
queries only) and continues (`rest`), but the secret key keeps `keep seed d` (the seed and part of what it derived, as the
leanXMSS crate's key keeps the seed and the public parameter), from which the signer derives the
rest again (`rederive`) and signs as `signWith` of the derived value. (`Common.SeedKey` shows the
two have the same success when `rederive` reruns queries of `derive`.) -/
structure KeptKey (S : SchemeWithHash Seed PK SK Req Resp F) (D SK' : Type) where
  /-- What the signer needs, derived from the seed. -/
  derive : Seed → OracleComp SchemeHashSpec D
  /-- The rest of key generation. -/
  rest : Seed → D → OracleComp SchemeHashSpec (PK × SK)
  /-- The signer, from the derived value. -/
  signWith : D → Req → OracleComp SchemeHashSpec Resp
  /-- The secret key kept, from the seed and the derived value. -/
  keep : Seed → D → SK'
  /-- What the signer derives again from the kept key. -/
  rederive : SK' → OracleComp SchemeHashSpec D
  keygen_eq : ∀ seed, S.keygen seed = derive seed >>= rest seed
  sign_eq : ∀ seed d, ∀ keys ∈ support (rest seed d), S.sign keys.2 = signWith d

/-- The scheme with the kept key: key generation as `S`'s, keeping `keep seed d` as the key, the
signer deriving its value from the kept key first. -/
def KeptKey.scheme {S : SchemeWithHash Seed PK SK Req Resp F} {D SK' : Type}
    (K : KeptKey S D SK') : SchemeWithHash Seed PK SK' Req Resp F where
  sample := S.sample
  keygen seed := K.derive seed >>= fun d ↦ (fun keys ↦ (keys.1, K.keep seed d)) <$> K.rest seed d
  sign key request := K.rederive key >>= fun d ↦ K.signWith d request
  verify := S.verify
  win := S.win

/-- The hash in the random-permutation model: Keccak-256 over `π` (`keccak256OverPermutation`), its
digest read as a bit vector (`digestBytesEquivBitVec`). -/
def schemeHashOverPermutation : QueryImpl SchemeHashSpec (OracleComp RandomPermutationOracles) :=
  fun m ↦ digestBytesEquivBitVec <$> keccak256OverPermutation m

/-- The signing oracle in the random-permutation model. -/
def loggedSigningOracleWithHash (S : SchemeWithHash Seed PK SK Req Resp F) (sk : SK) :
    QueryImpl (Req →ₒ Resp)
      (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) :=
  QueryImpl.withLogging fun r ↦ simulateQ schemeHashOverPermutation (S.sign sk r)

/-- **The RPM game**: the game with `H` Keccak-256 over the permutation, and an adversary that
also queries `π` and `π⁻¹`. -/
noncomputable def forgeryGameWithHash (S : SchemeWithHash Seed PK SK Req Resp F)
    (main : PK → OracleComp (RandomPermutationOracles + (Req →ₒ Resp)) F) :
      OracleComp RandomPermutationOracles Bool := do
  let seed ← liftM S.sample
  let (pk, sk) ← simulateQ schemeHashOverPermutation (S.keygen seed)
  let ((forgery, log) : F × QueryLog (Req →ₒ Resp)) ←
    (simulateQ
      (QueryImpl.ofLift RandomPermutationOracles
        (WriterT (QueryLog (Req →ₒ Resp)) (OracleComp RandomPermutationOracles)) +
      loggedSigningOracleWithHash S sk) (main pk)).run
  let verified ← simulateQ schemeHashOverPermutation (S.verify pk forgery)
  return S.win log forgery && verified


end SufCma

end Common

end
