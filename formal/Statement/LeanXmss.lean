module

public import Statement.HashSignatures
public import EthLib.Cryptography.Xmss

/-!
# leanXMSS

leanXMSS is EthLib's (`EthLib.Cryptography.Xmss`, at the commit `Statement/lakefile.toml` pins):
its key generation (`keyGenWith`), signer (`signWith`) and verifier (`verifyWith`), each over a hash
`H` of lanes. Here `H` is EthLib's Keccak-256 sponge over a permutation `π` of leanVM's Keccak state
(`xmssHash`): in the end statement `π` is the random permutation, in the aggregation's claims
leanVM's Keccak-f[1600] (`verifyWithKeccak`). This file holds what leanVM's statement adds around
EthLib's scheme: the two layouts of the Keccak state, the request and the forgery of the SUF-CMA
game of `Statement/SufCma.lean`, and the end statement
`LeanXmss.RandomPermutationModel.LeanXmssStronglyUnforgeable`, which `lean_xmss` proves from
EthLib's theorem.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace LeanXmss

open EthLib.Cryptography.Xmss (PublicKey SecretKey Signature Message Seed LeafIndex keyGenWith
  signWith verifyWith)
open EthLib.Cryptography.Xmss.Constants (LOG_LIFETIME)
open EthLib.Cryptography.Hash.Keccak (Lanes4 keccak256LanesWith)
open LeanVM.Semantics (KeccakState keccakF1600)

/-! ## The hash -/

/-- leanVM's Keccak state as EthLib's: lane `x + 5y`, at index `x + 5y`, in the field `a(x+5y)`. -/
def stateToEthLib (s : KeccakState) : EthLib.Cryptography.Hash.Keccak.State :=
  ⟨s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7], s[8], s[9], s[10], s[11], s[12], s[13], s[14],
    s[15], s[16], s[17], s[18], s[19], s[20], s[21], s[22], s[23], s[24]⟩

/-- EthLib's Keccak state as leanVM's. -/
def stateOfEthLib (s : EthLib.Cryptography.Hash.Keccak.State) : KeccakState :=
  #v[s.a0, s.a1, s.a2, s.a3, s.a4, s.a5, s.a6, s.a7, s.a8, s.a9, s.a10, s.a11, s.a12, s.a13, s.a14,
    s.a15, s.a16, s.a17, s.a18, s.a19, s.a20, s.a21, s.a22, s.a23, s.a24]

/-- **leanXMSS's hash `H` over `π`**: EthLib's Keccak-256 of lanes, its sponge over `π`, each
state carried to leanVM's layout and back. -/
def xmssHash {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState) :
    Array UInt64 → m Lanes4 :=
  keccak256LanesWith fun s ↦ stateToEthLib <$> π (stateOfEthLib s)

/-- A 256-bit value as four lanes, least significant first: a claim's message, the key's seed. -/
def lanesOfBits (value : BitVec 256) : Lanes4 :=
  ⟨UInt64.ofBitVec (value.extractLsb' 0 64), UInt64.ofBitVec (value.extractLsb' 64 64),
    UInt64.ofBitVec (value.extractLsb' 128 64), UInt64.ofBitVec (value.extractLsb' 192 64)⟩

/-- **leanXMSS verification as deployed**: EthLib's, its hash Keccak-256 over Keccak-f[1600]. -/
def verifyWithKeccak (publicKey : PublicKey) (message : Message)
    (signature : Signature) : Bool :=
  Id.run (verifyWith (xmssHash (m := Id) keccakF1600) publicKey message signature)

/-! ## Signing requests, forgeries and transcripts -/

/-- A signing request: a leaf index and a message. -/
structure SigningRequest where
  /-- The leaf index to sign with. -/
  leafIndex : LeafIndex
  /-- The message. -/
  message : Message
deriving DecidableEq

/-- A claimed forgery: a message and a signature, which carries its leaf index. -/
structure Forgery where
  /-- The message. -/
  message : Message
  /-- Its claimed signature. -/
  signature : Signature
deriving DecidableEq

/-- The signing oracle answers a request with a signature, or `none` if the signer fails. -/
abbrev SigningOracleSpec := SigningRequest →ₒ Option Signature

namespace SigningTranscript

/-- A transcript is valid when no leaf index occurs twice. -/
abbrev NoLeafIndexReused (log : QueryLog SigningOracleSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

end SigningTranscript

/-! ## Security in the random-permutation model -/

namespace RandomPermutationModel

open Common Common.SufCma

/-- **The key's seed `S_0`**: 32 uniform bytes, as four lanes, least significant first. -/
noncomputable def sampleSeed : ProbComp Seed :=
  lanesOfBits <$> HashSig.sampleMasterSeed

/-- leanXMSS in the generic SUF-CMA game, its hash over `π` (`queryPermutation`): the seed, key
generation, the signer of a request, which always signs with the secret key from key generation
and drops the key signing returns, the verifier, and the winning condition: a valid transcript
without the forgery (`SignerReturnedForgery`). -/
noncomputable def sufCmaScheme :
    Scheme Seed PublicKey SecretKey SigningRequest (Option Signature)
      Forgery where
  sampleSeed := sampleSeed
  generateKeys := keyGenWith (xmssHash queryPermutation)
  sign secretKey request := (fun result ↦ result.1.toOption) <$>
    signWith (xmssHash queryPermutation) secretKey request.leafIndex request.message
  verify publicKey forgery :=
    verifyWith (xmssHash queryPermutation) publicKey forgery.message forgery.signature
  winningCondition log forgery :=
    decide (SigningTranscript.NoLeafIndexReused log ∧
      ¬SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature)

/-- The additive constant of leanXMSS's bound, in units of `2^-127` (`statement.tex` derives it). -/
def securitySlack : Nat := 2 ^ 10

/-- **leanXMSS in the random-permutation model**: an adversary that itself makes at most `q` calls
of `π` and `π⁻¹` and at most `2^32` signing requests forges with probability at most
`(q + 2^10) · 2^-127` (`StronglyUnforgeable` at 127 bits). The signer's hashing, its randomizer
grinding included, key generation and the forgery's verification are not charged to `q`. The
adversary chooses each request's leaf index, and a run that requests one twice is a loss
(`NoLeafIndexReused`). -/
abbrev LeanXmssStronglyUnforgeable : Prop :=
  StronglyUnforgeable sufCmaScheme (2 ^ LOG_LIFETIME) securitySlack 127

end RandomPermutationModel

end LeanXmss

end
