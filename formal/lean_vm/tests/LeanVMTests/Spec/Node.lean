import Statement.LeanVmGuest
import LeanXmss.Scheme
import Statement.LeanSphincs
import Statement.Fast.Schemes
import LeanDa.Scheme
import Statement.Fast.Keccak
import Statement.Fast.QuadExt
import Statement.Fast.FieldWords
import LeanVM.Facts.Verifier
import LeanVM.Facts.NodeWith
import LeanVM.Facts.DaWith
import LeanVMTests.Spec.NodeVectors

/-!
# The deferring verifier and the node's statement: inhabitants, known answers and mutations

* `claimedBytecodeValue` answers with the claimed value at the claimed point and rejects
  elsewhere, and the deferring verifier's seed is the deployed verifier's.
* The deferring verifier rejects garbage, and so does the deployed one on the same proof.
* `DeferredClaim.HasBytecodeShape` rejects a bytecode point one coordinate short, which the digest alone
  cannot tell apart (`statementDigest` carries no lengths: the short claim's odd cell count is
  paired with a zero cell).
* Known answers for the statement's encodings (`claimListDigest` of each scheme's claims,
  `daClaimDigest`, `statementDigest`), the batching transcript's seed (`batchSeed`) and the
  batching of two children (`batch`): computed by an independent transcription of
  `claim_list_digest`, `root_vector_digest`, `statement_digest`, `FiatShamirState` and
  `aggregate_deferred_claims` (`crates/rec_aggregation/src/aggregation.rs`,
  `crates/fiat_shamir/src/lib.rs` at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`, the
  statement's digest at `990b935263dc7f793f280914f262ca7955ddc3e0`, its one DA digest at
  `93ebecc5f87ed7b1248a9772c392f9a41b6ac8d0`, the batching's one challenge and its powers at
  `c445e3d51a5a85031df47240595698f3b24897bf`) over the pinned verifier's Keccak and field
  arithmetic. The batching's hints are the transcription's honest sumcheck messages; Lean's
  transcript must squeeze the same challenges for the claim to close at the transcription's point,
  which is a true claim on the table.
  Mutations: a wrong final value, or a child's false claim, and the batching rejects.
* `batch` on no children is inhabited; the outer verifier's membership challenge
  (`membershipChallengeOf`) of a root is not zero.
* The Rust vectors (`NodeVectors.lean`, written by `scripts/guest-export` from the deployed
  `crates/rec_aggregation/src/aggregation/` at the guest's shape, `bytecode_vars = 23`): the
  statement's encodings and the batching of two children's true claims on the guest's stacked
  bytecode are the Spec's, and a batching hint off by one rejects. What is slow in the
  interpreter, `lake exe node-vectors` (`cli/NodeVectors.lean`) checks compiled: that their seed
  is `deployedSeed guest` (the Keccak-256 IV of the guest's `2^23` bytecode words), and the DA
  root's vector digest.
-/

namespace LeanVMTests.Spec.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Node

/-- A field element from its limbs. -/
def e (c0 c1 c2 : ℕ) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-! ## The deferring verifier -/

/-- A claim on the fixed polynomial. -/
def c : BytecodeClaim := ⟨[1, 0], 1⟩

example (words : List K) :
    claimedBytecodeValue c words c.bytecodePoint = .ret c.bytecodeValue := by
  simp [claimedBytecodeValue, VerifierProgram.require]; rfl

-- Mutation: at another point the claimed evaluation rejects.
example (words : List K) : claimedBytecodeValue c words [0, 0] = .fail := by
  simp [claimedBytecodeValue, VerifierProgram.require, c]; rfl

/-- The deferring verifier's seed is the deployed verifier's, from the deployed IV. -/
example (bytecode : List K) (publicInput : Digest) :
    seed bytecode publicInput = keccakF1600 (seedInput (fiatShamirIv bytecode) publicInput) := rfl

/-- A bytecode of 32 words. -/
def bytecode : List K := (List.range 32).map K.ofBits

#guard verifyDeferred bytecode (fiatShamirIv bytecode) default c ⟨[], []⟩ = false
#guard verify bytecode default ⟨[], []⟩ = false

/-! ## The deferred claim's shape -/

/-- A deferred claim of the bytecode's shape, at zero. -/
def zeroClaim : DeferredClaim := ⟨List.replicate 5 0, 0⟩

/-- A deferred claim one coordinate short. -/
def shortClaim : DeferredClaim := ⟨List.replicate 4 0, 0⟩

example : zeroClaim.HasBytecodeShape bytecode ∧ zeroClaim.HasZeroPoint bytecode := by
  simp [DeferredClaim.HasBytecodeShape, DeferredClaim.HasZeroPoint, zeroClaim, bytecode]

/-- No claims. -/
def noClaims : NodeClaims := ⟨[], [], zeroDigest⟩

-- Mutation: a bytecode point one coordinate short has the same digest (its five cells are paired
-- with a zero cell, the six zero cells of `zeroClaim`), and `Shaped` is what rejects it.
#guard statementDigest default ⟨noClaims, zeroClaim⟩ = statementDigest default ⟨noClaims, shortClaim⟩

example : ¬ shortClaim.HasBytecodeShape bytecode := by
  simp [DeferredClaim.HasBytecodeShape, shortClaim, bytecode]

/-- The digest is Keccak-256 of the preimage the collision candidates name. -/
example (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = keccak256 (statementPreimage seed s) := rfl

/-! ## The statement's encodings: known answers -/

/-- The leanXMSS claims. -/
def xmss : List LeanXmssClaim :=
  [(⟨BitVec.ofNat 128 0x0123456789abcdef0011223344556677,
      BitVec.ofNat 128 0x8899aabbccddeeff0f1e2d3c4b5a6978⟩,
    BitVec.ofNat 256 0xdeadbeef00112233445566778899aabbccddeeff102132435465768798a9bacb),
   (⟨BitVec.ofNat 128 0x77665544332211000123456789abcdef,
      BitVec.ofNat 128 0x0f0e0d0c0b0a09080706050403020100⟩, BitVec.ofNat 256 1)]

/-- The leanSPHINCS claims. -/
def sphincs : List LeanSphincsClaim :=
  [(⟨BitVec.ofNat 128 0xfedcba98765432100123456789abcdef, BitVec.ofNat 128 1⟩,
    BitVec.ofNat 256 (2 ^ 256 - 1))]

/-- A DA claim: a root and a membership challenge. -/
def daClaim : DaClaim := ⟨keccak256 (utf8 "root0"), e 1 2 3⟩

/-- A statement's DA digest (the digest of the earlier, root and vector digest, claim). -/
def da : Digest := #v[0x12da73668473f030, 0x3b3c425c5e7d748d, 0x039ebf81841b3952, 0xde4718e69830fa95]

/-- A seed. -/
def seed0 : Digest := keccak256 (utf8 "seed")

/-- A deferred claim: five coordinates, one with a top limb, and a value. -/
def defer0 : DeferredClaim :=
  ⟨[e 1 2 3, e 4 5 6, e 7 8 9, e 10 11 12, e 0xffffffffffffffff 0 1], e 13 14 15⟩

#guard claimListDigest xmssPublicKeyBytes xmss =
  #v[0x414fd0b2c209e3b8, 0x6538b0954fa462a9, 0xe56f9cc0c9d4fdc7, 0xa490bc2e93724856]

#guard claimListDigest Sphincs.PublicKey.toBytes sphincs =
  #v[0xe8d78086d65bb925, 0x7ace3a6c82dbaf4e, 0xbf24729b60a19887, 0xc1ffa4b8c5dee59e]

/- An empty list hashes the empty string. -/
#guard claimListDigest xmssPublicKeyBytes [] =
  #v[0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b]

/- The DA claim's digest: Keccak-256 of the root, the challenge's three limbs and a zero word
(computed independently by another Keccak-256). -/
#guard daClaimDigest daClaim =
  #v[0x54e5caaf0b9df436, 0xe9801627f87d2cbd, 0x008b308358001569, 0xac0e2d12ab54f275]

#guard statementDigest seed0 ⟨⟨xmss, sphincs, da⟩, defer0⟩ =
  #v[0x390bb57c95a72731, 0xc6a7438398ab72ee, 0x42095a68d163c568, 0x172ac4a032779c05]

/- The same claim one coordinate short: five cells, paired with a zero cell. -/
#guard statementDigest seed0 ⟨⟨xmss, sphincs, da⟩, { defer0 with
    bytecodePoint := defer0.bytecodePoint.take 4 }⟩ =
  #v[0xdc54bf3336f25e78, 0xf384991b0b6165bf, 0xe7e52156413534f3, 0xe8b99f1696b9f4d7]

-- Mutation: other signature lists give another digest.
#guard statementDigest seed0 ⟨⟨[], [], da⟩, defer0⟩ =
  #v[0xa592644862762952, 0x09567e10b4b0d8c3, 0x3cb6feed0116cea8, 0x412ab1045c7507e5]

-- Mutation: no DA claim, the zero digest in its place.
#guard statementDigest seed0 ⟨⟨xmss, sphincs, zeroDigest⟩, defer0⟩ =
  #v[0xa065f9975aeba2b2, 0xdf0f15d80b8f94e2, 0x3d8fcd509b505190, 0xa750b8b1977f11ee]

/-! ## The batching: known answers and mutations -/

/- `FiatShamirState::from_label(RECURSION_AGG_LABEL)`'s state, whose lanes `16..25` the guest
bakes as `AGG_SEED_*`. -/
#guard batchSeed = #v[0x870d207a806c795a, 0xb4b4ddd8d965e271, 0xf4d25a66d674ca27,
  0xd58527e821d50d69, 0xe8b3b32bc6b41ca0, 0x1ac6405ae5e1c26c, 0x25100272f63a0add,
  0xddac48119a39ccbb, 0x2f557d8fdc241fb9, 0xb03075526083a5c6, 0x0ae457bd1e0fd49d,
  0xa690dfcc98cbc36e, 0xc8bc6a708f4be81f, 0xaf078f39833eded4, 0xfca5d5aea8d67de1,
  0x160ed37a53dc979a, 0x15afc20f66b0d5b9, 0x6a647807f52d7266, 0xa5800c0973e6ab80,
  0xc99f802c9aef9edd, 0xd2dc01646a279b0e, 0x5d0c9da7c6a96b8d, 0x971016a864ec6d1a,
  0x92ef5eb709b9fa89, 0x02359fac99c1f265]

/-- A table of eight words, the claims' polynomial. -/
def table : List E := (List.range 8).map fun i ↦ ofK (K.ofBits (3 * i + 1))

/-- The table's value at a point. -/
def mle (point : List E) : E := multilinearEval table point

/-- Child `i`: its public input, a true fresh claim and a true carried claim. -/
def child (i : ℕ) : ChildClaims :=
  let p := [e (i + 1) 2 0, e 5 i 7, e 0 0 (i + 9)]
  let q := [e i 1 1, e 2 2 i, e (i + 3) 0 0]
  ⟨keccak256 [i.toUInt8], ⟨p, mle p⟩, ⟨q, mle q⟩⟩

/-- Two children. -/
def children : List ChildClaims := [child 0, child 1]

/- The transcription's value of child 0's fresh claim. -/
#guard (child 0).freshClaim.bytecodeValue = e 0x3b2 0x222 0x7ee

/-- The transcription's honest hints. -/
def hints : BatchingHints :=
  ⟨[(e 0x79aca609cbc240eb 0x330e9f31986a68a6 0x2f43cb09de086072,
      e 0x57abf0bf21536352 0x3ff8403a19a4a63c 0x600534b9909e581d),
    (e 0x7d3effa4172e13e9 0x8b06819b75f551ab 0xf0afa16df931e5e,
      e 0x216085d8a973a048 0x4cc37560e3af5849 0x2c8fda88d7fb3af9),
    (e 0xf83368c1d8fa9bca 0xf478bc5c6648a954 0x4beebcc7db2cf34a,
      e 0x25d6c858a4d23316 0xe119ed795e599cc0 0x480cfbef0b9064fc)],
    e 0x995dddb79c2b594e 0xcfb3c7bfe92b5a17 0x3316f45eb5224d6f⟩

/-- The transcription's batched point. -/
def batchedPoint : List E :=
  [e 0x1c3b3515c26e39cd 0xd7cd85ddc12e4340 0x71e5c1b1a9072741,
    e 0xbc88ed94799e1144 0x6a3d395c0baa4ec 0x15e9d45adcaccac8,
    e 0xf5e74cc7d330c218 0xb9f65ff472a53d28 0xf002b01726f8c7eb]

#guard (batch children hints).map (·.bytecodePoint) = some batchedPoint
#guard (batch children hints).map (·.bytecodeValue) = some hints.finalBytecodeValue

/- The batched claim is true of the table. -/
#guard mle batchedPoint = hints.finalBytecodeValue

/- The batching with Keccak-f as a parameter, from `batchSeed`, is the same. -/
#guard (Id.run (batchWith (m := Id) keccakF1600 batchSeed children hints)).map (·.bytecodePoint) =
  some batchedPoint

-- Mutation: a wrong final value.
#guard (batch children { hints with finalBytecodeValue := hints.finalBytecodeValue + 1 }).isNone

-- Mutation: child 1's carried claim false, the same hints.
#guard (batch [child 0, { child 1 with carriedClaim := { (child 1).carriedClaim with
  bytecodeValue := (child 1).carriedClaim.bytecodeValue + 1 } }] hints).isNone

-- Mutation: the children swapped, the same hints.
#guard (batch [child 1, child 0] hints).isNone

/- No children: the empty sumcheck closes on the zero claim. -/
#guard (batch [] ⟨[], 0⟩).isSome

/-! ## The Rust vectors -/

#guard claimListDigest xmssPublicKeyBytes NodeVectors.xmss = NodeVectors.xmssListDigest
#guard claimListDigest Sphincs.PublicKey.toBytes NodeVectors.sphincs = NodeVectors.sphincsListDigest
#guard daClaimDigest NodeVectors.daClaim = NodeVectors.daDigest
#guard zeroDigest = NodeVectors.daNone

/-- The statement of the vectors' claims, deferring their claim. -/
def vectorStatement : NodeStatement :=
  ⟨⟨NodeVectors.xmss, NodeVectors.sphincs, NodeVectors.daDigest⟩, NodeVectors.defer⟩

#guard statementDigest NodeVectors.seed vectorStatement = NodeVectors.statementDigest

-- Mutation: another seed, another digest.
#guard statementDigest seed0 vectorStatement ≠ NodeVectors.statementDigest

/- The batching of the two children, with the Rust's hints, defers the Rust's claim. -/
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodePoint) =
  some NodeVectors.batched.bytecodePoint
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodeValue) =
  some NodeVectors.batched.bytecodeValue

-- Mutation: a final value one off.
#guard (batch NodeVectors.children { NodeVectors.hints with
  finalBytecodeValue := NodeVectors.hints.finalBytecodeValue + 1 }).isNone

/-! ## The DA claim -/

/-- A root. -/
def root : Digest := keccak256 []

#guard LeanVM.Da.membershipChallengeOf root != 0

end LeanVMTests.Spec.Node
