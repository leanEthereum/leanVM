import Statement.LeanVmGuest
import LeanXmss.Scheme
import Statement.LeanSphincs
import LeanDa.Scheme
import Statement.Fast.Keccak
import FastFields.QuadExt
import FastFields.FieldWords
import LeanVM.Facts.Verifier
import LeanVM.Facts.NodeWith
import LeanVM.Facts.DaWith
import LeanVMTests.Spec.NodeVectors
import LeanVMTests.Spec.Layout

/-!
# The deferring verifier and the node's statement: inhabitants, known answers and mutations

* `freshSplit` answers with the fresh claim's split columns at the claim's point and rejects
  elsewhere or on a wrong count of values, and the deferring verifier's seed is the deployed
  verifier's.
* The deferring verifier rejects garbage, and so does the deployed one on the same proof.
* `DeferredBytecodeClaim.HasBytecodeShape` rejects a bytecode point one coordinate short (whose cells, hashed
  unpadded, also change the digest).
* Known answers for the claim lists' digests (`claimListDigest` of each scheme's claims) and the
  batching transcript's seed (`batchSeed`), computed by an independent transcription of
  `claim_list_digest` and `FiatShamirState` (`crates/rec_aggregation/src/aggregation.rs`,
  `crates/fiat_shamir/src/lib.rs` at leanVM `4af2cdddd7cd41b9df2cc7e123e314a91b0b4462`), which the
  field change left as they were.
* The split program on the 16-instruction program of `Spec/Layout.lean`: `splitValues` is the
  Rust's `split_values` there, and the split table (`splitTable`) at the point and any column
  challenges is the values folded at them (`foldColumns`), the batching's fresh claim
  (`aggregate_deferred_claims`' `debug_assert_eq`); its length and shape.
* `batch` on no children is inhabited; the outer verifier's membership challenge
  (`membershipChallengeOf`) of a root is not zero.
* The Rust vectors (`NodeVectors.lean`, written by `scripts/guest-export` from the deployed
  `crates/aggregation/src/` at the guest's shape, `bytecode_vars = 25`): the
  statement's encodings and the batching of two children's true claims on the guest's split
  program (fresh claims at points over the instructions, carried claims on the split table) are
  the Spec's, with the permutation as a parameter too (`batchWith`); a batching hint off
  by one, the children swapped, and another seed or no DA claim in the statement change the
  outcome. What is slow in the
  interpreter, `lake exe node-vectors` (`cli/NodeVectors.lean`) checks compiled: that their seed
  is `deployedSeed guest` (the Keccak-256 IV of the guest's `2^23` bytecode words), the DA
  root's vector digest, and the children's fresh values the split columns at their points
  (`splitValues`, against `split_values`).
-/

namespace LeanVMTests.Spec.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash LeanVM.Node

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : List UInt8 := s.toUTF8.toList

/-- A seed. -/
def seed0 : Digest := keccak256 (utf8 "seed")

/-! ## The deferring verifier -/

/-- A fresh claim: a point over two instructions, a value per split column. -/
def fresh : FreshClaim := ⟨[1], (splitColumns tables).map fun _ ↦ 1⟩

/-- Whether a program accepts at once. -/
def accepts {α : Type} : VerifierProgram α → Bool
  | .ret _ => true
  | _ => false

#guard accepts (freshSplit fresh [] fresh.point [])

-- Mutation: at another point the fresh claim rejects.
#guard !accepts (freshSplit fresh [] [0] [])

-- Mutation: a value short, the fresh claim rejects.
#guard !accepts (freshSplit ⟨fresh.point, fresh.values.drop 1⟩ [] fresh.point [])

/-- The deferring verifier's seed is the deployed verifier's, from the deployed IV. -/
example (bytecode : List K) (publicInput : Digest) :
    seed bytecode publicInput = keccakF1600 (seedInput (fiatShamirIv bytecode) publicInput) := rfl

/-- A bytecode of 32 words. -/
def bytecode : List K := (List.range 32).map K.ofBits

#guard verifyDeferred bytecode (fiatShamirIv bytecode) default fresh ⟨[], []⟩ = false
#guard verify bytecode default ⟨[], []⟩ = false

/-! ## The deferred claim's shape -/

/-- A deferred claim of the split program's shape, at zero: the instruction's coordinate, then
the columns' six. -/
def zeroClaim : DeferredBytecodeClaim := ⟨List.replicate 7 0, 0⟩

/-- A deferred claim one coordinate short. -/
def shortClaim : DeferredBytecodeClaim := ⟨List.replicate 6 0, 0⟩

example : zeroClaim.HasBytecodeShape bytecode ∧ zeroClaim.HasZeroPoint bytecode := by
  simp [DeferredBytecodeClaim.HasBytecodeShape, DeferredBytecodeClaim.HasZeroPoint, zeroClaim, bytecode,
    deferredVariableCount, instructionVariableCount, splitLog, bytecodeSlotBits]

/-- No claims. -/
def noClaims : NodeClaims := ⟨[], [], zeroDigest⟩

-- Mutation: a bytecode point one coordinate short; its cells, hashed unpadded, change the digest,
-- and `HasBytecodeShape` rejects it.
#guard statementDigest default ⟨noClaims, zeroClaim⟩ ≠ statementDigest default ⟨noClaims, shortClaim⟩

example : ¬ shortClaim.HasBytecodeShape bytecode := by
  simp [DeferredBytecodeClaim.HasBytecodeShape, shortClaim, bytecode, deferredVariableCount,
    instructionVariableCount, splitLog, bytecodeSlotBits]

/-- The digest is Keccak-256 of the preimage the collision candidates name. -/
example (seed : Digest) (s : NodeStatement) :
    statementDigest seed s = keccak256 (statementPreimage seed s) := rfl

/-! ## The split program on a small program -/

/- `splitValues` is the Rust's `split_values` on `Spec/Layout.lean`'s program. -/
#guard splitValues Layout.program16 Layout.splitPoint = Layout.splitValues

/-- Column challenges. -/
def columnChallenges : List E := [3, 5, 7, 11, 13, 17].map fun n ↦ Layout.e n (2 * n + 1)

/-- The split table of the program, as `E` words. -/
def table16 : List E := (splitTable Layout.program16).map ofK

/- Sixteen instructions, sixty-four columns: `2^(4 + splitLog)` entries, `deferredVariableCount`
coordinates. -/
#guard table16.length = 2 ^ 10 ∧ deferredVariableCount Layout.program16 = 10

/- A fresh claim's value on the table at its point and the column challenges is its values folded
at the challenges. -/
#guard multilinearEval table16 (Layout.splitPoint ++ columnChallenges) =
  LeanVM.Guest.Batch.foldColumns columnChallenges Layout.splitValues

-- Mutation: a value off, the fold differs.
#guard multilinearEval table16 (Layout.splitPoint ++ columnChallenges) ≠
  LeanVM.Guest.Batch.foldColumns columnChallenges (Layout.splitValues.set 0 0)

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

#guard claimListDigest xmssPublicKeyBytes xmss =
  #v[0x414fd0b2c209e3b8, 0x6538b0954fa462a9, 0xe56f9cc0c9d4fdc7, 0xa490bc2e93724856]

#guard claimListDigest Sphincs.PublicKey.toBytes sphincs =
  #v[0xe8d78086d65bb925, 0x7ace3a6c82dbaf4e, 0xbf24729b60a19887, 0xc1ffa4b8c5dee59e]

/- An empty list hashes the empty string. -/
#guard claimListDigest xmssPublicKeyBytes [] =
  #v[0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b]

/-! ## The batching's seed -/

/- `FiatShamirState::from_label(RECURSION_AGG_LABEL)`'s state, whose lanes `16..25` the guest
bakes as `AGG_SEED_*`. -/
#guard batchSeed = #v[0x870d207a806c795a, 0xb4b4ddd8d965e271, 0xf4d25a66d674ca27,
  0xd58527e821d50d69, 0xe8b3b32bc6b41ca0, 0x1ac6405ae5e1c26c, 0x25100272f63a0add,
  0xddac48119a39ccbb, 0x2f557d8fdc241fb9, 0xb03075526083a5c6, 0x0ae457bd1e0fd49d,
  0xa690dfcc98cbc36e, 0xc8bc6a708f4be81f, 0xaf078f39833eded4, 0xfca5d5aea8d67de1,
  0x160ed37a53dc979a, 0x15afc20f66b0d5b9, 0x6a647807f52d7266, 0xa5800c0973e6ab80,
  0xc99f802c9aef9edd, 0xd2dc01646a279b0e, 0x5d0c9da7c6a96b8d, 0x971016a864ec6d1a,
  0x92ef5eb709b9fa89, 0x02359fac99c1f265]

/- No children: the empty sumcheck closes on the zero claim, the nonce `0` passing the proof of
work. -/
#guard (batch [] ⟨0, [], 0⟩).isSome

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

/- The batching of the two children, with the Rust's hints (after `λ`, the six column challenges),
defers the Rust's claim. -/
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodePoint) =
  some NodeVectors.batched.bytecodePoint
#guard (batch NodeVectors.children NodeVectors.hints).map (·.bytecodeValue) =
  some NodeVectors.batched.bytecodeValue

/- The batching with Keccak-f as a parameter, from `batchSeed`, is the same. -/
#guard (Id.run (batchWith (m := Id) keccakF1600 batchSeed NodeVectors.children
  NodeVectors.hints)).map (·.bytecodePoint) = some NodeVectors.batched.bytecodePoint

-- Mutation: a final value one off.
#guard (batch NodeVectors.children { NodeVectors.hints with
  finalBytecodeValue := NodeVectors.hints.finalBytecodeValue + 1 }).isNone

-- Mutation: the children swapped, the same hints.
#guard (batch NodeVectors.children.reverse NodeVectors.hints).isNone

-- Mutation: no DA claim, the zero digest in its place.
#guard statementDigest NodeVectors.seed { vectorStatement with
  claims := { vectorStatement.claims with daDigest := zeroDigest } } ≠ NodeVectors.statementDigest

/-! ## The DA claim -/

/-- A root. -/
def root : Digest := keccak256 []

#guard LeanVM.Da.membershipChallengeOf root != 0

end LeanVMTests.Spec.Node
