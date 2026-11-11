module

public import Statement.LeanVmGuestBatching
public import Statement.LeanXmss
public import Statement.LeanSphincs
public import Statement.LeanDa
public import Statement.Data.Bytecode
public import Statement.Fast.Schemes
public import Statement.CostMachine

/-!
# The leanISA guest program: what a node proves

A node of the aggregation has claims (`NodeStatement`: leanXMSS and leanSPHINCS claims, a DA
digest, and a claim it defers on the guest program's bytecode) and witnesses (`NodeWitness`: raw
signatures, a blob matrix, children carrying proofs, the batching's hints). What a valid execution
of the guest program establishes is that the witnesses hold the claims, `NodeRelation`:

* `SignatureClaimsHeld`: every raw signature verifies, and every leanXMSS and leanSPHINCS claim
  is a raw signature's or in a child's statement's list;
* `DaDigestHeld`: the DA digest is that of the blob matrix the node checks, zeros, or a child's;
* `ChildrenProven`: every child's proof is accepted, for the child's statement, by the deferring
  verifier, which takes the bytecode's value at the child's point from the witness;
* `DeferredClaimBatched`: the node's claim on the bytecode batches its children's, and so has the
  bytecode's shape.

The node's public input is its statement's digest under a seed (`statementDigest`). After the
relation: what a decoding of an execution explains (`ExplainsPublicInput`), the binding of the
statement's digest (`StatementDigestBinds`), and the guest decoder a program computes, with
**`GuestKnowledgeSoundness`**. The batching program (`Batch.nodeBatchingProgram`), reference
material, is `LeanVmGuestBatching.lean`'s; the completeness side is `LeanVmGuestCompleteness.lean`.

Transcribed from leanVM at the pin (`../leanvm-rev`): the modules of
`crates/rec_aggregation/src/aggregation/` (the statement, its digest, the batching) and
`crates/rec_aggregation/guests/lean_ethereum.py` (the guest program); `aggregation/<module>.rs:N`
and `lean_ethereum.py:N` are lines of those files at the pin. The signature schemes are
`LeanXmss.lean`'s and `LeanSphincs.lean`'s with Keccak-256 as their hash; LeanDA is
`LeanDa.lean`'s.

**What the witness gives.** The witness is the knowledge content: "some signature verifies" says
little (some signature verifies for almost every key and message), so the soundness statement takes
the decoder that names the witness as a parameter, a program of the cost machine run within a
budget (`GuestKnowledgeSoundness`). A decoder that output another statement of the same digest
would exhibit a Keccak-256 collision; what excludes it is that none is known. A claim held through
a child carries no knowledge by itself: the deferring verifier reads the bytecode only through its
length and takes the bytecode's value at the child's point from the witness (`Child.freshClaim`),
which nothing here requires true, so a proof of any program of the guest program's length, under
the node's seed, is a child of any statement. A child's claims mean something only once its fresh
claim is true, which needs both the root's deferred claim recomputed, as the deployed outer
verifier does (`AggregateSound`, `Corollaries.lean`, assumes it), and the batching sound inside the
circuit at every level, its Keccak behaving as the random permutation of `LeanVM.KnowledgeSoundness`
(`BatchingSound` is the batching outside the circuit). No end statement gives the latter: that the
root's statement makes every claim held at the leaves is not proved.
-/

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The claims -/

/-- A leanXMSS key and a message it signed, at a leaf index the claim does not record
(`LeanXmssClaim`, `aggregation/mod.rs:64`). -/
abbrev LeanXmssClaim : Type := HashSig.PublicKey × HashSig.Message

/-- A leanSPHINCS key and a message it signed (`LeanSphincsClaim`, `aggregation/mod.rs:67`). -/
abbrev LeanSphincsClaim : Type := Sphincs.PublicKey × HashSig.Message

/-- **A DA claim**: a blob matrix's Merkle root (an aggregate's claims' `da_commitment`,
`aggregation/proof.rs:27-28`) and the membership challenge whose dual codeword its rows are
orthogonal to. A statement carries the claim's digest (`daClaimDigest`). -/
structure DaClaim where
  /-- The matrix's Merkle root: the commitment to its codewords. -/
  daRoot : Digest
  /-- The membership challenge `z`, which the guest program reads as a hint (`da_challenge`,
  `lean_ethereum.py:4342`); the deployed outer verifier derives it from the root
  (`membership_challenge`, `crates/verifier/src/da.rs:14-17`). -/
  membershipChallenge : E
  deriving DecidableEq, Inhabited

/-- A node's claims: leanXMSS claims, leanSPHINCS claims, and its DA digest: a DA claim's
`daClaimDigest`, or `zeroDigest` without one (`verifier::da::digest`,
`crates/verifier/src/da.rs:19-26`). -/
structure NodeClaims where
  /-- The leanXMSS claims. -/
  xmss : List LeanXmssClaim
  /-- The leanSPHINCS claims. -/
  sphincs : List LeanSphincsClaim
  /-- The DA digest. -/
  daDigest : Digest
/-- A node's statement: its claims and its deferred claim. -/
structure NodeStatement where
  /-- Its signature and DA claims. -/
  claims : NodeClaims
  /-- The claim on the bytecode it defers to its parent. -/
  deferredClaim : DeferredClaim

/-! ## The statement's digest

Each digest is Keccak-256 of its preimage; the preimages are also the inputs of the candidate
collisions (`collisionCandidates`, below). -/

/-- A leanXMSS key's `32` bytes, its root then its parameter (`LeanXmssPublicKey::to_bytes`,
`crates/signatures/src/lean_xmss/scheme.rs:24-29`); a leanSPHINCS key's are `PK.seed ‖ PK.root`
(`Sphincs.PublicKey.toBytes`). -/
def xmssPublicKeyBytes (publicKey : HashSig.PublicKey) : List UInt8 :=
  HashSig.littleEndianBytes 16 publicKey.root ++ HashSig.littleEndianBytes 16 publicKey.parameter

/-- A claim as the `64` bytes its list hashes: the key's bytes (`to_bytes`, by `publicKeyBytes`),
then the message (`claim_cells`, `lean_xmss_claim_cells`, `lean_sphincs_claim_cells`,
`aggregation/statement.rs:39-56`). -/
def claimBytes {PublicKey : Type} (publicKeyBytes : PublicKey → List UInt8)
    (claim : PublicKey × HashSig.Message) : List UInt8 :=
  publicKeyBytes claim.1 ++ HashSig.littleEndianBytes 32 claim.2

/-- The bytes `claimListDigest publicKeyBytes claims` hashes: the claims' bytes one after the
other. -/
def claimListPreimage {PublicKey : Type} (publicKeyBytes : PublicKey → List UInt8)
    (claims : List (PublicKey × HashSig.Message)) : List UInt8 :=
  claims.flatMap (claimBytes publicKeyBytes)

/-- The digest of a list of leanXMSS claims (`publicKeyBytes = xmssPublicKeyBytes`) or of
leanSPHINCS claims (`Sphincs.PublicKey.toBytes`) (`claim_list_digest`,
`aggregation/statement.rs:32-37`, `lean_ethereum.py:4131-4162`). -/
def claimListDigest {PublicKey : Type} (publicKeyBytes : PublicKey → List UInt8)
    (claims : List (PublicKey × HashSig.Message)) : Digest :=
  keccak256 (claimListPreimage publicKeyBytes claims)

/-- A DA claim's digest, which a statement carries: Keccak-256 of the root, then the challenge as
its three limbs and a zero word, little-endian (`digest`, `crates/verifier/src/da.rs:19-26`; the
guest program's `keccak([root_0, root_1], [z_0, z_1])`, `lean_ethereum.py:4613`). -/
def daClaimDigest (claim : DaClaim) : Digest :=
  keccak256 (digestBytes claim.daRoot ++ E.toBytes claim.membershipChallenge ++ List.replicate 8 0)

/-- The DA digest of a statement without a DA claim: zeros (`digest(None)`,
`crates/verifier/src/da.rs:19-26`; `own_da`'s zero cells, `lean_ethereum.py:4615-4616`). -/
def zeroDigest : Digest := Vector.replicate 4 0

/-- The deferred claim's cells, an odd count paired with a zero cell. -/
def paddedDeferredClaimCells (claim : DeferredClaim) : List E :=
  claim.cells ++ if claim.cells.length % 2 = 1 then [0] else []

/-- The bytes `statementDigest seed statement` hashes: the seed, the leanXMSS and leanSPHINCS
claims' digests, the DA digest, then the padded deferred cells. Each list's digest binds its length
through Keccak's padding. -/
def statementPreimage (seed : Digest) (statement : NodeStatement) : List UInt8 :=
  digestBytes seed ++ digestBytes (claimListDigest xmssPublicKeyBytes statement.claims.xmss) ++
    digestBytes (claimListDigest Sphincs.PublicKey.toBytes statement.claims.sphincs) ++
    digestBytes statement.claims.daDigest ++
    (paddedDeferredClaimCells statement.deferredClaim).flatMap E.toBytes

/-- **The statement's digest under `seed`**, a node's public input (`statement_digest`,
`aggregation/statement.rs:85-114`, `lean_ethereum.py:4065-4096`). The cells carry no lengths: the
digest tells two deferred claims apart only at one shape. -/
def statementDigest (seed : Digest) (statement : NodeStatement) : Digest :=
  keccak256 (statementPreimage seed statement)

end LeanVM.Node

/-! ## The witnesses -/

namespace LeanVM.Da

open LeanVM.Parameters

/-- What holds a DA claim: a matrix of codewords. -/
structure MatrixWitness where
  /-- The codewords, one per row. -/
  rows : List (List K)

end LeanVM.Da

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-- A child of a node: its statement, its proof, and what the proof claims of the bytecode. -/
structure Child where
  /-- The child's node statement. -/
  statement : NodeStatement
  /-- The claim on the bytecode its proof makes. -/
  freshClaim : BytecodeClaim
  /-- Its proof. -/
  proof : Proof

/-- What a node holds its statement by: its children, its raw signatures with the claims they
sign, the blob matrix it checks directly with the DA claim it opens (if any), and the batching's
hints. -/
structure NodeWitness where
  /-- The children. -/
  children : List Child
  /-- The raw leanXMSS signatures, each with the claim it signs. -/
  xmssSignatures : List (LeanXmssClaim × LeanXmss.Signature)
  /-- The raw leanSPHINCS signatures, each with the claim it signs. -/
  sphincsSignatures : List (LeanSphincsClaim × Sphincs.Signature)
  /-- The blob matrix the node checks directly, with the DA claim it opens. -/
  daMatrix : Option (DaClaim × Da.MatrixWitness)
  /-- The prover's part of the batching of the children's deferred claims. -/
  batchingHints : BatchingHints

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `aggregation/deferred.rs:196-198`; `BYTECODE_VARS`, `lean_ethereum.py:347`). -/
def DeferredClaim.HasBytecodeShape (bytecode : List K) (claim : DeferredClaim) : Prop :=
  claim.bytecodePoint.length = Nat.log2 bytecode.length

/-- What a leaf defers: the bytecode at the all-zero point (`DeferredClaim::leaf`,
`aggregation/deferred.rs:37-39`; `main`'s leaf branch, `lean_ethereum.py:4659-4667`). The value is
the outer verifier's to check. -/
def DeferredClaim.HasZeroPoint (bytecode : List K) (claim : DeferredClaim) : Prop :=
  claim.bytecodePoint = List.replicate (Nat.log2 bytecode.length) 0

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the value is
the bytecode's multilinear extension at the point (`DeferredClaim::recompute_scalar`,
`aggregation/deferred.rs:50-82`). The length being `2 ^ len` is part of it: `HasBytecodeShape` reads
`Nat.log2` of the length, which a bytecode of other length shares, and the extension is of
`2 ^ len` values. Stronger than `BytecodeClaim.Holds` (the value only). The deployed outer verifier
checks it of the root's deferred claim (`EthereumProof::verify`, `aggregation/proof.rs:149-159`). -/
def DeferredClaim.HoldsWithShape (bytecode : List K) (claim : DeferredClaim) : Prop :=
  claim.HasBytecodeShape bytecode ∧ 2 ^ claim.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) claim.bytecodePoint = claim.bytecodeValue

/-! ## What the guest program proves

`NodeRelation` first, then each of its conditions with what it reads. (A `mutual` block only so
that the relation reads before its parts: nothing in it is recursive.) -/

mutual

/-- **What the witness `witness` establishes of the statement `statement`**, for the guest
program's bytecode `bytecode` and under the seed `seed`: the witnesses cover the claims (the four
conditions below). -/
def NodeRelation (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  SignatureClaimsHeld statement witness ∧ DaDigestHeld statement witness ∧
    ChildrenProven bytecode seed witness ∧ DeferredClaimBatched bytecode seed statement witness

/-- **Every signature claim is held**: every raw signature verifies its claim (at any leaf
index), and every leanXMSS claim is a raw signature's claim or in some child's statement's list;
likewise for leanSPHINCS. Holders need not differ: one raw signature or one child may hold several
equal claims. -/
def SignatureClaimsHeld (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  (∀ raw ∈ witness.xmssSignatures, LeanXmss.verifyWithKeccak raw.1.1 raw.1.2 raw.2 = true) ∧
  (∀ raw ∈ witness.sphincsSignatures, Sphincs.verifyWithKeccak raw.1.1 raw.1.2 raw.2 = true) ∧
  (∀ claim ∈ statement.claims.xmss, claim ∈ witness.xmssSignatures.map (·.1) ∨
    ∃ child ∈ witness.children, claim ∈ child.statement.claims.xmss) ∧
  (∀ claim ∈ statement.claims.sphincs, claim ∈ witness.sphincsSignatures.map (·.1) ∨
    ∃ child ∈ witness.children, claim ∈ child.statement.claims.sphincs)

/-- **The DA digest is held**: it is the digest of the DA claim that the matrix checked here
opens; without such a matrix, zero or some child's DA digest (`da_pick`,
`lean_ethereum.py:4652-4655`). -/
def DaDigestHeld (statement : NodeStatement) (witness : NodeWitness) : Prop :=
  match witness.daMatrix with
  | some (claim, matrix) =>
    statement.claims.daDigest = daClaimDigest claim ∧
      LeanVM.Da.MatrixWitness.Opens claim.daRoot claim.membershipChallenge matrix
  | none =>
    statement.claims.daDigest = zeroDigest ∨
      ∃ child ∈ witness.children, child.statement.claims.daDigest = statement.claims.daDigest

/-- **The matrix opens the DA claim `⟨root, z⟩`** (`da_verify`, `lean_ethereum.py:4331-4371`):
`1` to `1024` codewords of `2^15` symbols commit to `root` (the root of the matrix they form,
`LeanDa.commitCells`, over Keccak-f[1600] with LeanDA's digests as 32 bytes), and each is
orthogonal to the dual codeword of `z`, `L(x) = ∏_j (1 + z^(2^j) Ŵ_j(x))` (`LeanDa.dualCodewordAt`,
which the guest program builds from `z`: `da_vector`, `lean_ethereum.py:4429-4493`). Only where
`z` is the root's membership challenge, as the deployed outer verifier derives it (no end statement
here assumes it), are the rows codewords, except with the membership test's error (`lean_da`'s
`checker_sound`); the link to `lean_da`'s code binding is not proved. -/
def _root_.LeanVM.Da.MatrixWitness.Opens (root : Digest) (z : E)
    (witness : LeanVM.Da.MatrixWitness) : Prop :=
  1 ≤ witness.rows.length ∧ witness.rows.length ≤ LeanDa.maxRows ∧
    (∀ row ∈ witness.rows, row.length = 2 ^ LeanDa.logM) ∧
    LeanDa.commitCells keccakF1600 (LeanDa.cellsOfRows witness.rows) = root.toBytes ∧
    ∀ row ∈ witness.rows, LeanDa.innerProduct (LeanDa.dualCodewordAt z) (fun b ↦ row.getD b 0) = 0

/-- **Every child is proven**: its deferred claim has the bytecode's shape, and the deferring
verifier (`verifyDeferred`, the guest program's `verify_sub`) accepts its proof for its statement's
digest under the same seed. The deferring verifier reads only the bytecode's length: it takes the
bytecode's value at the child's point from the witness (`freshClaim`), which the batching folds into
the node's deferred claim and nothing here checks. -/
def ChildrenProven (bytecode : List K) (seed : Digest) (witness : NodeWitness) : Prop :=
  ∀ child ∈ witness.children, child.statement.deferredClaim.HasBytecodeShape bytecode ∧
    verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
      child.proof = true

/-- **The deferred claim batches the children's**: without children, the bytecode at the zero
point; with children, the batching program (`Batch.nodeBatchingProgram`), over Keccak-f[1600],
accepts the stream of the children's claims (each child's public input, fresh claim and deferred
claim) and the hints, with the statement's deferred claim as its outcome. Either way the deferred
claim has the bytecode's shape: the zero point's, or the sumcheck's `log₂ |bytecode|` challenges. -/
def DeferredClaimBatched (bytecode : List K) (seed : Digest) (statement : NodeStatement)
    (witness : NodeWitness) : Prop :=
  if witness.children = [] then statement.deferredClaim.HasZeroPoint bytecode
  else
    let children : List ChildClaims := witness.children.map fun child ↦
      ⟨statementDigest seed child.statement, child.freshClaim, child.statement.deferredClaim⟩
    Guest.Batch.runBatching (m := Id) keccakF1600
      (Guest.Batch.nodeBatchingProgram (· = statement.deferredClaim) bytecode children)
      ⟨Guest.Batch.batchingStream children witness.batchingHints, []⟩ = true

end

/-! ## What a proof of the guest program establishes, its witness named -/

/-- What a decoder names on an execution: a seed, a statement and a witness. -/
structure SeedStatementAndWitness where
  /-- The seed of the statement's digest. -/
  seed : Digest
  /-- The node statement. -/
  statement : NodeStatement
  /-- Its witness. -/
  witness : NodeWitness

/-- **The decoding explains the public input `input`**: its seed and statement have the input's
digest (the statement is the one the input commits to), and its witness holds that statement's
claims (`NodeRelation`). `GuestKnowledgeSoundness` (below) says this of what the decoder
program outputs on every valid execution. -/
def ExplainsPublicInput (guest : LeanIsaProgram) (input : PublicInput)
    (decoding : SeedStatementAndWitness) : Prop :=
  statementDigest decoding.seed decoding.statement = publicInputDigest input ∧
    NodeRelation (bytecodeWords guest) decoding.seed decoding.statement decoding.witness

/-- **The candidate collisions** of two statements' digests: the pairs of inputs of the three
hashes the digests compute, the outer one and the two claim lists'. The DA digest enters the
preimage as it is. -/
def collisionCandidates (seed : Digest) (statement : NodeStatement) (seed' : Digest)
    (statement' : NodeStatement) : List (List UInt8 × List UInt8) :=
  [(statementPreimage seed statement, statementPreimage seed' statement'),
    (claimListPreimage xmssPublicKeyBytes statement.claims.xmss,
      claimListPreimage xmssPublicKeyBytes statement'.claims.xmss),
    (claimListPreimage Sphincs.PublicKey.toBytes statement.claims.sphincs,
      claimListPreimage Sphincs.PublicKey.toBytes statement'.claims.sphincs)]

/-- **A collision**: a pair of different inputs with the same Keccak-256 digest, among
`pairs`. -/
def HasCollision (pairs : List (List UInt8 × List UInt8)) : Prop :=
  ∃ p ∈ pairs, p.1 ≠ p.2 ∧ keccak256 p.1 = keccak256 p.2

/-- **The statement's digest binds the seed and the statement**: two statements whose deferred
claims have the shape of one bytecode and whose digests (under two seeds) are equal are the same
statement under the same seed, or one of the candidate pairs is a Keccak-256 collision. The shape
fixes the length of the deferred claim's point, which the digest does not record. Proved by
`LeanVM.Guest.Binding.digest_binds`. -/
def StatementDigestBinds : Prop :=
  ∀ (bytecode : List K) (seed seed' : Digest) (statement statement' : NodeStatement),
    statement.deferredClaim.HasBytecodeShape bytecode →
    statement'.deferredClaim.HasBytecodeShape bytecode →
    statementDigest seed statement = statementDigest seed' statement' →
    (seed = seed' ∧ statement = statement') ∨
      HasCollision (collisionCandidates seed statement seed' statement')

/-- The guest program's deployed seed: its Fiat-Shamir IV (`fs_seed`,
`crates/leanvm_core/src/cpu/mod.rs:48-50`). -/
abbrev deployedSeed (guest : LeanIsaProgram) : Digest := fiatShamirIv (bytecodeWords guest)

end LeanVM.Node

namespace LeanVM.Guest

/-- **The deployed leanISA guest program**, assembled from the generated `Statement/Data/`. -/
def guestProgram : LeanVM.Semantics.LeanIsaProgram := assemble Data.functions 19 (by decide)

end LeanVM.Guest

/-! ## The guest decoder a program computes

`GuestKnowledgeSoundness` takes the decoder that names the witness as a program `D` of the cost
machine (`CostMachine.lean`), as `KnowledgeSoundness` takes the extractor: `D`, of size at most
`guestWitnessDecoderSizeBound`, is run on the encoded program and execution
(`encodeGuestWitnessDecoderInput`) within `guestWitnessDecoderBudget`, and its output is the
encoding (`encodeValue`) of a decoding that explains the public input. There is no parse: the
statement names the decoding, and the encoding is injective (`lean_vm`'s
`LeanVM.Cost.encodeValue_decoded_injective`). `D` may compute the witness by any algorithm; what
excludes one that chooses is that it is a program (no classical choice) whose only runtime data is
its input, of bounded size, run within a proved upper bound on the compiled decoder's price. -/

namespace LeanVM.Cost

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

/-! ### The encodings of a decoding: a constructor of tag `0` for each structure, its fields in
order -/

instance : MachineEncoding HashSig.PublicKey :=
  ⟨fun k ↦ .constructor 0 [encodeValue k.root, encodeValue k.parameter]⟩

instance : MachineEncoding Sphincs.PublicKey :=
  ⟨fun k ↦ .constructor 0 [encodeValue k.publicSeed, encodeValue k.root]⟩

instance : MachineEncoding LeanXmss.LayerSignature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.randomizer, encodeValue σ.chainValues,
    encodeValue σ.authenticationPath]⟩

instance : MachineEncoding LeanXmss.Signature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.leafIndex, encodeValue σ.layers]⟩

instance : MachineEncoding Sphincs.ForsTreeOpening :=
  ⟨fun o ↦ .constructor 0 [encodeValue o.secret, encodeValue o.path]⟩

instance (layer : Sphincs.Layer) : MachineEncoding (Sphincs.LayerSignature layer) :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.counter, encodeValue σ.chainValues,
    encodeValue σ.authenticationPath]⟩

/-- A signature; its layers, a dependent function of the layer, as the array of their values,
bottom first. -/
instance : MachineEncoding Sphincs.Signature :=
  ⟨fun σ ↦ .constructor 0 [encodeValue σ.randomizer, encodeValue σ.forsOpening,
    .array (Array.ofFn fun layer ↦ encodeValue (σ.layers layer))]⟩

instance : MachineEncoding BytecodeClaim :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.bytecodePoint, encodeValue c.bytecodeValue]⟩

instance : MachineEncoding DaClaim :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.daRoot, encodeValue c.membershipChallenge]⟩

instance : MachineEncoding Da.MatrixWitness :=
  ⟨fun m ↦ .constructor 0 [encodeValue m.rows]⟩

instance : MachineEncoding NodeClaims :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.xmss, encodeValue c.sphincs, encodeValue c.daDigest]⟩

instance : MachineEncoding NodeStatement :=
  ⟨fun s ↦ .constructor 0 [encodeValue s.claims, encodeValue s.deferredClaim]⟩

instance : MachineEncoding Child :=
  ⟨fun c ↦ .constructor 0 [encodeValue c.statement, encodeValue c.freshClaim, encodeValue c.proof]⟩

instance : MachineEncoding BatchingHints :=
  ⟨fun h ↦ .constructor 0 [encodeValue h.sumcheckMessages, encodeValue h.finalBytecodeValue]⟩

instance : MachineEncoding NodeWitness :=
  ⟨fun w ↦ .constructor 0 [encodeValue w.children, encodeValue w.xmssSignatures,
    encodeValue w.sphincsSignatures, encodeValue w.daMatrix, encodeValue w.batchingHints]⟩

instance : MachineEncoding SeedStatementAndWitness :=
  ⟨fun decoding ↦ .constructor 0 [encodeValue decoding.seed, encodeValue decoding.statement,
    encodeValue decoding.witness]⟩

/-- **The decoder's input**: the program and its execution (the memory's log-size `κ`, its `2^κ`
words, the steps). -/
def encodeGuestWitnessDecoderInput (program : Semantics.LeanIsaProgram)
    (execution : Execution program) : MachineValue :=
  .constructor 0 [encodeValue program, encodeValue execution]

end LeanVM.Cost

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics

/-! ### The guest decoder's size bound and budget

`statement.tex` (*Soundness*, the decoder's budget and size bound) has their measurements and
limits. -/

/-- **The bound on the guest decoder program's size** (`MachineProgram.size`): `463560`, a bound
`lean_vm`'s `Cost/DecoderSize.lean` proves on the compiled decoder's size at the pin (`../leanvm-rev`)
plus a slack of `430`, room for one leanXMSS signature's encoding (`309`) but not
two, so no useful table of witnesses (hard-coded signatures, matrices or proofs that would mask a
bug of the guest program on finitely many statements) fits beside the compiled decoder's code. The
size counts in full the guest program's per-function tables, literals of the compiled decoder; a
program written differently could hold more. -/
def guestWitnessDecoderSizeBound : ℕ := 463560

/-- **The guest decoder's budget** on an execution of `program` of `steps` steps on a memory of
`2^κ` words: the most the decoder's run may cost, in the machine's price (so also the most steps it
may execute), with `lg = log₂(steps + 1)`,
`(steps + 1)·(2^21 + 2^13·lg) + (70κ + 374 + 2^23 + 2^14·lg)·2^κ + 2^37·(lg + 16)`: per step, the
step replayed and filed in a sorted table of function entries; per memory word, the sorted table of
the memory's addresses and the witness read at the counts the guest program's asserts bound on
every valid execution (each below the memory's size, `assert_gpow`); and the witness read at the
cursors and the other counts they bound.
`lean_vm` proves the compiled decoder's price at most this on every valid execution
(`decoderPriceWithinBudget`, `Cost/Bounds/Guest/Budget.lean`). The constants are the deployed
guest program's, and `program` is only ever `LeanVM.Guest.guestProgram`. -/
def guestWitnessDecoderBudget {program : LeanIsaProgram} (execution : Execution program) : ℕ :=
  (execution.stepCount + 1) * (2 ^ 21 + 2 ^ 13 * Nat.log2 (execution.stepCount + 1)) +
    (70 * execution.logMemorySize + 374 + 2 ^ 23 + 2 ^ 14 * Nat.log2 (execution.stepCount + 1)) *
      2 ^ execution.logMemorySize +
    2 ^ 37 * (Nat.log2 (execution.stepCount + 1) + 16)

/-- **Knowledge soundness of the leanISA guest program, its witness named**: on every valid
execution of `LeanVM.Guest.guestProgram` on a public input, the decoder program
`guestWitnessDecoder`, of size at most `guestWitnessDecoderSizeBound`, run on the encoded program
and execution within its budget, outputs the encoding of a decoding that explains the input
(`ExplainsPublicInput`: a seed, the node statement the input commits to under it, and a witness
holding it). A larger program, or a run that fails or exceeds its budget, outputs nothing, so the
statement fails at that execution (the completeness statements give the guest program valid
executions). -/
def GuestKnowledgeSoundness (guestWitnessDecoder : Cost.MachineProgram) : Prop :=
  ∀ input (execution : Execution Guest.guestProgram),
    ValidExecution Guest.guestProgram input execution →
    ∃ decoding : SeedStatementAndWitness,
      Cost.outputWithin guestWitnessDecoder guestWitnessDecoderSizeBound
          (guestWitnessDecoderBudget execution)
          (Cost.encodeGuestWitnessDecoderInput Guest.guestProgram execution) =
        some (Cost.encodeValue decoding) ∧
      ExplainsPublicInput Guest.guestProgram input decoding

end LeanVM.Node

end
