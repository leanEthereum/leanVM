module

public import Statement.SufCma
public import Statement.Fast.Keccak

/-!
# Hash-based signatures: what leanXMSS and leanSPHINCS share

Read before the two schemes,: the sizes and types both schemes use, the shape of
their tweakable hash `Truncate_16(H(prefix ‖ address ‖ payload))` (`hasherInput`, `truncateHash`:
`hasher` and `truncate` of `crates/signatures/src/lib.rs`), each scheme laying out its own address;
the hash `H`, Keccak-256 over a permutation `π` of the Keccak state in any monad (`keccakHash`), and
the hash chains and Merkle paths every chain and path of both schemes instantiates (`walkChain`,
`foldPath`: the crate's shared `path_fold`), and leanXMSS's Merkle trees (`buildTree`; namespace
`HashSig.OverPermutation`).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace HashSig

/-! ## The sizes and types both schemes share -/

/-- `n`: a digest's bits (`128`, `16` bytes: `N`, `crates/signatures/src/lib.rs`, both schemes'
`N`). -/
def digestBits : Nat := 128
/-- `w`: the bits of a Winternitz digit (`2`). -/
def winternitzBits : Nat := 2
/-- A hash chain's positions, `2^w` (`4`): a digit's values. -/
def chainLength : Nat := 2 ^ winternitzBits
/-- The key's secret seed `S_0`, `256` bits. -/
abbrev MasterSeed := BitVec 256
/-- A digest: a tweakable hash's output, `n` bits (a chain value, a Merkle node, a root). -/
abbrev Digest := BitVec digestBits
/-- The hash `H`'s output, `256` bits, before truncation to a digest. -/
abbrev HashOutput := BitVec 256
/-- A message to sign, `256` bits. -/
abbrev Message := BitVec 256
/-- The public parameter `P`, `128` bits, prefixed to every addressed (tweakable) hash call. -/
abbrev PublicParameter := BitVec 128
/-- A signature's randomizer, one digest. -/
abbrev Randomizer := Digest
/-- A Winternitz digit, a chain's position: `0` to `chainLength - 1`. -/
abbrev WinternitzDigit := Fin chainLength
/-- A step along a chain, from position `t` to `t + 1`: `0` to `chainLength - 2`. -/
abbrev ChainStep := Fin (chainLength - 1)
/-- A hash call's input bytes. -/
abbrev HashInput := List UInt8

/-- `Truncate_16` (`truncate`, `crates/signatures/src/lib.rs`): keep the first 16 bytes of a
hash output, the low 128 bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- leanXMSS's public key `pk = (root, P)` (`LeanXmssPublicKey`,
`crates/signatures/src/lean_xmss/scheme.rs`); leanSPHINCS's is `Sphincs.PublicKey`. -/
structure PublicKey where
  /-- The Merkle root over the key's one-time public keys. -/
  root : Digest
  /-- The public parameter `P`. -/
  parameter : PublicParameter
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def littleEndianBytes (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- `d_0 || ... || d_{n-1}`, 16 bytes each: a one-time key's chain ends, which its leaf hashes. -/
def digestsPayload {n : Nat} (digests : Fin n → Digest) : HashInput :=
  (List.ofFn digests).flatMap (littleEndianBytes 16)

/-- The first `n` base-`2^w` digits of a digest, little endian: digit `i` is bits `w i` to
`w i + w - 1`, how far a WOTS+C signature opens chain `i`. -/
def digestDigits {n : Nat} (digest : Digest) (i : Fin n) : WinternitzDigit :=
  (digest.extractLsb' (winternitzBits * i.val) winternitzBits).toFin

/-- `prefix || address || payload`: the input of both schemes' tweakable hash
`Truncate_16(H(prefix || address || payload))`, the bytes a `hasher(prefix, address)` absorbs before
the payload (`hasher`, `lib.rs`). The prefix is a scheme's 16-byte public value (leanXMSS's
public parameter `P`), the address each scheme's own. -/
def hasherInput (hashPrefix : PublicParameter) (address payload : HashInput) : HashInput :=
  littleEndianBytes 16 hashPrefix ++ address ++ payload

/-- **The key's seed `S_0`**, sampled uniformly. -/
noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace OverPermutation

open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)

/-! ## Chains, Merkle paths and trees, and the hash, over a permutation `π` -/

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

/-- `steps` steps of a hash chain from position `start`: the step leaving position
`t < stepFunctionCount` is `step t`, and a walk past position `stepFunctionCount` gives `0`. -/
def walkChain {m : Type → Type} [Monad m] {stepFunctionCount : Nat}
    (step : Fin stepFunctionCount → Digest → m Digest) :
    Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← walkChain step start steps value
      if h : start + steps < stepFunctionCount then step ⟨start + steps, h⟩ previous else pure 0

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  littleEndianBytes 16 left ++ littleEndianBytes 16 right

/-- Fold the leaf at index `leafIndex` and its path, the sibling at level `l` being
`siblingAtLevel l`, up `levels` levels: the node at level `l + 1` is
`node l (leafIndex / 2^(l + 1))` of its children in index order (`path_fold`,
`crates/signatures/src/lib.rs`, both schemes' Merkle paths). -/
def foldPath {m : Type → Type} [Monad m] (node : Nat → Nat → HashInput → m Digest)
    (leafIndex : Nat) (siblingAtLevel : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | l + 1, value => do
      let current ← foldPath node leafIndex siblingAtLevel l value
      node l (leafIndex / 2 ^ (l + 1))
        (if leafIndex.testBit l then nodePayload (siblingAtLevel l) current
          else nodePayload current (siblingAtLevel l))

/-- Node `index` at level `level` of the Merkle tree over the leaves `leaf i`: the node at level
`l + 1` is `node l index` of its two children. -/
def buildTree {m : Type → Type} [Monad m] (leaf : Nat → m Digest)
    (node : Nat → Nat → HashInput → m Digest) : Nat → Nat → m Digest
  | 0, index => leaf index
  | l + 1, index => do
      let left ← buildTree leaf node l (2 * index)
      let right ← buildTree leaf node l (2 * index + 1)
      node l index (nodePayload left right)

variable {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)

/-- **The hash `H`**: Keccak-256 over the permutation `π` (`keccak256With`), its digest's 32 bytes
(`digestBytes`) read as a little-endian number. -/
def keccakHash (input : HashInput) : m HashOutput :=
  (fun digest ↦ BitVec.ofNat 256 ((digestBytes digest).foldr (fun b acc ↦ b.toNat + 256 * acc) 0))
    <$> keccak256With π input

end OverPermutation

end HashSig
