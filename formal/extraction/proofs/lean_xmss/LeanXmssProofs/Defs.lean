import LeanXmss
import Statement.LeanXmss
import Keccak256Proofs.Defs

/-!
# What is proved about the extraction of `crates/lean_xmss`, stated

The Rust `verify`, as hax extracts it (`lean_xmss.scheme.verify`), computes the statement's
`LeanXmss.verifyWithKeccak` (`formal/Statement/LeanXmss.lean`) on the values its arguments stand
for. This file fixes how a Rust key and signature stand for the statement's, and the statement of
each function's theorem, as a `Prop` the files beside this one prove and compose. How Rust's bytes
stand for the statement's bit vectors, and what the proofs ask of the hasher (`HasherSpec`), are
shared with leanSPHINCS (`Keccak256Proofs.Defs`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation LeanXmss
open LeanVM.Semantics (KeccakState)
open Keccak256Proofs

namespace LeanXmssProofs

/-! ## Keys and signatures -/

/-- The Rust public key as the statement's: the root, then the public parameter. -/
def toPublicKey (pk : lean_xmss.scheme.LeanXmssPublicKey) : HashSig.PublicKey :=
  ⟨toDigest pk.merkle_root, toDigest pk.public_param⟩

/-- One layer's signature as the statement's: the randomizer, the chain values, the path. -/
def toLayerSignature (s : lean_xmss.scheme.LayerSignature) : LeanXmss.LayerSignature :=
  ⟨toDigest s.randomizer, fun i ↦ toDigest s.chain_values.val[i.val]!,
    fun z ↦ toDigest s.path.val[z.val]!⟩

/-- A Rust leaf index, a `u32`, as the statement's. -/
def toLeafIndex (i : Std.U32) : LeafIndex := ⟨i.val, i.hBounds⟩

/-- The Rust signature as the statement's: the leaf index, the bottom layer's signature at layer
`0` and the top layer's at layer `1`. -/
def toSignature (sig : lean_xmss.scheme.LeanXmssSignature) : LeanXmss.Signature :=
  ⟨toLeafIndex sig.leaf_index,
    fun l ↦ if l.val = 0 then toLayerSignature sig.bottom else toLayerSignature sig.top⟩

/-- hax's `Option` as Lean's. -/
def ofOption {α : Type} : core.option.Option α → Option α
  | .None => none
  | .Some x => some x

end LeanXmssProofs
