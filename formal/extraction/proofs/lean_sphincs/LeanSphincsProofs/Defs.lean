import LeanSphincs
import Statement.LeanSphincs
import Keccak256Proofs.Defs

/-!
# What is proved about the extraction of `crates/lean_sphincs`, stated

The Rust `verify`, as hax extracts it (`lean_sphincs.scheme.verify`), computes the statement's
`Sphincs.verifyWithKeccak` (`formal/Statement/LeanSphincs.lean`) on the values its arguments stand
for. This file fixes how a Rust key and signature stand for the statement's, and the statement of
each function's theorem, as a `Prop` the files beside this one prove and compose. How Rust's bytes
stand for the statement's bit vectors (`toDigest`, `toMessage`), and what the proofs ask of the
hasher (`HasherSpec`), are shared with leanXMSS (`Keccak256Proofs.Defs`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation Sphincs
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open Keccak256Proofs

namespace LeanSphincsProofs

/-! ## Keys and signatures -/

/-- The Rust public key as the statement's. -/
def toPublicKey (pk : lean_sphincs.scheme.LeanSphincsPublicKey) : Sphincs.PublicKey :=
  ⟨toDigest pk.pk_seed, toDigest pk.root⟩

instance : Inhabited lean_sphincs.fors.ForsTreeOpening := ⟨⟨default, default⟩⟩
instance : Inhabited lean_sphincs.scheme.LayerSignature := ⟨⟨default, default⟩⟩

/-- One FORS tree's opening as the statement's. -/
def toForsOpening (o : lean_sphincs.fors.ForsTreeOpening) : Sphincs.ForsTreeOpening :=
  ⟨toDigest o.secret, fun z ↦ toDigest o.path.val[z.val]!⟩

/-- Layer `l` of a Rust signature as the statement's: its counter, its chain values, and its
path, which the crate keeps in `paths` after the paths of the layers below (`path_range`). -/
def toLayerSignature (sig : lean_sphincs.scheme.LeanSphincsSignature) (l : Layer) :
    Sphincs.LayerSignature l :=
  ⟨(sig.layers.val[l.val]!).counter.bv,
    fun i ↦ toDigest (sig.layers.val[l.val]!).wots.val[i.val]!,
    fun z ↦ toDigest sig.paths.val[bitsBelowLayer l + z.val]!⟩

/-- The Rust signature as the statement's. -/
def toSignature (sig : lean_sphincs.scheme.LeanSphincsSignature) : Sphincs.Signature :=
  ⟨toDigest sig.randomizer, fun κ ↦ toForsOpening sig.fors.val[κ.val]!, toLayerSignature sig⟩

/-! ## Addresses and keys -/

/-- A Rust address holds the bytes of the statement's. -/
def AdrsIs (a : lean_sphincs.hash.Adrs) (A : Sphincs.Address) : Prop := bytes a.val = A.toBytes

/-- A Rust one-time key is the statement's `(layer, tree, leaf)`. -/
def KeyIs (k : lean_sphincs.wots.OtsKey) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex) : Prop :=
  k.layer.val = layer.val ∧ k.tree.val = tree.val ∧ k.leaf.val = leaf.val

/-- hax's `Option` as Lean's. -/
def ofOption {α : Type} : core.option.Option α → Option α
  | .None => none
  | .Some x => some x

/-! ## Each function's theorem -/

section
variable (π : KeccakState → KeccakState)

/-- `th`: the truncated hash of `PK.seed ‖ ADRS ‖ M`. -/
def ThSpec : Prop :=
  ∀ (seed : Array Std.U8 16#usize) (adrs : lean_sphincs.hash.Adrs) (m : Slice Std.U8),
    ∃ d, lean_sphincs.hash.th seed adrs m = ok d ∧
      toDigest d = truncateHash (Id.run (keccakHash (inId π)
        (bytes seed.val ++ bytes adrs.val ++ bytes m.val)))

/-- `OtsKey::adrs`: a key's address of a type, the last two words zero. -/
def KeyAdrsSpec : Prop :=
  ∀ (k : lean_sphincs.wots.OtsKey) (t : Std.U32) (T : AddressType), t.val = T.word →
    k.layer.val < 2 ^ 32 →
    ∃ a, lean_sphincs.wots.OtsKey.adrs k t = ok a ∧
      AdrsIs a (makeAddress k.layer.val k.tree.val T k.leaf.val 0 0)

/-- `Adrs::with_chain`, `with_tree_height` (the fifth word) and `with_hash`, `with_tree_index`
(the sixth) set one word. -/
def AdrsWordSpec : Prop :=
  ∀ (a : lean_sphincs.hash.Adrs) (A : Sphincs.Address) (v : Std.U32), AdrsIs a A →
    (∃ a', lean_sphincs.hash.Adrs.with_chain a v = ok a' ∧
      AdrsIs a' { A with chainOrTreeHeight := v.bv }) ∧
    (∃ a', lean_sphincs.hash.Adrs.with_tree_height a v = ok a' ∧
      AdrsIs a' { A with chainOrTreeHeight := v.bv }) ∧
    (∃ a', lean_sphincs.hash.Adrs.with_hash a v = ok a' ∧
      AdrsIs a' { A with hashOrTreeIndex := v.bv }) ∧
    (∃ a', lean_sphincs.hash.Adrs.with_tree_index a v = ok a' ∧
      AdrsIs a' { A with hashOrTreeIndex := v.bv })

/-- `OtsKey::tree_adrs` then `with_type`: a tree's address of a type, the last three words
zero (`node`). -/
def TreeAdrsSpec : Prop :=
  ∀ (k : lean_sphincs.wots.OtsKey) (t : Std.U32) (T : AddressType), t.val = T.word →
    k.layer.val < 2 ^ 32 →
    ∃ a a', lean_sphincs.wots.OtsKey.tree_adrs k = ok a ∧
      lean_sphincs.hash.Adrs.with_type a t = ok a' ∧
      AdrsIs a' (makeAddress k.layer.val k.tree.val T 0 0 0)

/-- `OtsKey::of_index`: the key of a layer on the way up from an index. -/
def OfIndexSpec : Prop :=
  ∀ (layer : Std.Usize) (idx : Std.U64) (l : Layer) (index : Index),
    layer.val = l.val → idx.val = index.val →
    ∃ k, lean_sphincs.wots.OtsKey.of_index layer idx = ok k ∧
      KeyIs k l (treeOfIndex l index) (leafOfIndex l index)

/-- `chain`: `steps` steps of a chain from `start`. -/
def ChainSpec : Prop :=
  ∀ (seed : Array Std.U8 16#usize) (k : lean_sphincs.wots.OtsKey) (i start steps : Std.Usize)
    (v : Array Std.U8 16#usize) (layer : Layer) (tree : TreeIndex) (leaf : TreeLeafIndex)
    (chainIndex : ChainIndex),
    KeyIs k layer tree leaf → i.val = chainIndex.val → start.val + steps.val ≤ 3 →
    ∃ r, lean_sphincs.wots.chain seed k i start steps v = ok r ∧
      toDigest r = Id.run (Verification.chainWalk (inId π) (toDigest seed) layer tree leaf
        chainIndex start.val steps.val (toDigest v))

/-- `wots_leaf`: the one-time leaf a claimed signature recovers. -/
def WotsLeafSpec : Prop :=
  ∀ (seed : Array Std.U8 16#usize) (k : lean_sphincs.wots.OtsKey) (msg : Array Std.U8 16#usize)
    (c : Std.U32) (sig : Array (Array Std.U8 16#usize) 64#usize) (layer : Layer)
    (tree : TreeIndex) (leaf : TreeLeafIndex),
    KeyIs k layer tree leaf →
    ∃ o, lean_sphincs.wots.wots_leaf seed k msg c sig = ok o ∧
      (ofOption o).map (fun p ↦ toDigest p.2) =
        Id.run (Verification.otsLeaf (inId π) (toDigest seed) layer tree leaf (toDigest msg) c.bv
          (fun i ↦ toDigest sig.val[i.val]!))

/-- `tree_root`: a key's leaf and its path folded to its tree's root. -/
def TreeRootSpec : Prop :=
  ∀ (seed : Array Std.U8 16#usize) (k : lean_sphincs.wots.OtsKey) (leafValue : Array Std.U8 16#usize)
    (path : Slice (Array Std.U8 16#usize)) (layer : Layer) (tree : TreeIndex)
    (leaf : TreeLeafIndex),
    KeyIs k layer tree leaf → path.length ≤ 16 →
    ∃ r, lean_sphincs.scheme.tree_root seed k leafValue path = ok r ∧
      toDigest r = Id.run (Verification.treeFold (inId π) (toDigest seed) layer tree leaf
        (fun z ↦ toDigest path.val[z]!) path.length (toDigest leafValue))

/-- `fors_root`: the FORS public key an opening reaches. -/
def ForsRootSpec : Prop :=
  ∀ (seed : Array Std.U8 16#usize) (idx : Std.U64) (leaves : Array Std.Usize 24#usize)
    (opening : Array lean_sphincs.fors.ForsTreeOpening 24#usize) (index : Index),
    idx.val = index.val → (∀ κ : ForsTreeIndex, leaves.val[κ.val]!.val < 2 ^ forsTreeHeight) →
    ∃ r, lean_sphincs.fors.fors_root seed idx leaves opening = ok r ∧
      toDigest r = Id.run (Verification.forsRecover (inId π) (toDigest seed) index
        (fun κ ↦ forsLeafOfNat leaves.val[κ.val]!.val)
        (fun κ ↦ toForsOpening opening.val[κ.val]!))

/-- `message_digest`: the index and the FORS leaves the message digest spells. -/
def MessageDigestSpec : Prop :=
  ∀ (pk : lean_sphincs.scheme.LeanSphincsPublicKey) (r : Array Std.U8 16#usize)
    (m : Array Std.U8 32#usize),
    ∃ idx leaves, lean_sphincs.scheme.message_digest pk r m = ok (idx, leaves) ∧
      idx.val = (digestIndex (Id.run (Verification.messageDigest (inId π) (toPublicKey pk)
        (toDigest r) (toMessage m)))).val ∧
      ∀ κ : ForsTreeIndex, leaves.val[κ.val]!.val =
        (digestForsLeaves (Id.run (Verification.messageDigest (inId π) (toPublicKey pk)
          (toDigest r) (toMessage m))) κ).val

/-- **`verify`**: the Rust verifier returns, and returns the statement's verdict. -/
def VerifySpec : Prop :=
  ∀ (pk : lean_sphincs.scheme.LeanSphincsPublicKey) (m : Array Std.U8 32#usize)
    (sig : lean_sphincs.scheme.LeanSphincsSignature),
    lean_sphincs.scheme.verify pk m sig =
      ok (Id.run (Verification.verify (inId π) (toPublicKey pk) (toMessage m) (toSignature sig)))

end

end LeanSphincsProofs
