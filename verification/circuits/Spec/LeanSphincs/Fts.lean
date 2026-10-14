import LeanSphincs.TweakHash

/-!
# `LeanSphincs.Fts`

The few-time signature (FORS+C): `k - 1` Merkle trees of `2^a` secret leaves, the verifier's half
(`programs/leansphincs/guest/src/fts.rs` lines 12 to 66).
-/

namespace LeanSphincs.Fts

open LeanSphincs.Constants
open EthCryptographySpecs.Xmss (packBytes)

/-- Leaf `j` of tree `kappa` of forest `idx`: the hash of its secret (`LeafHash::leaf`, fts.rs lines 21 to 28). -/
def leaf (pp : PublicParam) (idx : Nat) (kappa j : Nat) (secret : Digest) : Digest :=
  th pp (tweak .ftsLeaf kappa (UInt32.ofNat idx) 0 (UInt32.ofNat j)) (packBytes secret)

/-- `Fts.key`: the few-time public key, `Th` over the 14 roots in order (`key`, fts.rs lines 41 to 49). -/
def key (pp : PublicParam) (idx : Nat) (roots : List Digest) : Digest :=
  th pp (tweak .ftsRoots 0 (UInt32.ofNat idx) 0 0) (concatDigests roots)

/-- `Fts.recover`: the few-time key an opening of the leaves `u` reaches (`recover`, fts.rs lines 51 to 66): tree
`kappa`'s root is its opened leaf folded up its path under `tweak .ftsNode kappa idx`. -/
def recover (pp : PublicParam) (idx : Nat) (u : Vector Nat K) (opening : Vector FtsOpening FTS_TREES) : Digest :=
  key pp idx (List.ofFn fun kappa : Fin FTS_TREES =>
    let opened := u[kappa.val]'(by have := kappa.isLt; simp only [FTS_TREES, K] at this ⊢; omega)
    let o := opening[kappa]
    fold pp .ftsNode kappa (UInt32.ofNat idx) opened (leaf pp idx kappa opened o.secret) o.path.toList)

end LeanSphincs.Fts
