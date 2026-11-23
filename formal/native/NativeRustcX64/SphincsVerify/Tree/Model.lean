module

public import NativeRustcX64.SphincsVerify.Basic

/-!
# The tree region's model facts (x86-64)

Layer `l`'s next message as the machine computes it: the fold's step at height `z`
(`Run.foldStep`: the node above (`Run.nodeAdrs`) of the children (`Run.children`: the current
value and the sibling, bit `z` of the key's leaf saying which is left)) and the fold after `z`
steps (`Run.foldUpTo`, `Tree.foldUpTo_succ`), which after `heightOf l` steps is `Run.layerRoot`
(`Tree.layerRoot_eq`). Layer `l`'s path from node `pathStart l` of the 26, in the frame at
`24764 + 16 j` (`Tree.bytesAt_sibling`). The addresses' bytes (`Tree.keyAdrs_one`,
`Tree.nodeAdrs_eq`).
-/

namespace NativeRustcX64.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs LeanVM.Protocol.KeccakHash Native.Keccak

@[expose] public section

/-- Where layer `l`'s path starts among the 26 nodes. -/
def Tree.pathStart (l : Nat) : Nat := (layerHeights.take l).sum

/-- Layer `l`'s height. -/
def Tree.heightOf (l : Nat) : Nat := layerHeights.getD l 0

namespace Run

variable (r : Run)

/-- Node `z` of layer `l`'s path, the sibling at height `z`. -/
def sibling (l z : Nat) : List UInt8 := (r.sig.path l).getD z []

/-- The address of the node above height `z`. -/
def nodeAdrs (l z : Nat) : List UInt8 :=
  withTreeIndex (withTreeHeight (withType (r.key l).treeAdrs 2) (z + 1).toUInt32)
    ((r.key l).leaf.toNat >>> (z + 1)).toUInt32

/-- The children of the node above height `z`, from the value `cur`. -/
def children (l : Nat) (cur : List UInt8) (z : Nat) : List UInt8 :=
  if (r.key l).leaf.toNat >>> z &&& 1 = 0 then cur ++ r.sibling l z else r.sibling l z ++ cur

/-- **The fold's step** at height `z` from the current value `cur`. -/
def foldStep (l : Nat) (cur : List UInt8) (z : Nat) : List UInt8 :=
  th r.seed (r.nodeAdrs l z) (r.children l cur z)

/-- **The fold after `z` steps** from the one-time leaf of the chain ends `e`. -/
def foldUpTo (l : Nat) (e : List (List UInt8)) (z : Nat) : List UInt8 :=
  (List.range z).foldl (r.foldStep l) (wotsLeafHash r.seed (r.key l) e)

/-- The node's hash input: `PK.seed | ADRS | children`. -/
def nodeIn (l : Nat) (e : List (List UInt8)) (z : Nat) : List UInt8 :=
  r.seed ++ r.nodeAdrs l z ++ r.children l (r.foldUpTo l e z) z

end Run

end

namespace Tree

public section

/-! ## Addresses -/

/-- The one-time key's address of type `1` (`WOTS_PK`). -/
theorem keyAdrs_one (key : OtsKey) :
    key.adrs 1 = be32 key.layer.toUInt32 ++ ([0, 0, 0, 0] ++ (be64 key.tree ++ (be32 1 ++
      (be32 key.leaf ++ List.replicate 8 0)))) := rfl

/-- A node's address: type `2`, the height and the index. -/
theorem nodeAdrs_eq (key : OtsKey) (z j : UInt32) :
    withTreeIndex (withTreeHeight (withType key.treeAdrs 2) z) j =
      be32 key.layer.toUInt32 ++ ([0, 0, 0, 0] ++ (be64 key.tree ++ (be32 2 ++
        ([0, 0, 0, 0] ++ (be32 z ++ be32 j))))) := rfl

theorem length_adrs (key : OtsKey) (t : UInt32) : (key.adrs t).length = 32 := rfl

/-! ## Lengths -/

theorem pathStart_lt {l : Nat} (hl : l < 3) : pathStart l + heightOf l ≤ 26 := by
  interval_cases l <;> decide

theorem pathStart_cases {l : Nat} (hl : l < 3) :
    pathStart l = 0 ∨ pathStart l = 8 ∨ pathStart l = 16 := by
  interval_cases l <;> decide

theorem heightOf_le {l : Nat} (hl : l < 3) : heightOf l ≤ 10 := by
  interval_cases l <;> decide

theorem heightOf_pos {l : Nat} (hl : l < 3) : 0 < heightOf l := by
  interval_cases l <;> decide

theorem length_th (seed adrs m : List UInt8) : (th seed adrs m).length = 16 := by
  rw [th, List.length_take, NativeRustc.Sphincs.length_hashBytes]
  rfl

theorem length_pkBytes (w : Nat → UInt64) : (pkBytes w).length = 32 := by
  rw [pkBytes, Proof.length_wordsBytes]
  simp

variable (r : Run)

theorem sig_eq : r.sig = sigOf r.w := rfl

theorem length_seed : r.seed.length = 16 := by
  rw [Run.seed, Run.pk, PublicKey.fromBytes, List.length_take, length_pkBytes]
  rfl

theorem length_pkRoot : r.pk.root.length = 16 := by
  show ((pkBytes r.w).drop 16).length = 16
  rw [List.length_drop, length_pkBytes]

/-- Layer `l`'s path has `heightOf l` nodes. -/
theorem length_path {l : Nat} (hl : l < 3) : (r.sig.path l).length = heightOf l := by
  rw [Signature.path, List.length_take, List.length_drop, sig_eq, SigMem.length_paths]
  have := pathStart_lt hl
  unfold pathStart heightOf at *
  omega

theorem sibling_eq {l z : Nat} (hz : z < heightOf l) :
    r.sibling l z = r.sig.paths.getD (pathStart l + z) [] :=
  SigMem.path_getD r.w hz

theorem length_sibling {l z : Nat} (hl : l < 3) (hz : z < heightOf l) :
    (r.sibling l z).length = 16 := by
  rw [sibling_eq r hz]
  have hlt : pathStart l + z < (sigOf r.w).paths.length := by
    rw [SigMem.length_paths]
    have := pathStart_lt hl
    omega
  apply SigMem.length_node r.w
  rw [sig_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.getElem_mem _

theorem length_foldUpTo (l : Nat) (e : List (List UInt8)) (z : Nat) :
    (r.foldUpTo l e z).length = 16 := by
  cases z with
  | zero => exact length_th _ _ _
  | succ z =>
    simp only [Run.foldUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact length_th _ _ _

theorem length_nodeAdrs (l z : Nat) : (r.nodeAdrs l z).length = 32 := by
  rw [Run.nodeAdrs, nodeAdrs_eq]; simp [be32, be64]

theorem length_children {l z : Nat} {cur : List UInt8} (hl : l < 3) (hz : z < heightOf l)
    (hc : cur.length = 16) : (r.children l cur z).length = 32 := by
  unfold Run.children; split <;> simp [hc, length_sibling r hl hz]

theorem length_nodeIn {l z : Nat} {e : List (List UInt8)} (hl : l < 3) (hz : z < heightOf l) :
    (r.nodeIn l e z).length = 80 := by
  rw [Run.nodeIn, List.length_append, List.length_append, length_seed, length_nodeAdrs,
    length_children r hl hz (length_foldUpTo r l e z)]

/-! ## The fold -/

/-- The fold's last step. -/
theorem foldUpTo_succ (l : Nat) (e : List (List UInt8)) (z : Nat) :
    r.foldUpTo l e (z + 1) = r.foldStep l (r.foldUpTo l e z) z := by
  simp only [Run.foldUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Layer `l`'s next message** is the fold after `heightOf l` steps. -/
theorem layerRoot_eq {l : Nat} (hl : l < 3) (e : List (List UInt8)) :
    r.layerRoot l e = r.foldUpTo l e (heightOf l) := by
  have hlen : (r.sig.path l).length = heightOf l := length_path r hl
  unfold Run.layerRoot treeFold pathFold
  rw [hlen]
  rfl

end

end Tree

end NativeRustcX64.SphincsVerifyProof
