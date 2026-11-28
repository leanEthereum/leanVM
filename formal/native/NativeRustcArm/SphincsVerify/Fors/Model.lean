module

public import NativeRustcArm.SphincsVerify.SigMem
public import NativeRustcArm.SphincsVerify.InlineTh.Model
public import NativeRustc.Sphincs.Address

/-!
# The FORS region's model facts

FORS tree `c` as the machine computes it: its leaf index (`Run.leafOf`, below `2 ^ 10`:
`Run.leafOf_lt`), its opening (`Run.openingOf`), a node's step at height `z` (`Run.forsStep`: the
node above of the current value and the path's node, bit `z` of the leaf index saying which is
left) and the value after `z` steps (`Run.forsUpTo`, `Run.forsUpTo_succ`), which after 10 steps
is the tree's root (`Run.forsRoot_eq`). The bottom key's tree and leaf (`Run.key0_tree`,
`Run.key0_leaf`) and a FORS node's address (`forsNodeAdrs_eq`).
-/

namespace NativeRustcArm.SphincsVerifyProof

open NativeRustc NativeRustc.Keccak NativeRustc.Sphincs

@[expose] public section

namespace Run

variable (r : Run)

/-- Tree `c`'s leaf index. -/
def leafOf (c : Nat) : Nat := r.leaves.getD c 0

/-- Tree `c`'s opening. -/
def openingOf (c : Nat) : ForsTreeOpening := r.sig.fors.getD c ⟨[], []⟩

/-- **A node's step** of tree `c` at height `z` from the current value `cur`. -/
def forsStep (c : Nat) (cur : List UInt8) (z : Nat) : List UInt8 :=
  forsNode r.seed r.idx c (z + 1) (r.leafOf c >>> (z + 1))
    (if r.leafOf c >>> z &&& 1 = 0 then cur ++ (r.openingOf c).path.getD z []
      else (r.openingOf c).path.getD z [] ++ cur)

/-- **Tree `c`'s value after `z` steps** from its leaf. -/
def forsUpTo (c z : Nat) : List UInt8 :=
  (List.range z).foldl (r.forsStep c) (forsLeaf r.seed r.idx c (r.leafOf c) (r.openingOf c).secret)

/-- Tree `c`'s path node at height `z`. -/
def pathNode (c z : Nat) : List UInt8 := (r.openingOf c).path.getD z []

/-- The children at height `z`: the current value and the path's node, bit `z` of the leaf
index saying which is left. -/
def childrenOf (c z : Nat) : List UInt8 :=
  if r.leafOf c >>> z &&& 1 = 0 then r.forsUpTo c z ++ r.pathNode c z
  else r.pathNode c z ++ r.forsUpTo c z

/-- The address of the node above height `z`. -/
def nodeAdrsOf (c z : Nat) : List UInt8 := forsNodeAdrs r.idx c (z + 1) (r.leafOf c >>> (z + 1))

end Run

end

public section

namespace Run

variable (r : Run)

theorem forsUpTo_zero (c : Nat) :
    r.forsUpTo c 0 = forsLeaf r.seed r.idx c (r.leafOf c) (r.openingOf c).secret := rfl

/-- A step is `th` of the node's address and the children. -/
theorem forsStep_eq (c z : Nat) :
    r.forsStep c (r.forsUpTo c z) z = th r.seed (r.nodeAdrsOf c z) (r.childrenOf c z) := by
  unfold forsStep childrenOf nodeAdrsOf pathNode forsNode
  split <;> rfl

/-- One step more. -/
theorem forsUpTo_succ (c z : Nat) : r.forsUpTo c (z + 1) = r.forsStep c (r.forsUpTo c z) z := by
  simp only [forsUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem length_openingOf_path {c : Nat} (hc : c < 24) : (r.openingOf c).path.length = 10 := by
  rw [openingOf, r.fors_getD hc]
  simp

/-- **The root** is the value after the path's 10 steps. -/
theorem forsRoot_eq {c : Nat} (hc : c < 24) : r.forsRoot c = r.forsUpTo c 10 := by
  unfold forsRoot pathFold
  rw [show (r.sig.fors.getD c ⟨[], []⟩).path.length = 10 from r.length_openingOf_path hc]
  rfl

/-- A bit of the digest. -/
theorem digestBit_le (d : List UInt8) (p : Nat) : digestBit d p ≤ 1 := by
  unfold digestBit
  rw [UInt8.toNat_and]
  exact Nat.and_le_right

/-- Folding bits stays below `2 ^ (n + k)`. -/
theorem foldl_bits_lt (g : Nat → Nat) (hg : ∀ j, g j ≤ 1) :
    ∀ (l : List Nat) (v n : Nat), v < 2 ^ n →
      l.foldl (fun v j ↦ v <<< 1 ||| g j) v < 2 ^ (n + l.length)
  | [], v, n, h => by simpa using h
  | j :: l, v, n, h => by
    rw [List.foldl_cons, List.length_cons, show n + (l.length + 1) = (n + 1) + l.length by omega]
    apply foldl_bits_lt g hg l
    have hb : g j < 2 ^ (n + 1) := by
      have := hg j
      have : 1 < 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
      omega
    apply Nat.or_lt_two_pow _ hb
    rw [Nat.shiftLeft_eq, Nat.pow_succ]
    omega

/-- `digest_fields`' leaves are ten bits. -/
theorem digestFields_leaf_lt (d : List UInt8) {c : Nat} (hc : c < 24) :
    (digestFields d).2.getD c 0 < 1024 := by
  have h : (digestFields d).2 = (List.range 24).map fun c ↦
      (List.range 10).foldl (fun v j ↦ v <<< 1 ||| digestBit d (10 * c + j)) 0 := rfl
  rw [h, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc,
    Option.map_some, Option.getD_some]
  exact foldl_bits_lt (fun j ↦ digestBit d (10 * c + j)) (fun j ↦ digestBit_le d _) _ 0 0
    (by decide)

/-- **A leaf index is ten bits.** -/
theorem leafOf_lt {c : Nat} (hc : c < 24) : r.leafOf c < 1024 :=
  digestFields_leaf_lt _ hc

theorem idx_shift_zero : r.idx >>> ((layerHeights.take 0).sum).toUInt64 = r.idx :=
  UInt64.toBitVec_inj.mp (by simp)

/-- The bottom key's tree. -/
theorem key0_tree : (r.key 0).tree = r.idx >>> 8 := by
  show (r.idx >>> ((layerHeights.take 0).sum).toUInt64) >>> (layerHeights.getD 0 0).toUInt64 = _
  rw [idx_shift_zero]
  rfl

/-- The bottom key's leaf. -/
theorem key0_leaf : (r.key 0).leaf = (r.idx &&& 255).toUInt32 := by
  show ((r.idx >>> ((layerHeights.take 0).sum).toUInt64) &&&
    ((1 <<< (layerHeights.getD 0 0).toUInt64) - 1)).toUInt32 = _
  rw [idx_shift_zero]
  rfl

end Run

/-- **A FORS node's address**: layer 0, the bottom key's tree, type `FORS_TREE` (3), the key's
leaf, the height, the index across the trees. -/
theorem forsNodeAdrs_eq (idx : UInt64) (c z j : Nat) :
    forsNodeAdrs idx c z j = adrsBytes 0 (OtsKey.ofIndex 0 idx).tree 3 (OtsKey.ofIndex 0 idx).leaf
      z.toUInt32 ((c <<< (10 - z)) + j).toUInt32 := by
  rw [forsNodeAdrs, forsAdrs, OtsKey.adrs_eq, withTreeHeight_eq, withTreeIndex_eq]
  rfl

end

end NativeRustcArm.SphincsVerifyProof
