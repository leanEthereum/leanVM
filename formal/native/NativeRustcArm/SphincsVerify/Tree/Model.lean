module

public import NativeRustcArm.SphincsVerify.Basic
public import NativeRustc.Sphincs.Verify

/-!
# The tree region's model facts

Layer `l`'s next message as the machine computes it: the fold's step at height `z`
(`Run.foldStep`: the node above of the current value and the sibling, bit `z` of the key's leaf
saying which is left) and the fold after `z` steps (`Run.foldUpTo`, `Run.foldUpTo_succ`), which
after `layerHeights[l]` steps is `Run.layerRoot` (`Run.layerRoot_eq`). The parsed signature's
paths: 26 nodes of 16 bytes (`length_paths`, `length_of_mem_paths`), layer `l`'s from node
`pathStart l` (`path_getD`, `length_path`), in memory at `4708 + 16 i` (`Run.bytesAt_node`).
The addresses' bytes: the one-time key's (`keyAdrs_one`) and a node's (`nodeAdrs_eq`).
-/

namespace NativeRustcArm.SphincsVerifyProof

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

/-- **The fold's step** at height `z` from the current value `cur`. -/
def foldStep (l : Nat) (cur : List UInt8) (z : Nat) : List UInt8 :=
  node r.seed (r.key l) (z + 1) ((r.key l).leaf.toNat >>> (z + 1))
    (if (r.key l).leaf.toNat >>> z &&& 1 = 0 then cur ++ r.sibling l z else r.sibling l z ++ cur)

/-- **The fold after `z` steps** from the one-time leaf of the chain ends `e`. -/
def foldUpTo (l : Nat) (e : List (List UInt8)) (z : Nat) : List UInt8 :=
  (List.range z).foldl (r.foldStep l) (wotsLeafHash r.seed (r.key l) e)

end Run

end

namespace Tree

public section

/-! ## Lists -/

theorem length_slice {b : List UInt8} {off len : Nat} (h : off + len ≤ b.length) :
    (slice b off len).length = len := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem length_flatten_const {L : List (List UInt8)} {k : Nat} (h : ∀ x ∈ L, x.length = k) :
    L.flatten.length = k * L.length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatten_cons, List.length_append, h x List.mem_cons_self,
      ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy), List.length_cons]
    rw [Nat.mul_succ]
    omega

/-! ## The signature's bytes and its paths -/

/-- The 26 nodes of the paths. -/
theorem length_paths (sig : List UInt8) : (Signature.fromBytes sig).paths.length = 26 := by
  simp [Signature.fromBytes, layerHeights, List.flatMap, List.range_succ]

/-- Each node is 16 bytes. -/
theorem length_of_mem_paths {sig : List UInt8} (hsig : sig.length = 7740) {x : List UInt8}
    (hx : x ∈ (Signature.fromBytes sig).paths) : x.length = 16 := by
  simp only [Signature.fromBytes, List.mem_flatMap, List.mem_map, List.mem_range] at hx
  obtain ⟨l, hl, z, hz, rfl⟩ := hx
  apply length_slice
  rw [hsig]
  interval_cases l <;> simp [sigLayerOff, layerHeights] at hz ⊢ <;> omega

/-- The FORS openings are `24 · 176` bytes. -/
theorem length_forsMem {sig : List UInt8} (hsig : sig.length = 7740) :
    ((Signature.fromBytes sig).fors.map openingMem).flatten.length = 4224 := by
  rw [length_flatten_const (k := 176)]
  · simp [Signature.fromBytes]
  intro x hx
  simp only [Signature.fromBytes, List.map_map, List.mem_map, List.mem_range,
    Function.comp_def] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  rw [openingMem, List.length_append, length_flatten_const (k := 16), length_slice]
  · simp
  · rw [hsig]; omega
  intro y hy
  simp only [List.mem_map, List.mem_range] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  apply length_slice
  rw [hsig]
  omega

theorem pathStart_lt {l : Nat} (hl : l < 3) : pathStart l + heightOf l ≤ 26 := by
  interval_cases l <;> decide

/-- Layer `l`'s path has `heightOf l` nodes. -/
theorem length_path (sig : List UInt8) {l : Nat} (hl : l < 3) :
    ((Signature.fromBytes sig).path l).length = heightOf l := by
  rw [Signature.path, List.length_take, List.length_drop, length_paths]
  have := pathStart_lt hl
  unfold pathStart heightOf at *
  omega

/-- Node `z` of layer `l`'s path is node `pathStart l + z` of the paths. -/
theorem path_getD (sig : List UInt8) {l z : Nat} (hz : z < heightOf l) :
    ((Signature.fromBytes sig).path l).getD z [] =
      (Signature.fromBytes sig).paths.getD (pathStart l + z) [] := by
  rw [Signature.path, List.getD_eq_getElem?_getD,
    List.getElem?_take_of_lt (show z < layerHeights.getD l 0 from hz),
    List.getElem?_drop, List.getD_eq_getElem?_getD]
  rfl

end

/-! ## Bytes in memory -/

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


theorem addr_add' (b : BitVec 64) (o i : Nat) :
    b + BitVec.ofNat 64 o + BitVec.ofNat 64 i = b + BitVec.ofNat 64 (o + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem bytesAt_append_left {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (h : BytesAt d a (p ++ q)) : BytesAt d a p := fun i hi ↦ by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem bytesAt_append_right {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (h : BytesAt d a (p ++ q)) : BytesAt d (a + BitVec.ofNat 64 p.length) q := fun i hi ↦ by
  rw [addr_add', h (p.length + i) (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem bytesAt_append {d : DataMem} {a : BitVec 64} {p q : List UInt8}
    (hp : BytesAt d a p) (hq : BytesAt d (a + BitVec.ofNat 64 p.length) q) :
    BytesAt d a (p ++ q) := fun i hi ↦ by
  by_cases h : i < p.length
  · rw [hp i h, List.getElem_append_left h]
  · have := hq (i - p.length) (by simp at hi; omega)
    rw [addr_add', show p.length + (i - p.length) = i by omega] at this
    rw [this, List.getElem_append_right (by omega)]

/-- Element `i` of a flattening of `k`-byte lists is at `a + k i`. -/
theorem bytesAt_flatten_getD {d : DataMem} {k : Nat} :
    ∀ {L : List (List UInt8)} {a : BitVec 64} {i : Nat}, BytesAt d a L.flatten →
      (∀ x ∈ L, x.length = k) → i < L.length → BytesAt d (a + BitVec.ofNat 64 (k * i)) (L.getD i [])
  | [], _, _, _, _, hi => absurd hi (by simp)
  | x :: L, a, i, h, hk, hi => by
    rw [List.flatten_cons] at h
    cases i with
    | zero =>
      simpa using bytesAt_append_left h
    | succ i =>
      have h' := bytesAt_flatten_getD (L := L) (i := i) (bytesAt_append_right h)
        (fun y hy ↦ hk y (List.mem_cons_of_mem _ hy)) (by simp at hi; omega)
      rw [addr_add', hk x List.mem_cons_self] at h'
      rw [List.getD_cons_succ, show k * (i + 1) = k + k * i by rw [Nat.mul_succ]; omega]
      exact h'

variable (r : Run)

theorem off_add (a b : Nat) : r.off a + BitVec.ofNat 64 b = r.off (a + b) := by
  rw [Run.off, addr_add']
  rfl

theorem sig_eq : r.sig = Signature.fromBytes r.sigBytes := rfl

/-- **Node `i` of the paths** is at `4708 + 16 i` in the frame. -/
theorem bytesAt_node {m : MachineData} (h : BytesAt m.dmem (r.off 484) (sigMem r.sig)) {i : Nat}
    (hi : i < 26) : BytesAt m.dmem (r.off (4708 + 16 * i)) (r.sig.paths.getD i []) := by
  have h1 := bytesAt_append_left (bytesAt_append_right h)
  rw [sig_eq r, length_forsMem r.hsig, off_add] at h1
  have := bytesAt_flatten_getD (k := 16) (i := i) h1 (fun x hx ↦ length_of_mem_paths r.hsig hx)
    (by rw [length_paths]; exact hi)
  rwa [off_add] at this

/-- **The sibling at height `z < heightOf l`** of layer `l`. -/
theorem bytesAt_sibling {m : MachineData} (h : BytesAt m.dmem (r.off 484) (sigMem r.sig))
    {l z : Nat} (hl : l < 3) (hz : z < heightOf l) :
    BytesAt m.dmem (r.off (4708 + 16 * (pathStart l + z))) (r.sibling l z) := by
  rw [Run.sibling, sig_eq r, path_getD _ hz]
  exact bytesAt_node r h (by have := pathStart_lt hl; omega)

theorem length_sibling {l z : Nat} (hl : l < 3) (hz : z < heightOf l) :
    (r.sibling l z).length = 16 := by
  rw [Run.sibling, sig_eq r, path_getD _ hz]
  apply length_of_mem_paths r.hsig
  have hlt : pathStart l + z < (Signature.fromBytes r.sigBytes).paths.length := by
    rw [length_paths]
    have := pathStart_lt hl
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  exact List.getElem_mem _

/-- The fold's last step. -/
theorem foldUpTo_succ (l : Nat) (e : List (List UInt8)) (z : Nat) :
    r.foldUpTo l e (z + 1) = r.foldStep l (r.foldUpTo l e z) z := by
  simp only [Run.foldUpTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **Layer `l`'s next message** is the fold after `heightOf l` steps. -/
theorem layerRoot_eq {l : Nat} (hl : l < 3) (e : List (List UInt8)) :
    r.layerRoot l e = r.foldUpTo l e (heightOf l) := by
  have hlen : (r.sig.path l).length = heightOf l := length_path r.sigBytes hl
  unfold Run.layerRoot treeFold pathFold
  rw [hlen]
  rfl

end

end Tree

end NativeRustcArm.SphincsVerifyProof
