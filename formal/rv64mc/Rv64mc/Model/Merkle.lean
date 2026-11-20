module

public import Rv64mc.Model.Hash

/-!
# `merkle.rs` as the Rust computes it

Mirrors of `crates/verifier/src/merkle.rs`: `hash_pair`, `hash_leaf` and `MerklePath::root`, on
bytes as `Model.Hash` holds them (a `Digest` is its `32` bytes, a `K` word its `BitVec 64`).
`MerklePath::root` climbs the siblings bottom up, the bit `leaf_index >> level & 1` (the shift
masked to six bits) choosing the side; it is the statement's `climb` from the leaf's hash
(`rootRust_eq`), for paths of at most `64` siblings, the height the verifier allows
(`log2_strict` of a `u64`).
-/

namespace Rv64mc.Model

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
  LeanVM.Protocol.Compile

@[expose] public section

/-- A digest's `32` bytes, as the Rust holds them. -/
def digestBits (d : Digest) : List (BitVec 8) := byteBits (digestBytes d)

theorem toLeBytes_fromLeBytes {l : List (BitVec 8)} (h : l.length = 8) :
    toLeBytes (fromLeBytes l) = l := by
  match l, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    simp only [toLeBytes, fromLeBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
      List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, List.getD_cons_succ,
      List.getD_cons_zero, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      interval_cases i <;> simp

theorem digestBits_eq (d : Digest) :
    digestBits d = d.toList.flatMap fun w ↦ toLeBytes w.toBitVec := by
  rw [digestBits, digestBytes, byteBits, List.map_flatMap]
  exact List.flatMap_congr fun w _ ↦ (toLeBytes_toBitVec w).symm

/-- A digest's bytes determine it. -/
theorem digestBits_injective : Function.Injective digestBits := by
  intro a b h
  have h' := congrArg digestWordsRust h
  rw [digestBits, digestBits, digestWordsRust_digestBytes, digestWordsRust_digestBytes] at h'
  have hl : a.toList = b.toList :=
    List.map_injective_iff.mpr (fun x y hxy ↦ UInt64.toBitVec_inj.mp hxy) h'
  exact Vector.toList_inj.mp hl

/-- Every `[u8; 32]` is a digest's bytes. -/
theorem exists_digestBits {b : List (BitVec 8)} (h : b.length = 32) :
    ∃ d : Digest, digestBits d = b := by
  have hc : ∀ n, n ≤ 24 → ((b.drop n).take 8).length = 8 := fun n hn ↦ by simp [h]; omega
  have htd : ∀ n, (b.drop n).take 8 ++ b.drop (n + 8) = b.drop n := fun n ↦ by
    rw [← List.drop_drop, List.take_append_drop]
  refine ⟨#v[⟨fromLeBytes ((b.drop 0).take 8)⟩, ⟨fromLeBytes ((b.drop 8).take 8)⟩,
    ⟨fromLeBytes ((b.drop 16).take 8)⟩, ⟨fromLeBytes ((b.drop 24).take 8)⟩], ?_⟩
  rw [digestBits_eq]
  simp only [Vector.toList_mk, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [toLeBytes_fromLeBytes (hc 0 (by norm_num)), toLeBytes_fromLeBytes (hc 8 (by norm_num)),
    toLeBytes_fromLeBytes (hc 16 (by norm_num)), toLeBytes_fromLeBytes (hc 24 (by norm_num)),
    List.take_of_length_le (by simp [h] : (b.drop 24).length ≤ 8), ← List.append_assoc,
    show (24 : ℕ) = 16 + 8 from rfl, htd, List.append_assoc, show (16 : ℕ) = 8 + 8 from rfl, htd,
    List.drop_zero, List.take_append_drop]

/-- `hash_pair(left, right)`: Keccak-256 of the `64` bytes `left ‖ right` (both `[u8; 32]`). -/
def hashPairRust (left right : List (BitVec 8)) : List (BitVec 8) := keccakHashRust (left ++ right)

/-- `hash_leaf(image)`: Keccak-256 of the words' little-endian bytes. -/
def hashLeafRust (image : List (BitVec 64)) : List (BitVec 8) :=
  keccakHashRust (image.flatMap toLeBytes)

/-- `MerklePath`: the leaf's position, its words, and the siblings from the bottom level up. -/
structure MerklePathRust where
  /-- `leaf_index`. -/
  leafIndex : BitVec 64
  /-- `leaf`. -/
  leaf : List (BitVec 64)
  /-- `siblings`, bottom level first. -/
  siblings : List (List (BitVec 8))

/-- One level of `MerklePath::root`: `node` is the left child when the position's bit at `level`
is clear. -/
def rootStep (leafIndex : BitVec 64) (node : List (BitVec 8)) (sl : List (BitVec 8) × ℕ) :
    List (BitVec 8) :=
  if (leafIndex >>> (sl.2 % 64)) &&& 1#64 = 0#64 then hashPairRust node sl.1
  else hashPairRust sl.1 node

/-- `MerklePath::root`: the leaf's hash, then `for (level, sibling) in siblings.enumerate()`. -/
def MerklePathRust.root (p : MerklePathRust) : List (BitVec 8) :=
  p.siblings.zipIdx.foldl (rootStep p.leafIndex) (hashLeafRust p.leaf)

/-- The Rust path of a statement opening. -/
def MerklePathRust.ofOpening (o : Opening) : MerklePathRust :=
  ⟨BitVec.ofNat 64 o.leafIndex, o.leaf.map BF64.toBitVec, o.path.map digestBits⟩

/-- **`hash_pair` is Keccak-256 of the two digests' bytes.** -/
theorem hashPairRust_eq (a b : Digest) :
    hashPairRust (digestBits a) (digestBits b) =
      digestBits (keccak256With (m := Id) keccakF1600 (digestBytes a ++ digestBytes b)) := by
  rw [hashPairRust, digestBits, digestBits, byteBits, byteBits, ← List.map_append, ← byteBits,
    keccakHashRust_eq]
  rfl

/-- **`hash_leaf` is Keccak-256 of the leaf's bytes.** -/
theorem hashLeafRust_eq (leaf : List K) :
    hashLeafRust (leaf.map BF64.toBitVec) =
      digestBits (keccak256With (m := Id) keccakF1600 (leaf.flatMap K.toBytes)) := by
  have h : (leaf.map BF64.toBitVec).flatMap toLeBytes = byteBits (leaf.flatMap K.toBytes) := by
    induction leaf with
    | nil => rfl
    | cons a l ih =>
      simp only [List.map_cons, List.flatMap_cons, ih, byteBits, List.map_append]
      rw [show toLeBytes a.toBitVec = toLeBytes a.lane.toBitVec from rfl, toLeBytes_toBitVec]
      rfl
  rw [hashLeafRust, h, keccakHashRust_eq]
  rfl

private theorem bit_eq_zero_iff (idx : BitVec 64) {n : ℕ} (hn : n < 64) :
    (idx >>> (n % 64)) &&& 1#64 = 0#64 ↔ idx.toNat / 2 ^ n % 2 = 0 := by
  rw [Nat.mod_eq_of_lt hn, ← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

private theorem rootLoop_eq (idx : BitVec 64) : ∀ (ss : List Digest) (n : ℕ) (node : Digest),
    n + ss.length ≤ 64 →
    ((ss.map digestBits).zipIdx n).foldl (rootStep idx) (digestBits node) =
      digestBits (climb (m := Id) keccakF1600 node (idx.toNat / 2 ^ n) ss)
  | [], _, _, _ => rfl
  | s :: ss, n, node, h => by
    simp only [List.length_cons] at h
    rw [List.map_cons, List.zipIdx_cons, List.foldl_cons, climb]
    have hstep : rootStep idx (digestBits node) (digestBits s, n) =
        digestBits (if idx.toNat / 2 ^ n % 2 = 0 then
          keccak256With (m := Id) keccakF1600 (digestBytes node ++ digestBytes s)
          else keccak256With (m := Id) keccakF1600 (digestBytes s ++ digestBytes node)) := by
      rw [rootStep]
      dsimp only
      by_cases hb : idx.toNat / 2 ^ n % 2 = 0
      · rw [ite_eq_left ((bit_eq_zero_iff idx (by omega)).mpr hb), ite_eq_left hb,
          hashPairRust_eq]
      · rw [ite_eq_right (fun h' ↦ hb ((bit_eq_zero_iff idx (by omega)).mp h')),
          ite_eq_right hb, hashPairRust_eq]
    rw [hstep, rootLoop_eq idx ss (n + 1) _ (by omega), Nat.div_div_eq_div_mul, ← pow_succ]
    split <;> rfl

/-- **`MerklePath::root` is the statement's climb from the leaf's hash.** -/
theorem rootRust_eq (o : Opening) (hi : o.leafIndex < 2 ^ 64) (hp : o.path.length ≤ 64) :
    (MerklePathRust.ofOpening o).root =
      digestBits (climb (m := Id) keccakF1600
        (keccak256With (m := Id) keccakF1600 (o.leaf.flatMap K.toBytes)) o.leafIndex o.path) := by
  rw [MerklePathRust.root, MerklePathRust.ofOpening]
  dsimp only
  rw [hashLeafRust_eq, rootLoop_eq _ _ 0 _ (by omega), pow_zero, Nat.div_one,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

end

end Rv64mc.Model
