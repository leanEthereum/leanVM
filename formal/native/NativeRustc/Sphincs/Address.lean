module

public import NativeRustc.Sphincs.Model
public import NativeRustc.Digest
public import Statement.LeanSphincs

/-!
# The address is FIPS 205's

`u32::to_be_bytes` and `u64::to_be_bytes` are `bigEndianBytes` (`be32_eq`, `be64_eq`); every
address the Rust code builds is `adrsBytes` of its eight words (`adrsNew_eq`, `withType_eq`, ...,
`OtsKey.adrs_eq`), which is the statement's `Address.toBytes` (`adrsBytes_eq`); the key of an
index is the statement's (`OtsKey.ofIndex_tree`, `OtsKey.ofIndex_leaf`).
-/

@[expose] public section

namespace NativeRustc.Sphincs

open _root_.Sphincs HashSig

/-! ## Big-endian bytes -/

/-- **`u32::to_be_bytes`** is `bigEndianBytes 4`. -/
theorem be32_eq (x : UInt32) : be32 x = bigEndianBytes 4 (BitVec.ofNat 32 x.toNat) := by
  have hx := x.toNat_lt
  apply List.ext_getElem (by simp [be32, bigEndianBytes])
  intro i h1 h2
  have hi : i < 4 := by simpa [be32] using h1
  apply UInt8.toNat_inj.mp
  interval_cases i <;>
    simp [be32, bigEndianBytes, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat,
      UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-- **`u64::to_be_bytes`** is `bigEndianBytes 8`. -/
theorem be64_eq (x : UInt64) : be64 x = bigEndianBytes 8 (BitVec.ofNat 64 x.toNat) := by
  have hx := x.toNat_lt
  apply List.ext_getElem (by simp [be64, bigEndianBytes])
  intro i h1 h2
  have hi : i < 8 := by simpa [be64] using h1
  apply UInt8.toNat_inj.mp
  interval_cases i <;>
    simp [be64, bigEndianBytes, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat,
      UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

/-! ## Addresses -/

/-- The 32 bytes of the address of the eight words: the layer, zero, the tree (two words), the
type, the key pair, the chain or tree height, the hash or tree index. -/
def adrsBytes (layer : UInt32) (tree : UInt64) (t kp ch h : UInt32) : List UInt8 :=
  be32 layer ++ (be32 0 ++ (be64 tree ++ (be32 t ++ (be32 kp ++ (be32 ch ++ be32 h)))))

theorem adrsNew_eq (layer : UInt32) (tree : UInt64) : adrsNew layer tree = adrsBytes layer tree 0 0 0 0 :=
  (rfl)

theorem withType_eq (layer : UInt32) (tree : UInt64) (t kp ch h t' : UInt32) :
    withType (adrsBytes layer tree t kp ch h) t' = adrsBytes layer tree t' 0 0 0 := (rfl)

theorem withKeyPair_eq (layer : UInt32) (tree : UInt64) (t kp ch h kp' : UInt32) :
    withKeyPair (adrsBytes layer tree t kp ch h) kp' = adrsBytes layer tree t kp' ch h := (rfl)

theorem withChain_eq (layer : UInt32) (tree : UInt64) (t kp ch h ch' : UInt32) :
    withChain (adrsBytes layer tree t kp ch h) ch' = adrsBytes layer tree t kp ch' h := (rfl)

theorem withTreeHeight_eq (layer : UInt32) (tree : UInt64) (t kp ch h ch' : UInt32) :
    withTreeHeight (adrsBytes layer tree t kp ch h) ch' = adrsBytes layer tree t kp ch' h := (rfl)

theorem withHash_eq (layer : UInt32) (tree : UInt64) (t kp ch h h' : UInt32) :
    withHash (adrsBytes layer tree t kp ch h) h' = adrsBytes layer tree t kp ch h' := (rfl)

theorem withTreeIndex_eq (layer : UInt32) (tree : UInt64) (t kp ch h h' : UInt32) :
    withTreeIndex (adrsBytes layer tree t kp ch h) h' = adrsBytes layer tree t kp ch h' := (rfl)

/-- A key's address of type `t`. -/
theorem OtsKey.adrs_eq (key : OtsKey) (t : UInt32) :
    key.adrs t = adrsBytes key.layer.toUInt32 key.tree t key.leaf 0 0 := (rfl)

/-- A key's tree's address. -/
theorem OtsKey.treeAdrs_eq (key : OtsKey) :
    key.treeAdrs = adrsBytes key.layer.toUInt32 key.tree 0 0 0 0 := (rfl)

/-- **The address's bytes are the statement's** for the words' numbers. -/
theorem adrsBytes_eq {layer : UInt32} {tree : UInt64} {t kp ch h : UInt32} {aty : AddressType}
    {layerN treeN kpN chN hN : Nat} (hl : layer.toNat = layerN) (htr : tree.toNat = treeN)
    (ht : t.toNat = aty.word) (hkp : kp.toNat = kpN) (hch : ch.toNat = chN) (hh : h.toNat = hN) :
    adrsBytes layer tree t kp ch h = (makeAddress layerN treeN aty kpN chN hN).toBytes := by
  subst hl htr hkp hch hh
  rw [adrsBytes, Address.toBytes, makeAddress, be32_eq, be32_eq, be64_eq, be32_eq, be32_eq, be32_eq,
    be32_eq, ht]
  simp only [List.append_assoc]
  rfl

end NativeRustc.Sphincs
