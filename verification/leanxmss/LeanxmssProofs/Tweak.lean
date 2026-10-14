import LeanxmssProofs.Prelude

/-!
# Tweaks

The guest's two tweak words are the specification's sixteen tweak bytes.
-/

open Aeneas Aeneas.Std Result WP
open EthCryptographySpecs.Xmss EthCryptographySpecs.Xmss.Constants

namespace leanxmss.Proofs

open Bytes

/-- A guest `u32` as the specification's. -/
def u32 (x : Std.U32) : UInt32 := UInt32.ofBitVec x.bv

@[simp] theorem u32_toNat (x : Std.U32) : (u32 x).toNat = x.val := rfl

theorem epoch_eq_u32 (x : Std.U32) : Statement.epoch x = u32 x := rfl

/-- The guest's byte for a tweak type. -/
def tyByte (t : TweakType) : Std.U8 := ⟨t.toByte.toBitVec⟩

@[simp] theorem tyByte_val (t : TweakType) : (tyByte t).val = t.toByte.toNat := rfl

theorem wordBytes_toList (w : UInt32) : (Blake2s.Internal.wordBytes w).toList = le 4 w.toNat := by
  have h := w.toNat_lt
  simp only [Blake2s.Internal.wordBytes, Vector.toList_ofFn, List.ofFn_succ, List.ofFn_zero, le]
  simp only [List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toNat_inj.mp
    simp [UInt32.toNat_shiftRight, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow]
    try omega

theorem makeTweak_toList (t : TweakType) (pos idx : UInt32) :
    (makeTweak t pos idx).toList = [EthCryptographySpecs.Xmss.PROTOCOL_DOMAIN_SEP, t.toByte, 0, 0] ++
      (Blake2s.Internal.wordBytes pos).toList ++ [0, 0, 0, 0] ++ (Blake2s.Internal.wordBytes idx).toList := by
  show Vector.toList (α := UInt8) (n := 4 + 4 + 4 + 4)
    (#v[EthCryptographySpecs.Xmss.PROTOCOL_DOMAIN_SEP, t.toByte, 0, 0] ++ Blake2s.Internal.wordBytes pos ++
      #v[0, 0, 0, 0] ++ Blake2s.Internal.wordBytes idx) = _
  simp only [Vector.toList_append]
  rfl

/-- The first tweak word: domain separator 0, the type, two zero bytes, the position. -/
def tweakWord0 (ty : Std.U8) (pos : Std.U32) : Std.U64 := ⟨BitVec.ofNat 64 (ty.val * 256 + pos.val * 2 ^ 32)⟩

/-- The second tweak word: four zero bytes, the index. -/
def tweakWord1 (idx : Std.U32) : Std.U64 := ⟨BitVec.ofNat 64 (idx.val * 2 ^ 32)⟩

theorem tweakWord0_val (ty : Std.U8) (pos : Std.U32) : (tweakWord0 ty pos).val = ty.val * 256 + pos.val * 2 ^ 32 := by
  have h1 : ty.val < 256 := by have := ty.hBounds; simpa using this
  have h2 : pos.val < 2^32 := by have := pos.hBounds; simpa using this
  show (BitVec.ofNat 64 (ty.val * 256 + pos.val * 2 ^ 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem tweakWord1_val (idx : Std.U32) : (tweakWord1 idx).val = idx.val * 2 ^ 32 := by
  have h2 : idx.val < 2^32 := by have := idx.hBounds; simpa using this
  show (BitVec.ofNat 64 (idx.val * 2 ^ 32)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem tweak_ok (ty : Std.U8) (pos idx : Std.U32) :
    leanxmss.tweak ty pos idx = ok (Std.Array.make 2#usize [tweakWord0 ty pos, tweakWord1 idx]) := by
  apply eq_ok_of_spec
  unfold leanxmss.tweak
  simp only [lift]
  step*
  have h1 : ty.val < 256 := by have := ty.hBounds; simpa using this
  have h2 : pos.val < 2^32 := by have := pos.hBounds; simpa using this
  have h3 : idx.val < 2^32 := by have := idx.hBounds; simpa using this
  apply Std.Array.ext
  simp only [Std.Array.make_val, List.cons.injEq, and_true]
  have v0 := tweakWord0_val ty pos
  constructor
  · apply UScalar.eq_of_val_eq
    simp only [UScalar.val_or, i2_post, i5_post, core.convert.num.FromU64U8.from_val_eq,
      core.convert.num.FromU64U32.from_val_eq, leanxmss.PROTOCOL_DOMAIN_SEP]
    rw [v0]
    have e1 : (0#u8 : Std.U8).val = 0 := rfl
    rw [e1, Nat.zero_or, Nat.or_comm]
    simp only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.numBits]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
    omega
  · apply UScalar.eq_of_val_eq
    rw [i8_post, tweakWord1_val, core.convert.num.FromU64U32.from_val_eq]
    simp only [Nat.shiftLeft_eq, U64.size, U64.numBits, UScalarTy.numBits]
    rw [Nat.mod_eq_of_lt (by omega)]

theorem tweak_bytes (t : TweakType) (pos idx : Std.U32) :
    ofWords [tweakWord0 (tyByte t) pos, tweakWord1 idx] = (makeTweak t (u32 pos) (u32 idx)).toList := by
  have hp : pos.val < 2^32 := by have := pos.hBounds; simpa using this
  have hi : idx.val < 2^32 := by have := idx.hBounds; simpa using this
  have hb := t.toByte.toNat_lt
  rw [makeTweak_toList, wordBytes_toList, wordBytes_toList, u32_toNat, u32_toNat]
  simp only [ofWords_cons, ofWords_nil, List.append_nil, tweakWord0_val, tweakWord1_val, tyByte_val]
  simp only [le, EthCryptographySpecs.Xmss.PROTOCOL_DOMAIN_SEP, List.cons_append, List.nil_append,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply UInt8.toNat_inj.mp
    simp only [UInt8.toNat_ofNat']
    try simp
    try omega

/-- The tweak the guest computes for a type, a position and an index is the specification's. -/
theorem tweak_spec (t : TweakType) (pos idx : Std.U32) :
    ∃ w, leanxmss.tweak (tyByte t) pos idx = ok w ∧ ofWords w.val = (makeTweak t (u32 pos) (u32 idx)).toList :=
  ⟨_, tweak_ok _ _ _, by rw [Std.Array.make_val, tweak_bytes]⟩

end leanxmss.Proofs
