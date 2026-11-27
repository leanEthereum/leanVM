import LeanXmssProofs.Defs
import Keccak256Proofs.Bytes
import Keccak256Proofs.Path

/-!
# What the proofs share

The library models only this crate's extraction calls, as equations: `u32::to_le_bytes` and
`u128::to_le_bytes`, closures over the byte index, as the statement's `littleEndianBytes`. What
leanSPHINCS's proofs use too is in `Keccak256Proofs` (`../keccak256`).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM Std.Do
open HashSig HashSig.OverPermutation LeanXmss
open LeanVM.Semantics (KeccakState)
open LeanVM.Protocol.KeccakHash (digestBytes keccak256With)
open lean_xmss
open Keccak256Proofs

namespace LeanXmssProofs

/-! ## Little-endian bytes -/

/-- Byte `n` of a number, least significant first. -/
def leByte (v : ℕ) (n : ℕ) : Std.U8 := ⟨BitVec.ofNat 8 (v >>> (8 * n))⟩

theorem leByte_val (v n : ℕ) : (leByte v n).val = v / 2 ^ (8 * n) % 256 := by
  simp only [leByte, UScalar.val, Nat.shiftRight_eq_div_pow]
  rfl

/-- The closure of `u32::to_le_bytes`: byte `n`, and itself. -/
theorem u32_to_le_bytes_closure (x : Std.U32) (n : Std.Usize) (hn : n.val < 4) :
    core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n =
      ok (leByte x.val n.val, x) := by
  have h : core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n
      ⦃ r => r = (leByte x.val n.val, x) ⦄ := by
    unfold core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    step*
    have hiv : i.val = n.val := by
      rw [i_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by decide))
    have h4 : i4 = leByte x.val n.val := by
      rw [UScalar.eq_equiv, leByte_val, i4_post, UScalar.cast_val_eq, i3_post, i2_post, i1_post,
        hiv, Nat.mod_eq_of_lt (by omega : 8 * n.val < 32), Nat.shiftRight_eq_div_pow]
      rfl
    rw [h4]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- The closure of `u128::to_le_bytes`: byte `n`, and itself. -/
theorem u128_to_le_bytes_closure (x : Std.U128) (n : Std.Usize) (hn : n.val < 16) :
    core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n =
      ok (leByte x.val n.val, x) := by
  have h : core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut x n
      ⦃ r => r = (leByte x.val n.val, x) ⦄ := by
    unfold core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut
    step*
    have hiv : i.val = n.val := by
      rw [i_post, UScalar.cast_val_eq]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (by decide))
    have h4 : i4 = leByte x.val n.val := by
      rw [UScalar.eq_equiv, leByte_val, i4_post, UScalar.cast_val_eq, i3_post, i2_post, i1_post,
        hiv, Nat.mod_eq_of_lt (by omega : 8 * n.val < 128), Nat.shiftRight_eq_div_pow]
      rfl
    rw [h4]
  obtain ⟨r, hr, rfl⟩ := WP.spec_imp_exists h
  exact hr

/-- The first `n` bytes of a number, least significant first, are the statement's
`littleEndianBytes n` of its low `8 n` bits. -/
theorem bytes_leByte (n v : ℕ) :
    bytes ((List.range n).map (leByte v)) = littleEndianBytes n (BitVec.ofNat (8 * n) v) := by
  apply List.ext_getElem
  · simp [littleEndianBytes]
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp only [bytes, List.getElem_map, List.getElem_range, littleEndianBytes, List.getElem_ofFn]
    apply UInt8.toNat_inj.mp
    have hl : (b8 (leByte v i)).toNat = v / 2 ^ (8 * i) % 256 := by
      rw [← leByte_val]; rfl
    rw [hl]
    simp only [UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ (8 * n) = 2 ^ (8 * i) * (256 * 2 ^ (8 * (n - i - 1))) := by
      rw [show (256 : ℕ) = 2 ^ 8 by rfl, ← Nat.pow_add, ← Nat.pow_add]
      congr 1; omega
    rw [hpow, Nat.mod_mul_right_div_self, Nat.mod_mul_right_mod]

/-- `u32::to_le_bytes`: its four bytes, least significant first. -/
theorem u32_to_le_bytes (x : Std.U32) :
    ∃ a, core.num.U32.to_le_bytes x = ok a ∧ a.val = (List.range 4).map (leByte x.val) :=
  array_from_fn_eq 4#usize
    core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 x (leByte x.val)
    (fun i hi ↦ u32_to_le_bytes_closure x i hi)

/-- `u128::to_le_bytes`: the statement's `littleEndianBytes 16`. -/
theorem u128_to_le_bytes (x : Std.U128) :
    ∃ a, core.num.U128.to_le_bytes x = ok a ∧
      bytes a.val = littleEndianBytes 16 (BitVec.ofNat 128 x.val) := by
  obtain ⟨a, ha, hav⟩ := array_from_fn_eq 16#usize
    core.num.U128.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8 x (leByte x.val)
    (fun i hi ↦ u128_to_le_bytes_closure x i hi)
  exact ⟨a, ha, by rw [hav]; exact bytes_leByte 16 x.val⟩

end LeanXmssProofs
