import LeanXmssProofs.Common

/-!
# `hash.rs`: the address and the tweakable hash

`address` lays out the statement's `addressBytes` (`address_spec`), and `th` is the truncated
Keccak-256 of `P ‖ A ‖ M`, the statement's `LeanXmss.th` (`th_spec`, from `HasherSpec`).
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

/-! ## The library models, as triples for `hax_mvcgen` -/

theorem u32_to_le_bytes_triple (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄ core.num.U32.to_le_bytes x
    ⦃ ⇓ a => ⌜ a.val = (List.range 4).map (leByte x.val) ⌝ ⦄ :=
  triple_of_exists (u32_to_le_bytes x)

/-- `&a[..e]`. -/
theorem array_index_range_to {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ∃ s, core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e } = ok s ∧ s.val = a.val.take e.val := by
  simp [core.Array.Insts.CoreOpsIndexIndex.index, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, core.Slice.Insts.CoreOpsIndexIndex.index,
    core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get,
    rust_primitives.slice.slice_length, rust_primitives.slice.slice_slice, Slice.subslice, he]

@[spec]
theorem array_index_range_to_triple {α : Type} {N : Std.Usize} (a : Array α N) (e : Std.Usize)
    (he : e.val ≤ N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
        (core.ops.range.RangeToUsize.Insts.CoreSliceIndexSliceIndexSliceSlice α))
      a { «end» := e }
    ⦃ ⇓ r => ⌜ r.val = a.val.take e.val ⌝ ⦄ :=
  triple_of_exists (array_index_range_to a e he)

/-! ## The address -/

/-- Byte 7 of an address: the type, and the step above it. -/
def tagByte (tw : hash.Tweak) : Std.U8 := ⟨tw.t.bv ||| tw.step.bv <<< 5⟩

/-- `address`, byte by byte: `lo`'s four bytes, the low three of `hi`, the type and step, eight
zero bytes. -/
theorem address_val (tw : hash.Tweak) :
    ⦃ ⌜ True ⌝ ⦄ hash.address tw
    ⦃ ⇓ r => ⌜ r.val = (List.range 4).map (leByte tw.lo.val) ++
       ((List.range 3).map (leByte tw.hi.val)) ++ [tagByte tw] ++ List.replicate 8 0#u8 ⌝ ⦄ := by
  hax_mvcgen [hash.address, u32_to_le_bytes_triple]
  case vc2.h =>
    rename_i r0 h0 r hr a ha
    show r.1.val.length = a.to_slice.val.length
    rw [hr.1, h0]; simp
  case vc6.h =>
    rename_i r0 h0 r hr a ha s out1 hs r' hr' a' ha' s' hs'
    show r'.1.val.length = s'.val.length
    rw [hr'.1, hs', ha']; simp [List.slice, out1]
  case vc7.h_ok =>
    rename_i r0 h0 r hr a ha s out1 hs r' hr' a' ha' s' hs' s5 hs5 i hi1 hi2 hi3 out2
    have hi : (tw.t ||| i) = tagByte tw := by
      rw [UScalar.eq_equiv_bv_eq]
      simp only [tagByte, UScalar.bv_or, hi2]
      rfl
    rw [hi]
    simp [out2, out1, hr'.2, hr.2, hs, hs5, h0, ha, hs', ha']
    rfl
  case vc8.h_fail =>
    rename_i r0 h0 r hr a ha s out1 hs r' hr' a' ha' s' hs' s5 hs5 i hi1 hi2 hi3 out2 hlen
    have : out2.length = 16 := by simp [out2]
    scalar_tac

/-- The type and step byte is the statement's, for a type below 32. For a larger type the Rust
byte ORs the type's high bits into the step's, where the statement keeps five bits of it. -/
theorem tagByte_eq (tw : hash.Tweak) (ht : tw.t.val < 32) :
    [b8 (tagByte tw)] =
      littleEndianBytes 1 (BitVec.ofNat 3 tw.step.val ++ BitVec.ofNat 5 tw.t.val) := by
  have h : (tagByte tw).bv = (BitVec.ofNat 3 tw.step.val ++ BitVec.ofNat 5 tw.t.val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    show (tw.t.bv ||| tw.step.bv <<< 5).getLsbD i = _
    have htb : ∀ j, tw.t.bv.getLsbD j = tw.t.val.testBit j := fun _ => rfl
    have hsb : ∀ j, tw.step.bv.getLsbD j = tw.step.val.testBit j := fun _ => rfl
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append,
      BitVec.getLsbD_ofNat, htb, hsb]
    by_cases h5 : i < 5
    · simp [h5, hi]
    · have h32 : (2 : ℕ) ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
      have ht0 : tw.t.val.testBit i = false := Nat.testBit_lt_two_pow (by omega)
      simp [h5, hi, ht0]
      omega
  simp only [littleEndianBytes, List.ofFn_succ, List.ofFn_zero, b8, h]
  congr 2
  bv_bits

/-- **`address`** lays out the statement's `addressBytes`. No bound is asked of `step` or `hi`:
the Rust keeps three bits of one and three bytes of the other, as the statement's fields do. -/
theorem address_spec (tw : hash.Tweak) (ht : tw.t.val < 32) :
    ∃ a, hash.address tw = ok a ∧
      bytes a.val = addressBytes (tweakFields tw.t.val tw.step.val tw.hi.val tw.lo.val) := by
  obtain ⟨a, ha, hv⟩ := exists_of_triple (address_val tw)
  refine ⟨a, ha, ?_⟩
  rw [hv, bytes_append, bytes_append, bytes_append, bytes_leByte, bytes_leByte, bytes_replicate_zero]
  simp only [addressBytes, tweakFields]
  rw [← tagByte_eq tw ht]
  rfl

/-! ## The tweakable hash -/

/-- The statement's fields of a Rust address. -/
def toFields (tw : hash.Tweak) : TweakFields :=
  tweakFields tw.t.val tw.step.val tw.hi.val tw.lo.val

section
variable {π : KeccakState → KeccakState}

/-- `hasher`: a hasher that has absorbed `P ‖ A`. -/
theorem hasher_absorbed (H : HasherSpec π) (pp : Array Std.U8 16#usize) (tw : hash.Tweak)
    (ht : tw.t.val < 32) :
    ∃ h, hash.hasher pp tw = ok h ∧
      H.Absorbed h (bytes pp.val ++ addressBytes (toFields tw)) := by
  obtain ⟨a, ha, hA⟩ := address_spec tw ht
  obtain ⟨h0, hnew, habs0⟩ := H.new
  obtain ⟨h1, b1, hu1, habs1, hb1⟩ := H.update h0 [] pp.to_slice habs0
  obtain ⟨h2, b2, hu2, habs2, hb2⟩ := H.update h1 _ a.to_slice habs1
  refine ⟨h2, ?_, by rw [toFields, ← hA]; simpa [Array.to_slice] using habs2⟩
  simp [hash.hasher, ha, keccak256.prefixed_hasher, core.array.Array.as_slice,
    rust_primitives.slice.array_as_slice, hnew, hu1, hu2, hb1, hb2]

/-- The truncated hash of what a hasher has absorbed, after `P ‖ A`, as the statement's `th`. -/
theorem toDigest_th (pp : Array Std.U8 16#usize) (F : TweakFields) (payload : List UInt8)
    (d : Array Std.U8 32#usize) (a : Array Std.U8 16#usize)
    (hd : bytes d.val = hashBytes π (bytes pp.val ++ addressBytes F ++ payload))
    (ha : a.val = d.val.take 16) :
    toDigest a = Id.run (LeanXmss.th (inId π) (toDigest pp) F payload) := by
  rw [toDigest_truncate _ d a hd ha]
  simp only [LeanXmss.th, thInput, hasherInput, littleEndianBytes_toDigest, bind_pure_comp,
    Id.run_map]

/-- **`th`**: the truncated Keccak-256 of `P ‖ A ‖ M`. -/
theorem th_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (tw : hash.Tweak)
    (payload : Slice Std.U8) (ht : tw.t.val < 32) :
    ∃ d, hash.th pp tw payload = ok d ∧
      toDigest d = Id.run (LeanXmss.th (inId π) (toDigest pp) (toFields tw) (bytes payload.val)) := by
  obtain ⟨h, hh, habs⟩ := hasher_absorbed H pp tw ht
  obtain ⟨h1, b1, hu1, habs1, -⟩ := H.update h _ payload habs
  obtain ⟨d, hf, hd⟩ := H.finalize h1 _ habs1
  obtain ⟨r, hr, hrv⟩ := truncate_eq d
  refine ⟨r, ?_, toDigest_th pp _ _ d r hd hrv⟩
  simp [hash.th, hh, hu1, hf, hr]

/-- **`th_digests`**: `th` of the digests' bytes, one after the other. -/
theorem th_digests_spec (H : HasherSpec π) (pp : Array Std.U8 16#usize) (tw : hash.Tweak)
    (values : Slice (Array Std.U8 16#usize)) (ht : tw.t.val < 32)
    (hlen : 16 * values.length ≤ Usize.max) :
    ∃ d, hash.th_digests pp tw values = ok d ∧
      toDigest d = Id.run (LeanXmss.th (inId π) (toDigest pp) (toFields tw)
        (bytes ((values.val.map Array.val).flatten))) := by
  have hflat : ((values.val.map Array.val).flatten).length ≤ Usize.max := by
    rw [flat_length]; exact hlen
  obtain ⟨d, hd, hval⟩ := th_spec H pp tw (Slice.from _ hflat) ht
  refine ⟨d, ?_, ?_⟩
  · unfold hash.th_digests core.slice.SliceArray.as_flattened
    simp only [hflat, ↓reduceDIte, Aeneas.Std.bind_ok]
    exact hd
  · rw [hval, slice_from_val]

end

end LeanXmssProofs
