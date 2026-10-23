/-
  LeanVM.Guest.B1.Sig.Hashing

  The guest's `BLAKE2S` instructions as hashes of byte strings: one final block, two blocks, and the
  compile-time words they read (the IV, the metadata cells, small integers).
-/

module

public import LeanVM.Guest.B1.Sig.Template
public import LeanVM.Guest.B1.Sig.Bytes

/-!
# Compressions as hashes

`hb bs` is BLAKE2s of `bs` as its two output cells, `hcell cs` the hash of the cells' bytes.
`compress_final_iff` reads one compression under the IV with a final metadata word as `hb` of the
block's bytes, `compress_two_iff` two compressions in sequence, the first non-final.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Value

@[expose] public section

/-- BLAKE2s of bytes, as its two output cells. -/
def hb (bs : List UInt8) : E × E := digestScalars (blake2sBytes bs)

/-- BLAKE2s over the bytes of cells. -/
def hcell (cs : List E) : E × E := hb (cs.flatMap cellBytes)

/-! ## Compile-time words -/

theorem ivCells_eq_iv : Value.ivCells = (iv0, iv1) := by
  rw [ivCells_eq]
  simp only [iv0, iv1, word, eOfNat192, Prod.mk.injEq, ofLimbs_inj]
  decide

theorem mdw_eq (c : Nat) (f : Bool) : mdw c f = metadataCell c f := by
  cases f <;> rfl

theorem word_eq_eOfNat (n : Nat) : word n 0 0 = eOfNat n := by
  rw [eOfNat_eq_ofLimbs]; rfl

theorem isCanonical128_eOfNat (n : Nat) : IsCanonical128 (eOfNat n) := (eOfNat_isInK n).2

theorem isCanonical128_word (a b : Nat) : IsCanonical128 (word a b 0) := rfl

theorem isCanonical128_zero : IsCanonical128 (0 : E) := by
  rw [← eOfNat_zero]; exact isCanonical128_eOfNat 0

theorem isCanonical128_hb (bs : List UInt8) : IsCanonical128 (hb bs).1 ∧ IsCanonical128 (hb bs).2 :=
  isCanonical128_digestScalars _

theorem isCanonical128_add {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    IsCanonical128 (a + b) := by
  rw [eq_ofLimbs_of_canonical ha, eq_ofLimbs_of_canonical hb, ofLimbs_add]
  show (0 : K) + 0 = 0
  simp

/-! ## One and two blocks -/

theorem blake2sBytes_short {r : List UInt8} (hlen : r.length ≤ 64) :
    blake2sBytes r = absorb paramIv 0 0 r := by
  rw [blake2sBytes, show (r.length - 1) / 64 = 0 by omega]

/-- **One final compression under the IV**: the hash of the block's data bytes `r`, the rest of the
block zero. -/
theorem compress_final_iff {m : Fin 4 → E} {o0 o1 : E} {r : List UInt8}
    (hr : blockBytes m = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64) :
    CompressCells m iv0 iv1 o0 o1 (mdw r.length true) ↔
      (∀ i, IsCanonical128 (m i)) ∧ (o0, o1) = hb r := by
  have hiv : (iv0, iv1) = digestScalars paramIv := ivCells_eq_iv.symm
  have hiv0 : iv0 = (digestScalars paramIv).1 := congrArg Prod.fst hiv
  have hiv1 : iv1 = (digestScalars paramIv).2 := congrArg Prod.snd hiv
  rw [hiv0, hiv1, mdw_eq]
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    rw [hb, blake2sBytes_short hlen]
    exact chain_final (h := paramIv) (t := 0) hr (by rw [Nat.zero_add]) h
  · rintro ⟨hm, ho⟩
    refine (compressCells_iff hm (isCanonical128_metadataCell _ _)).mpr ?_
    rw [ho, hb, blake2sBytes_short hlen, unpackMetadata_metadataCell, hr, blockWords_append_zeros,
      absorb, Nat.zero_add]
    rfl

/-- The chaining value after one non-final block under the IV. -/
def hmid (m : Fin 4 → E) : E × E :=
  digestScalars (compress paramIv (blockWords (blockBytes m)) (64 : Nat).toUInt64 0 0)

/-- **Two compressions**: a non-final block under the IV, then a final one with data bytes `r`. -/
theorem compress_two_iff {b0 b1 : Fin 4 → E} {x0 x1 o0 o1 : E} {r : List UInt8}
    (hr : blockBytes b1 = r ++ List.replicate (64 - r.length) 0) (hlen : r.length ≤ 64)
    (hpos : 1 ≤ r.length) :
    (CompressCells b0 iv0 iv1 x0 x1 (mdw 64 false) ∧
      CompressCells b1 x0 x1 o0 o1 (mdw (64 + r.length) true)) ↔
      (∀ i, IsCanonical128 (b0 i)) ∧ (∀ i, IsCanonical128 (b1 i)) ∧ (x0, x1) = hmid b0 ∧
        (o0, o1) = hb (blockBytes b0 ++ r) := by
  have hiv : (iv0, iv1) = digestScalars paramIv := ivCells_eq_iv.symm
  have hiv0 : iv0 = (digestScalars paramIv).1 := congrArg Prod.fst hiv
  have hiv1 : iv1 = (digestScalars paramIv).2 := congrArg Prod.snd hiv
  set h := compress paramIv (blockWords (blockBytes b0)) (64 : Nat).toUInt64 0 0 with hh
  have hfin : blake2sBytes (blockBytes b0 ++ r) =
      compress h (blockWords r) (64 + r.length).toUInt64 lastBlock 0 := by
    rw [blake2sBytes, List.length_append, length_blockBytes,
      show (64 + r.length - 1) / 64 = 0 + 1 by omega, absorb, absorb,
      List.take_left' (length_blockBytes b0), List.drop_left' (length_blockBytes b0)]
  rw [hiv0, hiv1, mdw_eq, mdw_eq]
  constructor
  · rintro ⟨h0, h1⟩
    have e0 := compressCells_eq h0
    rw [unpackMetadata_metadataCell] at e0
    simp only [Bool.false_eq_true, ↓reduceIte] at e0
    refine ⟨h0.1, h1.1, e0, ?_⟩
    have e0' : x0 = (digestScalars h).1 ∧ x1 = (digestScalars h).2 := Prod.mk.inj e0
    rw [e0'.1, e0'.2] at h1
    have e1 := compressCells_eq h1
    rw [unpackMetadata_metadataCell, hr, blockWords_append_zeros] at e1
    rw [hb, hfin]
    exact e1
  · rintro ⟨hc0, hc1, e0, e1⟩
    refine ⟨(compressCells_iff hc0 (isCanonical128_metadataCell _ _)).mpr ?_, ?_⟩
    · rw [e0, hmid, unpackMetadata_metadataCell]; rfl
    · have e0' : x0 = (digestScalars h).1 ∧ x1 = (digestScalars h).2 := Prod.mk.inj e0
      rw [e0'.1, e0'.2]
      refine (compressCells_iff hc1 (isCanonical128_metadataCell _ _)).mpr ?_
      rw [e1, hb, hfin, unpackMetadata_metadataCell, hr, blockWords_append_zeros]
      rfl

/-! ## Blocks of cells -/

theorem blockBytes_four (a b c d : E) :
    blockBytes ![a, b, c, d] = [a, b, c, d].flatMap cellBytes := by
  simp [blockBytes]

theorem blockBytes_four' (a b c d : E) :
    blockBytes ![a, b, c, d] = [a, b, c, d].flatMap cellBytes ++ List.replicate (64 - 64) 0 := by
  rw [blockBytes_four]; rfl

theorem blockBytes_three (a b c : E) :
    blockBytes ![a, b, c, 0] = [a, b, c].flatMap cellBytes ++ List.replicate (64 - 48) 0 := by
  simp [blockBytes, cellBytes_zero]

theorem blockBytes_two (a b : E) :
    blockBytes ![a, b, 0, 0] = [a, b].flatMap cellBytes ++ List.replicate (64 - 32) 0 := by
  simp [blockBytes, cellBytes_zero]

theorem blockBytes_one (a : E) :
    blockBytes ![a, 0, 0, 0] = [a].flatMap cellBytes ++ List.replicate (64 - 16) 0 := by
  simp [blockBytes, cellBytes_zero]

theorem length_flatMap_cellBytes' (cs : List E) : (cs.flatMap cellBytes).length = 16 * cs.length :=
  length_flatMap_cellBytes cs

theorem fin4_canonical {a b c d : E} :
    (∀ i, IsCanonical128 ((![a, b, c, d] : Fin 4 → E) i)) ↔
      IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c ∧ IsCanonical128 d := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨ha, hb, hc, hd⟩ i; fin_cases i <;> assumption

/-- One final block of four cells under the IV. -/
theorem compress4_iff {a b c d o0 o1 : E} :
    CompressCells ![a, b, c, d] iv0 iv1 o0 o1 (mdw 64 true) ↔
      (IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c ∧ IsCanonical128 d) ∧
        (o0, o1) = hcell [a, b, c, d] := by
  have h := compress_final_iff (o0 := o0) (o1 := o1) (blockBytes_four' a b c d)
    (by rw [length_flatMap_cellBytes']; simp)
  rw [length_flatMap_cellBytes', show 16 * [a, b, c, d].length = 64 from rfl, fin4_canonical] at h
  rw [h, hcell]

/-- One final block of three cells and a zero under the IV. -/
theorem compress3_iff {a b c o0 o1 : E} :
    CompressCells ![a, b, c, 0] iv0 iv1 o0 o1 (mdw 48 true) ↔
      (IsCanonical128 a ∧ IsCanonical128 b ∧ IsCanonical128 c) ∧ (o0, o1) = hcell [a, b, c] := by
  have h := compress_final_iff (o0 := o0) (o1 := o1) (blockBytes_three a b c)
    (by rw [length_flatMap_cellBytes']; simp)
  rw [length_flatMap_cellBytes', show 16 * [a, b, c].length = 48 from rfl, fin4_canonical] at h
  rw [h, hcell]
  simp only [isCanonical128_zero, and_true]

end
end LeanVM.Guest.B1.Sig
