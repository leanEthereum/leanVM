/-
  LeanVM.Guest.B1.Main.Basic

  The vocabulary of `main`'s proof: claims and digests as the cells the guest holds them in, and
  the statement's digest from the bytes `statement_digest` hashes.
-/

module

public import LeanVM.Guest.B1.Main.Interface
public import LeanVM.Guest.B1.Digest.ChildDigest
public import LeanVM.Facts.ClaimBytes

/-!
# `main`: claims, digests and cells

* `claimBytes_cells`: the 64 bytes of a signature claim decoded from four cells
  (`Sig.xmssClaimOf`, `Sig.sphincsClaimOf`) are the cells' bytes, limbs `0` and `1` each;
* `digestBytes_ofCells`, `digestScalars_ofCells'`, `digestOfCells_scalars`: a digest held in two
  canonical cells;
* `xmssListDigest_cells`, `sphincsListDigest_cells`, `daListDigest_cells`: a list of claims read
  off `4n` canonical cells hashes as the cells do;
* `cellAt_eq_memAt`, `slotCells_of_readsAt`: `main`'s memory reads are the digest family's.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Digest LeanVM.Node

@[expose] public section

/-! ## Bytes of cells -/

theorem toNat_byteOfBitVec {n : ℕ} (v : BitVec n) (i : ℕ) :
    (UInt8.ofBitVec (v.extractLsb' (8 * i) 8)).toNat = v.toNat / 2 ^ (8 * i) % 256 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem length_kBytes (a : K) : (K.toBytes a).length = 8 := by simp [K.toBytes, wordBytes]

theorem toNat_kBytes (a : K) (k : ℕ) (hk : k < 8) :
    ((K.toBytes a)[k]'(by rw [length_kBytes]; exact hk)).toNat = kToNat a / 2 ^ (8 * k) % 256 := by
  simp only [K.toBytes, wordBytes, List.getElem_map, List.getElem_range]
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  have : (8 * k).toUInt64.toNat % 64 = 8 * k := by
    rw [Nat.toUInt64_eq]; simp; omega
  rw [this, Nat.shiftRight_eq_div_pow]
  rfl

theorem kToNat_lt (a : K) : kToNat a < 2 ^ 64 := a.toBitVec.isLt

theorem length_cellBytes' (c : E) : (cellBytes c).length = 16 := by
  simp [cellBytes, length_kBytes]

/-- The bytes of a cell are its 128-bit value's (`Sig.cellVal`). -/
theorem bytes16_cellVal (a : E) : HashSig.littleEndianBytes 16 (Sig.cellVal a) = cellBytes a := by
  apply List.ext_getElem (by simp [HashSig.littleEndianBytes])
  intro i h1 h2
  have hi : i < 16 := by simpa [HashSig.littleEndianBytes] using h1
  apply UInt8.toNat_inj.mp
  simp only [HashSig.littleEndianBytes, List.getElem_ofFn]
  rw [toNat_byteOfBitVec]
  have hv : (Sig.cellVal a).toNat = kToNat (a.limb 1) * 2 ^ 64 + kToNat (a.limb 0) := by
    simp only [Sig.cellVal, BitVec.toNat_append]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (a.limb 0).toBitVec.isLt, Nat.shiftLeft_eq]
    rfl
  rw [hv]
  have l0 := kToNat_lt (a.limb 0)
  have l1 := kToNat_lt (a.limb 1)
  simp only [cellBytes]
  by_cases h8 : i < 8
  · rw [List.getElem_append_left (by rw [length_kBytes]; exact h8), toNat_kBytes _ _ h8]
    interval_cases i <;> omega
  · rw [List.getElem_append_right (by rw [length_kBytes]; omega)]
    simp only [length_kBytes]
    rw [toNat_kBytes _ _ (by omega)]
    interval_cases i <;> omega

theorem bytes32_cellPairVal (c d : E) :
    HashSig.littleEndianBytes 32 (Sig.cellPairVal c d) = cellBytes c ++ cellBytes d := by
  apply List.ext_getElem (by simp [HashSig.littleEndianBytes])
  intro i h1 h2
  have hi : i < 32 := by simpa [HashSig.littleEndianBytes] using h1
  apply UInt8.toNat_inj.mp
  simp only [HashSig.littleEndianBytes, List.getElem_ofFn]
  rw [toNat_byteOfBitVec]
  have hv : (Sig.cellPairVal c d).toNat =
      (kToNat (d.limb 1) * 2 ^ 64 + kToNat (d.limb 0)) * 2 ^ 128 +
        (kToNat (c.limb 1) * 2 ^ 64 + kToNat (c.limb 0)) := by
    simp only [Sig.cellPairVal, Sig.cellVal, BitVec.toNat_append]
    have c0 := (c.limb 0).toBitVec.isLt
    have c1 := (c.limb 1).toBitVec.isLt
    rw [← Nat.shiftLeft_add_eq_or_of_lt (d.limb 0).toBitVec.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (c.limb 0).toBitVec.isLt,
      ← Nat.shiftLeft_add_eq_or_of_lt (b := (c.limb 1).toBitVec.toNat <<< 64 + (c.limb 0).toBitVec.toNat)
        (by rw [Nat.shiftLeft_eq]; omega)]
    simp only [Nat.shiftLeft_eq]
    rfl
  rw [hv]
  have c0 := kToNat_lt (c.limb 0)
  have c1 := kToNat_lt (c.limb 1)
  have d0 := kToNat_lt (d.limb 0)
  have d1 := kToNat_lt (d.limb 1)
  simp only [cellBytes, List.append_assoc]
  by_cases h8 : i < 8
  · rw [List.getElem_append_left (by rw [length_kBytes]; exact h8), toNat_kBytes _ _ h8]
    interval_cases i <;> omega
  · rw [List.getElem_append_right (by rw [length_kBytes]; omega)]
    simp only [length_kBytes]
    by_cases h16 : i < 16
    · rw [List.getElem_append_left (by rw [length_kBytes]; omega), toNat_kBytes _ _ (by omega)]
      interval_cases i <;> omega
    · rw [List.getElem_append_right (by rw [length_kBytes]; omega)]
      simp only [length_kBytes]
      by_cases h24 : i < 24
      · rw [List.getElem_append_left (by rw [length_kBytes]; omega), toNat_kBytes _ _ (by omega)]
        interval_cases i <;> omega
      · rw [List.getElem_append_right (by rw [length_kBytes]; omega)]
        simp only [length_kBytes]
        rw [toNat_kBytes _ _ (by omega)]
        interval_cases i <;> omega

/-- **A claim's 64 bytes are its four cells' bytes.** -/
theorem claimBytes_cells (a b c d : E) :
    claimBytesOf (Sig.cellVal a) (Sig.cellVal b) (Sig.cellPairVal c d) = cellsBytes [a, b, c, d] := by
  rw [claimBytesOf, bytes16_cellVal, bytes16_cellVal, bytes32_cellPairVal]
  simp [cellsBytes, List.append_assoc]

/-! ## Digests in cells -/

theorem digestBytes_ofCells (a b : E) : digestBytes (digestOfCells a b) = cellsBytes [a, b] := by
  simp [digestBytes, digestOfCells, cellsBytes, cellBytes, K.toBytes, List.append_assoc]

theorem digestScalars_ofCells' {a b : E} (ha : IsCanonical128 a) (hb : IsCanonical128 b) :
    digestHalves (digestOfCells a b) = (a, b) :=
  digestScalars_ofCells ha hb

theorem digestOfCells_scalars (d : Digest) :
    digestOfCells (digestHalves d).1 (digestHalves d).2 = d := by
  apply Vector.ext
  intro i hi
  simp only [digestOfCells, digestHalves]
  interval_cases i <;> simp [K.ofLane, K.lane]

theorem digestBytes_eq_cells (d : Digest) :
    digestBytes d = cellsBytes [(digestHalves d).1, (digestHalves d).2] := by
  conv_lhs => rw [← digestOfCells_scalars d]
  exact digestBytes_ofCells _ _

theorem digestScalars_canonical (d : Digest) :
    IsCanonical128 (digestHalves d).1 ∧ IsCanonical128 (digestHalves d).2 :=
  ⟨rfl, rfl⟩

theorem digestScalars_inj {d d' : Digest} (h : digestHalves d = digestHalves d') : d = d' := by
  rw [← digestOfCells_scalars d, ← digestOfCells_scalars d', h]

theorem digestCells_inj {d d' : Digest} (h : digestCells d = digestCells d') : d = d' := by
  simp only [digestCells, List.cons.injEq, and_true] at h
  exact digestScalars_inj (Prod.ext h.1 h.2)

/-! ## Memory reads -/

theorem cellAt_eq_memAt : cellAt = memAt := rfl

theorem readCells_eq_memRun : readCells = memRun := rfl

/-! ## The claim lists -/

/-- The claims of `4n` cells, by a decoder of four cells. -/
theorem flatMap_slots {α : Type} (f : E → E → E → E → α) (bytes : α → List UInt8)
    (hb : ∀ a b c d, bytes (f a b c d) = cellsBytes [a, b, c, d]) :
    ∀ (cells : List E) (n : ℕ), cells.length = 4 * n →
      ((List.range n).map fun s => f (cells.getD (4 * s) 0) (cells.getD (4 * s + 1) 0)
        (cells.getD (4 * s + 2) 0) (cells.getD (4 * s + 3) 0)).flatMap bytes = cellsBytes cells := by
  intro cells n
  induction n generalizing cells with
  | zero => intro h; simp_all
  | succ n ih =>
    intro h
    obtain ⟨a, b, c, d, rest, rfl⟩ : ∃ a b c d rest, cells = a :: b :: c :: d :: rest := by
      match cells, h with
      | a :: b :: c :: d :: rest, _ => exact ⟨a, b, c, d, rest, rfl⟩
    rw [List.range_succ_eq_map, List.map_cons, List.flatMap_cons]
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_cons_zero, List.getD_cons_succ, List.map_map]
    rw [hb]
    have hrest : rest.length = 4 * n := by simp at h; omega
    have := ih rest hrest
    rw [show (cellsBytes (a :: b :: c :: d :: rest)) = cellsBytes [a, b, c, d] ++ cellsBytes rest by
      simp [cellsBytes]]
    congr 1

end
end LeanVM.Guest.B1.Main
