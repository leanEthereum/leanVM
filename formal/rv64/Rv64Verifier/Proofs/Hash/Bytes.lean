import Rv64Verifier.Proofs.Hash.Contracts

/-!
# Byte ranges

`BytesValid` from doubleword validity, and doublewords from `bytesAt`.
-/

namespace Rv64Verifier.Contracts
open RiscvZkvm.Rv64

/-- The bytes of `n` valid doublewords followed by a valid one are valid: two consecutive valid
doublewords lie in one zone of memory. -/
theorem bytesValid_of_range {a : Word} {n : Nat} (h : ValidMemRange a (n + 1)) :
    BytesValid a (8 * n) := by
  have hb := ValidMemRange.bounds h (by omega)
  refine ⟨by omega, fun i hi ↦ ?_⟩
  have h1 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h (i / 8) (by omega)))
  have h2 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h (i / 8 + 1) (by omega)))
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at h1 h2
  simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- A byte range in the RAM zone is valid. -/
theorem bytesValid_ram {a : Word} {n : Nat} (h1 : 0xa0000000 ≤ a.toNat)
    (h2 : a.toNat + n ≤ 0xc0000001) : BytesValid a n := by
  refine ⟨by omega, fun i hi ↦ ?_⟩
  simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

/-- A range in one data window has valid bytes. -/
theorem _root_.Rv64Verifier.Runtime.Mapped.bytesValid {a : Word} {n : Nat} (h : Runtime.Mapped a n) :
    BytesValid a n := by
  simp only [Runtime.Mapped] at h
  refine ⟨by omega, fun i hi ↦ ?_⟩
  simp only [isValidMemAddr, MEM_START, MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START,
    RAM_MEM_END, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_add,
    BitVec.toNat_ofNat]
  omega

theorem _root_.Rv64Verifier.Runtime.Mapped.sub {a : Word} {n k m : Nat} (h : Runtime.Mapped a n)
    (hk : k + m ≤ n) : Runtime.Mapped (a + BitVec.ofNat 64 k) m := by
  simp only [Runtime.Mapped] at h ⊢
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The bytes of `n` valid doublewords followed by a valid one lie in one data window: no valid
doubleword starts between the windows. -/
theorem mapped_of_range {a : Word} {n : Nat} (h : ValidMemRange a (n + 1)) :
    Runtime.Mapped a (8 * n) := by
  have hb := ValidMemRange.bounds h (by omega)
  have h0 := (Sym.validAccess_eight _).mp (validAccess_of_dword (h 0 (by omega)))
  have hn := (Sym.validAccess_eight _).mp (validAccess_of_dword (h n (by omega)))
  simp only [Nat.mul_zero, BitVec.add_zero] at h0
  rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hn
  simp only [Runtime.Mapped]
  by_cases hgap : a.toNat ≤ 0x78000000 ∧ 0xa0000000 ≤ (a.toNat + 8 * n) % 2 ^ 64
  · have hi := (Sym.validAccess_eight _).mp (validAccess_of_dword
      (h ((0x78000008 - a.toNat) / 8) (by omega)))
    rw [BitVec.toNat_add, BitVec.toNat_ofNat] at hi
    omega
  · omega

theorem getByte_of_bytesAt {t : MachineState} {a : Word} {n : Nat} {l : List (BitVec 8)}
    (h : bytesAt t a n = l) {i : Nat} (hi : i < n) :
    t.getByte (a + BitVec.ofNat 64 i) = l.getD i 0 := by
  rw [← h, bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem ofNat_add_ofNat (a : Word) (i j : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (i + j) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- A doubleword of two aligned byte ranges that agree. -/
theorem getMem_of_bytesAt {s t : MachineState} {a b : Word} {n : Nat} (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0) (h : bytesAt t a n = bytesAt s b n) {j : Nat} (hj : 8 * j + 8 ≤ n) :
    t.getMem (a + BitVec.ofNat 64 (8 * j)) = s.getMem (b + BitVec.ofNat 64 (8 * j)) := by
  have hal (x : Word) (hx : x.toNat % 8 = 0) : (x + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := x.isLt
    omega
  apply getMem_eq_of_bytes (hal a ha) (hal b hb)
  intro i hi
  rw [ofNat_add_ofNat, ofNat_add_ofNat, getByte_of_bytesAt h (by omega),
    getByte_of_bytesAt (n := n) rfl (by omega)]

/-- A doubleword of an aligned byte range of zeros. -/
theorem getMem_of_bytesAt_zero {t : MachineState} {a : Word} {n : Nat} (ha : a.toNat % 8 = 0)
    (h : bytesAt t a n = List.replicate n 0) {j : Nat} (hj : 8 * j + 8 ≤ n) :
    t.getMem (a + BitVec.ofNat 64 (8 * j)) = 0 := by
  have hal : (a + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have := a.isLt
    omega
  apply word_eq_of_bytes
  intro i hi
  rw [← getByte_aligned t hal hi, ofNat_add_ofNat, getByte_of_bytesAt h (by omega),
    extractByte_zero]
  simp [List.getD_eq_getElem?_getD, show 8 * j + i < n by omega]

end Rv64Verifier.Contracts
