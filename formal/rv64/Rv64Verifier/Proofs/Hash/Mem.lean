import Rv64Verifier.Proofs.Common

/-!
# Doubleword lists and bytes in memory

`readWords` (riscv-zkvm) read element by element, and bytes (`getByte`, `extractByte`) of
doublewords.
-/

namespace Rv64Verifier
open RiscvZkvm.Rv64

theorem readWords_length (s : MachineState) (b : Word) (n : Nat) : (s.readWords b n).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [MachineState.readWords_succ, ih]

theorem readWords_getElem (s : MachineState) (b : Word) (n i : Nat) (hi : i < n)
    (h : i < (s.readWords b n).length := by rw [readWords_length]; exact hi) :
    (s.readWords b n)[i] = s.getMem (b + BitVec.ofNat 64 (8 * i)) := by
  induction n generalizing b i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [MachineState.readWords_succ, List.getElem_cons_succ]
      rw [ih (b + 8) i (by omega)]
      congr 1
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      have h8 : (8 : Word).toNat = 8 := rfl
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h8]
      omega

theorem readWords_getD (s : MachineState) (b : Word) (n i : Nat) (hi : i < n) :
    (s.readWords b n).getD i 0 = s.getMem (b + BitVec.ofNat 64 (8 * i)) := by
  rw [List.getD_eq_getElem _ _ (by rw [readWords_length]; exact hi), readWords_getElem _ _ _ _ hi]

/-- A list of doublewords in memory, from its elements. -/
theorem readWords_eq {t : MachineState} {b : Word} {n : Nat} {l : List Word} (hl : l.length = n)
    (h : ∀ i < n, t.getMem (b + BitVec.ofNat 64 (8 * i)) = l.getD i 0) : t.readWords b n = l := by
  apply List.ext_getElem
  · rw [readWords_length, hl]
  · intro i hi hi'
    rw [readWords_length] at hi
    rw [readWords_getElem _ _ _ _ hi, h i hi, List.getD_eq_getElem]

theorem readWords_congr {s t : MachineState} {b b' : Word} {n : Nat}
    (h : ∀ i < n, t.getMem (b + BitVec.ofNat 64 (8 * i)) = s.getMem (b' + BitVec.ofNat 64 (8 * i))) :
    t.readWords b n = s.readWords b' n :=
  readWords_eq (readWords_length _ _ _) fun i hi ↦ by rw [h i hi, readWords_getD _ _ _ _ hi]

/-! ## Bytes -/

theorem extractByte_eq (w : Word) (j : Nat) : extractByte w j = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
  congr 1
  omega

/-- A doubleword is determined by its eight bytes. -/
theorem word_eq_of_bytes {x y : Word} (h : ∀ j < 8, extractByte x j = extractByte y j) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj := h (i / 8) (by omega)
  rw [extractByte_eq, extractByte_eq] at hj
  have := congrArg (fun z : BitVec 8 ↦ z.getLsbD (i % 8)) hj
  simp only [BitVec.getLsbD_extractLsb', show i % 8 < 8 by omega, decide_true,
    Bool.true_and] at this
  rwa [show 8 * (i / 8) + i % 8 = i by omega] at this

theorem alignToDword_add {a : Word} (ha : a.toNat % 8 = 0) {j : Nat} (hj : j < 8) :
    alignToDword (a + BitVec.ofNat 64 j) = a := by
  apply BitVec.eq_of_toNat_eq
  rw [Sym.alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
  by_cases hw : a.toNat + j < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hw]; omega
  · omega

theorem byteOffset_add {a : Word} (ha : a.toNat % 8 = 0) {j : Nat} (hj : j < 8) :
    byteOffset (a + BitVec.ofNat 64 j) = j := by
  rw [Sym.byteOffset_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
  have := a.isLt
  rw [Nat.mod_eq_of_lt (by omega : j < 2 ^ 64)]
  by_cases hw : a.toNat + j < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hw]; omega
  · omega

/-- Byte `j` of an aligned doubleword. -/
theorem getByte_aligned (s : MachineState) {a : Word} (ha : a.toNat % 8 = 0) {j : Nat}
    (hj : j < 8) : s.getByte (a + BitVec.ofNat 64 j) = extractByte (s.getMem a) j := by
  rw [MachineState.getByte, alignToDword_add ha hj, byteOffset_add ha hj]

/-- Two aligned doublewords with the same bytes are equal. -/
theorem getMem_eq_of_bytes {s t : MachineState} {a b : Word} (ha : a.toNat % 8 = 0)
    (hb : b.toNat % 8 = 0)
    (h : ∀ j < 8, t.getByte (a + BitVec.ofNat 64 j) = s.getByte (b + BitVec.ofNat 64 j)) :
    t.getMem a = s.getMem b :=
  word_eq_of_bytes fun j hj ↦ by
    rw [← getByte_aligned t ha hj, ← getByte_aligned s hb hj]; exact h j hj

/-- One doubleword of a list in memory replaced. -/
theorem readWords_set {t t' : MachineState} {b : Word} {n p : Nat} {v : Word}
    (hv : t'.getMem (b + BitVec.ofNat 64 (8 * p)) = v)
    (hfr : ∀ j < n, j ≠ p →
      t'.getMem (b + BitVec.ofNat 64 (8 * j)) = t.getMem (b + BitVec.ofNat 64 (8 * j))) :
    t'.readWords b n = (t.readWords b n).set p v := by
  apply readWords_eq (by rw [List.length_set, readWords_length])
  intro j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hjp : p = j
  · subst hjp
    simp only [↓reduceIte, readWords_length, hj]
    exact hv
  · simp only [hjp, ↓reduceIte]
    rw [← List.getD_eq_getElem?_getD, readWords_getD _ _ _ _ hj]
    exact hfr j hj (Ne.symm hjp)

theorem extractByte_zero (j : Nat) : extractByte 0 j = 0 := by
  simp [extractByte]

end Rv64Verifier
