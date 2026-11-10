import Rv64Verifier.Proofs.Runtime.Alloc
import Rv64Verifier.Proofs.Runtime.Step

/-!
# What the bytecode and input proofs share

* Validity of sub-doubleword accesses inside a `Mapped` range (`valid_byte`, `valid_half`,
  `valid_dword`).
* A doubleword stored byte by byte, its eight bytes in any order, is the doubleword
  (`replaceBytes_eq`).
-/

namespace Rv64Verifier.Proofs.Bytecode
open RiscvZkvm.Rv64 Rv64Verifier.Runtime

theorem valid_byte {a x : Word} {n : Nat} (h : Mapped a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat < a.toNat + n) : Sym.validAccess 1 x = true := by
  simp only [Sym.validAccess, isValidByteAccess, isValidMemAddr_eq, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq]
  simp only [Mapped] at h
  omega

theorem valid_half {a x : Word} {n : Nat} (h : Mapped a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 2 ≤ a.toNat + n) (h3 : x.toNat % 2 = 0) : Sym.validAccess 2 x = true := by
  simp only [Sym.validAccess, isValidHalfwordAccess, isValidMemAddr_eq, isAligned2_eq, MEM_START,
    MEM_END, INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  simp only [Mapped] at h
  omega

theorem valid_dword {a x : Word} {n : Nat} (h : Mapped a n) (h1 : a.toNat ≤ x.toNat)
    (h2 : x.toNat + 8 ≤ a.toNat + n) (h3 : x.toNat % 8 = 0) : Sym.validAccess 8 x = true :=
  Mapped.valid8 h h1 h2 h3

/-- `valid_in h [f₁, ..]`: a byte, halfword or aligned doubleword access inside the `Mapped` range
`h`, its bounds by `addr_omega [f₁, ..]`. -/
macro "valid_in " h:term:max " [" ts:term,* "]" : tactic =>
  `(tactic| first
    | (refine valid_dword $h ?_ ?_ ?_ <;> addr_omega [$ts,*])
    | (refine valid_half $h ?_ ?_ ?_ <;> addr_omega [$ts,*])
    | (refine valid_byte $h ?_ ?_ <;> addr_omega [$ts,*]))

/-- Eight byte stores, one per byte of `w`, in the order the compiler emits them. -/
theorem replaceBytes_eq (old w : Word) :
    replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
      (replaceByte old 4 ((w >>> 32).truncate 8)) 5 ((w >>> 40).truncate 8)) 6
      ((w >>> 48).truncate 8)) 7 ((w >>> 56).truncate 8)) 0 (w.truncate 8)) 1
      ((w >>> 8).truncate 8)) 2 ((w >>> 16).truncate 8)) 3 ((w >>> 24).truncate 8) = w := by
  apply eq_of_extractByte
  intro i hi
  simp only [extractByte_replaceByte _ _ (by decide : (0 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (1 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (2 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (3 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (4 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (5 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (6 : Nat) < 8) hi,
    extractByte_replaceByte _ _ (by decide : (7 : Nat) < 8) hi]
  interval_cases i <;> simp [extractByte]

end Rv64Verifier.Proofs.Bytecode
