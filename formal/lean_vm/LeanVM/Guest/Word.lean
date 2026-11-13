/-
  LeanVM.Guest.Word

  The compile-time words of the zkDSL: literal embeddings, g-powers by square-and-multiply, field
  powers, limbs and bits, and the Keccak padding's words.
-/

module

public import Statement.LeanIsa
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
public import LeanVM.Parameters.Generator

/-!
# Compile-time words

What the compiler computes in `F128` while folding (`crates/lean_compiler/src/lib.rs`,
`lower/eval.rs`), on the Spec's fields:

* `word c0 c1`, the element `c0 + c1·y` from two 64-bit limbs; `litField n`, the word whose
  limbs a 128-bit source literal's bits spell (`lit_field`);
* `powBin`, square-and-multiply over the bits of the exponent, and `gpowK e = g^e` by it
  (`g_pow_u128`, proved equal to `gpow e` by `gpowK_eq`); `fieldPow` (`field_pow`);
* `limbsOf` and `wordBit`, a word's limbs and bits as the hints read them;
* the shape of a `KECCAK` state in cells (`stateCells`, `blockCells`) and the padding's words:
  `byteWord pos v`, the byte `v` at byte `pos` of a message cell (`xor_byte`), and
  `keccakPadValue`, the padding's first byte at the start of a cell (`keccak_pad_value`,
  `crates/lean_compiler/src/lower/builtins.rs`); the bytes themselves are the Spec's
  (`Protocol.KeccakHash.padFirst`, `padLast`, `rate`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- `2^128`, the bound of a source literal and of the compiler's integer arithmetic (`u128`). -/
def u128Bound : Nat := 2 ^ 128

/-- `2^64`. -/
def u64Bound : Nat := 2 ^ 64

/-- `2^32`, the bound of a compile-time index (`u32`). -/
def u32Bound : Nat := 2 ^ 32

/-- The word with these two 64-bit limbs (`F128::new`). -/
def word (c0 c1 : Nat) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1)

/-- A source literal, the word whose two limbs its 128 bits spell (`lit_field`). -/
def litField (n : Nat) : E := word (n % u64Bound) (n / u64Bound % u64Bound)

/-- `acc · b^e`, by square-and-multiply over at most `fuel` bits of `e`. -/
def powBin {M : Type} [Monoid M] : Nat → M → M → Nat → M
  | 0, _, acc, _ => acc
  | f + 1, b, acc, e =>
      if e = 0 then acc else powBin f (b * b) (if e % 2 = 1 then acc * b else acc) (e / 2)

theorem powBin_eq {M : Type} [Monoid M] :
    ∀ (f : Nat) (b acc : M) (e : Nat), e < 2 ^ f → powBin f b acc e = acc * b ^ e
  | 0, b, acc, e, h => by
      have : e = 0 := by simpa using h
      simp [powBin, this]
  | f + 1, b, acc, e, h => by
      unfold powBin
      by_cases he : e = 0
      · simp [he]
      · simp only [he, ↓reduceIte]
        rw [powBin_eq f _ _ _ (by rw [pow_succ] at h; omega)]
        have hsq : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
          rw [pow_mul, sq]
        rw [hsq]
        rcases Nat.mod_two_eq_zero_or_one e with h2 | h2
        · simp only [h2, zero_ne_one, ↓reduceIte]
          congr 2
          omega
        · simp only [h2, ↓reduceIte]
          rw [mul_assoc, ← pow_succ']
          congr 2
          omega

/-- `g^e` for `e < 2^128` (`g_pow_u128`), by square-and-multiply. -/
def gpowK (e : Nat) : K := powBin 128 g 1 e

theorem gpowK_eq {e : Nat} (h : e < u128Bound) : gpowK e = addressOfIndex e := by
  rw [gpowK, powBin_eq 128 g 1 e h, one_mul]

/-- `g^e` as a word. -/
def gpowE (e : Nat) : E := ofK (gpowK e)

/-- `b^k` for `k < 2^32` (`field_pow`). -/
def fieldPow (b : E) (k : Nat) : E := powBin 32 b 1 k

/-- `g⁻¹`, as `g^(2^64 - 2)` (`G.inv()`): the range check's runtime bound multiplies by it. -/
def gInv : K := gpowK (2 ^ 64 - 2)

/-- The two limbs of a word as natural numbers. -/
def limbsOf (x : E) : Nat × Nat :=
  ((x.limb 0).toBitVec.toNat, (x.limb 1).toBitVec.toNat)

/-- Bit `i < 128` of a word, limb `i / 64` first; `false` past it. -/
def wordBit (x : E) (i : Nat) : Bool :=
  let (c0, c1) := limbsOf x
  let l := if i / 64 = 0 then c0 else if i / 64 = 1 then c1 else 0
  (l / 2 ^ (i % 64)) % 2 = 1

/-- The cells of a Keccak state (`STATE_CELLS`, `crates/leanvm_core/src/keccak.rs:54`). -/
def stateCells : Nat := 13

/-- The rate cells a block of `136` bytes covers (`RATE_CELLS`,
`crates/leanvm_core/src/keccak.rs:56`). -/
def blockCells : Nat := 9

/-- The byte `v < 256` at byte `pos % 16` of a message cell, little-endian in limb `0` then limb
`1`, as the word XORed into the cell (`xor_byte`). -/
def byteWord (pos v : Nat) : E :=
  let byte := pos % 16
  let w := v * 2 ^ (8 * (byte % 8))
  if byte < 8 then word w 0 else word 0 w

/-- A cell holding the padding's first byte at its start (`keccak_pad_value`). -/
def keccakPadValue : E := word Protocol.KeccakHash.padFirst.toNat 0

end
end LeanVM.Guest
