/-
  LeanVM.Guest.Word

  The compile-time words of the zkDSL: literal embeddings, g-powers by square-and-multiply, field
  powers, BLAKE2s metadata and the initial chaining value as memory cells.
-/

module

public import LeanVM.Spec.Isa
public import LeanVM.Parameters.Generator

/-!
# Compile-time words

What the compiler computes in `F192` while folding (`crates/lean_compiler/src/lib.rs`,
`lower/eval.rs`), on the Spec's fields:

* `word c0 c1 c2`, the element `c0 + c1·y + c2·y²` from three 64-bit limbs; `litField n`, the
  embedding of a 128-bit source literal (`lit_field`);
* `powBin`, square-and-multiply over the bits of the exponent, and `gpowK e = g^e` by it
  (`g_pow_u128`, proved equal to `gpow e` by `gpowK_eq`); `fieldPow` (`field_pow`);
* `metadata` (`hash_flock::metadata`) and `ivCells`, the parameterized BLAKE2s-256 chaining value
  as its two memory cells (`hash_flock::IV_CELLS`).
-/

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Blake2sHash

@[expose] public section

/-- `2^128`, the bound of a source literal and of the compiler's integer arithmetic (`u128`). -/
def u128Bound : Nat := 2 ^ 128

/-- `2^64`. -/
def u64Bound : Nat := 2 ^ 64

/-- `2^32`, the bound of a compile-time index (`u32`). -/
def u32Bound : Nat := 2 ^ 32

/-- The word with these three 64-bit limbs (`F192::new`). -/
def word (c0 c1 c2 : Nat) : E := E.ofLimbs (K.ofBits c0) (K.ofBits c1) (K.ofBits c2)

/-- A source literal, its 128 bits in the low two limbs (`lit_field`). -/
def litField (n : Nat) : E := word (n % u64Bound) (n / u64Bound % u64Bound) 0

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

theorem gpowK_eq {e : Nat} (h : e < u128Bound) : gpowK e = gpow e := by
  rw [gpowK, powBin_eq 128 g 1 e h, one_mul]

/-- `g^e` as a word. -/
def gpowE (e : Nat) : E := ofK (gpowK e)

/-- `b^k` for `k < 2^32` (`field_pow`). -/
def fieldPow (b : E) (k : Nat) : E := powBin 32 b 1 k

theorem fieldPow_eq {b : E} {k : Nat} (h : k < u32Bound) : fieldPow b k = b ^ k := by
  rw [fieldPow, powBin_eq 32 b 1 k h, one_mul]

/-- `g⁻¹`, as `g^(2^64 - 2)` (`G.inv()`): the range check's runtime bound multiplies by it. -/
def gInv : K := gpowK (2 ^ 64 - 2)

/-- BLAKE2s's last-block flag word (`hash_flock::FINAL_FLAG`). -/
def finalFlag : Nat := 2 ^ 32 - 1

/-- The metadata word: the counter in limb 0, the flags in the halves of limb 1
(`hash_flock::metadata`). -/
def metadata (counter f0 f1 : Nat) : E := word counter (f0 + f1 * 2 ^ 32) 0

/-- The parameterized BLAKE2s-256 initial chaining value as its two memory cells
(`hash_flock::IV_CELLS`). -/
def ivCells : E × E := digestScalars paramIv

/-- The three limbs of a word as natural numbers. -/
def limbsOf (x : E) : Nat × Nat × Nat :=
  ((x.limb 0).toBitVec.toNat, (x.limb 1).toBitVec.toNat, (x.limb 2).toBitVec.toNat)

/-- Bit `i < 192` of a word, limb `i / 64` first. -/
def wordBit (x : E) (i : Nat) : Bool :=
  let (c0, c1, c2) := limbsOf x
  let l := if i / 64 = 0 then c0 else if i / 64 = 1 then c1 else c2
  (l / 2 ^ (i % 64)) % 2 = 1

end
end LeanVM.Guest
