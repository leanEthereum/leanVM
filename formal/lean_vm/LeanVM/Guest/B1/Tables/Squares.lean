/-
  LeanVM.Guest.B1.Tables.Squares

  The squares of `g`, `g^(2^j)` for `j < 34`, as kernel-checked words: the `g_squares` table, the
  index MLE's factors `1 + g^(2^t)` and the selectors' shares.
-/

module

public import LeanVM.Guest.B1.Tables.Basic

/-!
# The squares of `g`

`tbSquares n x` is `x, x², x⁴, …` (`n` terms), computed by one squaring an entry, never by a naive
power; `tbGSquaresBits` lists `g^(2^j)`, `j < 34`, as 64-bit words, checked against it by kernel
decision (`eOfNat_tbGSquaresBits`). Ported from the BLAKE2s-era `Value/Tables` (branch `mumbai`),
local until a shared module has it.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Guest.Value

@[expose] public section

/-- `SIZE_BITS` (G:52). -/
abbrev tbSizeBits : ℕ := 34

/-- `n` successive tbSquares from `x`: `x, x², x⁴, …`, as `sq_run *= sq_run` computes them. -/
def tbSquares {R : Type} [Mul R] : ℕ → R → List R
  | 0, _ => []
  | n + 1, x => x :: tbSquares n (x * x)

theorem tbLength_squares {R : Type} [Mul R] (n : ℕ) (x : R) : (tbSquares n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [tbSquares, ih]

/-- Entry `j` of the tbSquares from `x` is `x^(2^j)`. -/
theorem tbGetElem_squares {R : Type} [Monoid R] (n : ℕ) (x : R) (j : ℕ)
    (hj : j < (tbSquares n x).length) : (tbSquares n x)[j] = x ^ 2 ^ j := by
  induction n generalizing x j with
  | zero => simp [tbSquares] at hj
  | succ n ih =>
    cases j with
    | zero => simp [tbSquares]
    | succ j =>
      simp only [tbSquares, List.getElem_cons_succ]
      rw [ih (x * x) j (by simpa [tbSquares] using hj), ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

/-- `g^(2^j)` for `j < 34`, as 64-bit words. -/
def tbGSquaresBits : List ℕ := [
  0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101,
  0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e,
  0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13,
  0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527,
  0xb6d535c542116f62, 0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588,
  0x180d86953ed141c6, 0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba,
  0x5c62236777028505, 0xb964dc682c67ddcd]

/-- The words are the tbSquares of `g`, decided by the kernel over `tbSquares`. -/
theorem tbGSquaresBits_eq : tbGSquaresBits.map K.ofBits = tbSquares tbSizeBits g := by decide +kernel

theorem length_tbGSquaresBits : tbGSquaresBits.length = tbSizeBits := rfl

/-- **The `g_tbSquares` constants**: word `j < 34` is `g^(2^j)` in `K`. -/
theorem ofBits_tbGSquaresBits (j : ℕ) (hj : j < tbSizeBits) :
    K.ofBits (tbGSquaresBits.getD j 0) = g ^ 2 ^ j := by
  have h := congrArg (fun l : List K ↦ l[j]?) tbGSquaresBits_eq
  have hj1 : j < tbGSquaresBits.length := by rw [length_tbGSquaresBits]; exact hj
  have hj2 : j < (tbSquares tbSizeBits g).length := by rw [tbLength_squares]; exact hj
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
    Option.map_some, Option.some.injEq, tbGetElem_squares] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some, h]

/-- The same in `E`: the cell `E(word j)` is `GEN^(2^j)`. -/
theorem eOfNat_tbGSquaresBits (j : ℕ) (hj : j < tbSizeBits) :
    eOfNat (tbGSquaresBits.getD j 0) = gen ^ 2 ^ j := by
  rw [eOfNat, ofBits_tbGSquaresBits j hj, ofK_pow]
  rfl

/-- `g^(2^j)`, `j < 34`, is the word `tbGSquaresBits[j]`. -/
theorem gen_pow_two_pow_eq {j : ℕ} (hj : j < 34) : gen ^ 2 ^ j = eOfNat (tbGSquaresBits.getD j 0) :=
  (eOfNat_tbGSquaresBits j hj).symm

end
end LeanVM.Guest.B1.Tables
