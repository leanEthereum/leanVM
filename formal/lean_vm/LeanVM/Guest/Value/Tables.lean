/-
  LeanVM.Guest.Value.Tables

  The guest's exponent tables: `g_logs_pow2[g^j] = E(2^j)` and `g_squares[g^j] = g^(2^j)` for
  `j < 34`, the second by repeated squaring, generically and as kernel-checked words.
-/

module

public import LeanVM.Guest.Value.Tower

/-!
# The exponent tables (`exponent_tables`, G:572-587)

`exponent_tables` fills two heap tables over the exponent domain, both of `SIZE_BITS = 34`
entries (G:46): `g_logs_pow2[g^j] = 2^j`, a zkDSL integer, so `eOfNat (2^j)`; and
`g_squares[g^j] = sq_run`, where `sq_run` starts at `GEN` and is squared after each entry, so
`g^(2^j)` (`squares_eq`). Both values are compile-time, so the compiler may fold the products
into constants: `gSquaresBits` lists them as 64-bit words, and `ofBits_gSquaresBits` checks
them by kernel decision, through `squares`, which computes the table by one squaring an entry
(33 multiplications in `K`), never `g^(2^j)` by a naive power. A table's address `g^j` is the
word `2^j` (`Tower.g_pow_eq_ofBits`).
-/

namespace LeanVM.Guest.Value

open LeanVM.Parameters LeanVM.Protocol.Verifier

@[expose] public section

/-- `SIZE_BITS` (G:46): the tables' length. -/
abbrev sizeBits : ℕ := 34

/-- `n` successive squares from `x`: `x, x², x⁴, …`, as `sq_run *= sq_run` computes them. -/
def squares {R : Type} [Mul R] : ℕ → R → List R
  | 0, _ => []
  | n + 1, x => x :: squares n (x * x)

theorem length_squares {R : Type} [Mul R] (n : ℕ) (x : R) : (squares n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [squares, ih]

/-- Entry `j` of the squares from `x` is `x^(2^j)`. -/
theorem getElem_squares {R : Type} [Monoid R] (n : ℕ) (x : R) (j : ℕ)
    (hj : j < (squares n x).length) : (squares n x)[j] = x ^ 2 ^ j := by
  induction n generalizing x j with
  | zero => simp [squares] at hj
  | succ n ih =>
    cases j with
    | zero => simp [squares]
    | succ j =>
      simp only [squares, List.getElem_cons_succ]
      rw [ih (x * x) j (by simpa [squares] using hj), ← sq, ← pow_mul, pow_succ, Nat.mul_comm]

/-- **`g_squares`** (G:582-586): a run that starts at `GEN` and is squared at each step holds
`g^(2^j)` at step `j`. -/
theorem squares_eq {s : ℕ → E} (h0 : s 0 = gen) (hs : ∀ j, s (j + 1) = s j * s j) (j : ℕ) :
    s j = gen ^ 2 ^ j := by
  induction j with
  | zero => rw [h0, pow_zero, pow_one]
  | succ j ih => rw [hs, ih, ← sq, ← pow_mul, pow_succ]

/-- **`g_logs_pow2`** (G:578-580): entry `j < 34` is `E(2^j)`, below `2^64`. -/
theorem logsPow2_lt {j : ℕ} (hj : j < sizeBits) : 2 ^ j < 2 ^ 64 :=
  Nat.pow_lt_pow_right (by decide) (lt_trans hj (by decide))

/-- `g^(2^j)` for `j < 34`, as 64-bit words. -/
def gSquaresBits : List ℕ := [
  0x2, 0x4, 0x10, 0x100, 0x10000, 0x100000000, 0x1b, 0x145, 0x11011, 0x101000101,
  0x100000001001a, 0x1a00000144, 0x10dbc, 0x100514550, 0x11011011111b, 0x10001011a1a015e,
  0x15f0144001a114f, 0x1aad43011ba1e5, 0x11cefef6be466, 0x5455145e48670f13,
  0xbaf1bebe1ae4ad02, 0xb0ef530df44bb042, 0xe2170b43ee771735, 0x48380fd207a3b527,
  0xb6d535c542116f62, 0xa6df6baa62f965f5, 0xb9df3947cea0ffe7, 0xe1882807248fe588,
  0x180d86953ed141c6, 0x1894566cd1db8abf, 0x4cc78bf4ea999e25, 0xe333308087e402ba,
  0x5c62236777028505, 0xb964dc682c67ddcd]

/-- The words are the squares of `g`, decided by the kernel over `squares`. -/
theorem gSquaresBits_eq : gSquaresBits.map K.ofBits = squares sizeBits g := by decide +kernel

theorem length_gSquaresBits : gSquaresBits.length = sizeBits := rfl

/-- **The `g_squares` constants**: word `j < 34` is `g^(2^j)` in `K`. -/
theorem ofBits_gSquaresBits (j : ℕ) (hj : j < sizeBits) :
    K.ofBits (gSquaresBits.getD j 0) = g ^ 2 ^ j := by
  have h := congrArg (fun l : List K ↦ l[j]?) gSquaresBits_eq
  have hj1 : j < gSquaresBits.length := by rw [length_gSquaresBits]; exact hj
  have hj2 : j < (squares sizeBits g).length := by rw [length_squares]; exact hj
  simp only [List.getElem?_map, List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hj2,
    Option.map_some, Option.some.injEq, getElem_squares] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some, h]

/-- The same in `E`: the cell `E(word j)` is `GEN^(2^j)`. -/
theorem eOfNat_gSquaresBits (j : ℕ) (hj : j < sizeBits) :
    eOfNat (gSquaresBits.getD j 0) = gen ^ 2 ^ j := by
  rw [eOfNat, ofBits_gSquaresBits j hj, ofK_pow]
  rfl

end
end LeanVM.Guest.Value
