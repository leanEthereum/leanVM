/-
  LeanVM.Parameters.Field

  Lemmas about the fields `K = GF(2^64)` and `E = GF(2^128)` of `Statement.Field`: the limb
  view of `E` and its arithmetic.
-/

module

public import Statement.Field
public import FastFields.QuadExt
public import FastFields.FieldWords
import Mathlib.Tactic.LinearCombination

/-!
# The fields `K` and `E`

The moduli and the limb order are transcribed from specification §2,
`doc/leanvm/body/02-vm-specification.tex`; `K` is CompPoly's `BF64`
and `E` CompPoly's extension framework at `Statement.Field`'s parameters `eParams`:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      BF64.basePoly_eq, BF64.basePoly_irreducible
E = K[y]/(y^2 + x·y + 1),  |E| = 2^128       eParams_poly, ePoly_irreducible (Statement.Field)
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`
(`crates/primitives/src/field/gf2_64.rs`, `F64`); `E` is a `Vector K 2` whose limb `i` is
the coefficient of `y^i` (`crates/primitives/src/field/gf2_64x2.rs`, `F128`). The definitions are
in `Statement.Field`; this module proves lemmas about them. The limb arithmetic under
"Load-bearing lemmas" (`add_limbs`, `mul_limbs`, the `K`-word lemmas) is what the opcode tables
read their result coordinates with: a sum is bitwise `XOR` limb by limb, a product is the four
limb products folded by `y^2 = x·y + 1`.

## Wrong readings excluded

* `CompPoly.Fields.Binary.Tower` presents `GF(2^64)` with a different bit encoding; it is never
  used.
* Natural-number casts follow characteristic two: `2 : K = 0`. Wire words use
  `K.ofBits`; `K.ofBits 2` is `x` (bit 1), the generator `g`.
* `ofK a` occupies the `y^0` limb only. "`x ∈ K`" is the predicate `IsInK`.
* The modulus is `y^2 + x·y + 1`, not `y^2 + y + 1`: the `y` limb of a product carries
  `x·a₁b₁` (`mul_limbs`), the `g`-power on the `MUL_NATIVE` table's product coordinate.

## Computability and the module system

The section is `@[expose]`d so that definitions unfold downstream. From a `module` file, the
kernel reduces `K` arithmetic, `E.ofLimbs`, `E.limb`, and `IsInK` on literal words
(`decide +kernel`), which is why `E.ofLimbs` is a literal vector. It does not reduce CompPoly's
`Ext.ofFn`, hence not `ofK`, `y`, `+`, `*`, or `DecidableEq E`: core's `Array.ofFn` is not
`@[expose]`d, and a `module` importer sees only exposed bodies. Executable checks of those go
through compiled evaluation (`#guard` under `meta import`).

## Clean's field interface

Clean's `FiniteField K` is `instFiniteFieldK` in `LeanVM.Parameters.CleanField`, a separate
module, keeping the field carrier independent of that interface for the Semantics layer.
-/

namespace LeanVM.Parameters

@[expose] public section

open CompPoly.Extension

/-! ## The fields -/

/-- A proof-only enumeration of `K`; executable code uses its explicit bit coordinates. -/
noncomputable instance instFintypeK : Fintype K := Fintype.ofFinite K

/-- `E` has characteristic two, as its base field does. -/
instance instCharPE : CharP E 2 := charP_of_injective_algebraMap' (R := K) (A := E) 2

/-- The adjoined root `y` of `y^2 + x·y + 1`. -/
def y : E := Ext.gen

/-- The defining relation of `E`: `y^2 = x·y + 1`, with `x = g`. -/
theorem y_sq : y ^ 2 = ofK g * y + 1 := by
  have h : Polynomial.aeval y ePoly = 0 := by rw [← eParams_poly]; exact Ext.aeval_gen_poly
  simp only [ePoly, map_add, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, map_one,
    Ext.algebraMap_eq_ofBase] at h
  rw [← sub_eq_zero, CharTwo.sub_eq_add, ← add_assoc]
  exact h

/-- Hexadecimal rendering `E(0x<c1><c0>)`. -/
instance : ToString E :=
  ⟨fun x ↦
    let hi := (x.limb 1).toBitVec.toHex
    let lo := (x.limb 0).toBitVec.toHex
    s!"E(0x{hi}{lo})"⟩

/-! ## Load-bearing lemmas -/

/-- Words with the same limbs are equal. -/
theorem E.ext {x z : E} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

/-- The limbs of `E.ofLimbs c0 c1` are `c0, c1`. -/
@[simp] theorem limb_ofLimbs (c0 c1 : K) (i : Fin 2) :
    (E.ofLimbs c0 c1).limb i = ![c0, c1] i := by
  fin_cases i <;> rfl

/-- `ofK a` has `a` in limb `0` and zero in limb `1`. -/
@[simp] theorem limb_ofK (a : K) (i : Fin 2) :
    (ofK a).limb i = if (i : ℕ) = 0 then a else 0 :=
  Ext.coeff_ofBase (P := eParams) a i

/-- `ofK` is injective. -/
theorem ofK_injective : Function.Injective ofK := by
  intro a b h
  simpa using congrArg (fun z : E ↦ z.limb 0) h

/-- Every word is its limbs in the basis `1, y`. -/
theorem E.eq_sum_limbs (x : E) : x = ofK (x.limb 0) + ofK (x.limb 1) * y := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 2,
      algebraMap K (AdjoinRoot eParams.poly) (x.limb i) * Ext.rt eParams ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_two]
  simp [y]

/-- `E.ofLimbs c0 c1 = c0 + c1·y`. -/
theorem ofLimbs_eq (c0 c1 : K) : E.ofLimbs c0 c1 = ofK c0 + ofK c1 * y := by
  conv_lhs => rw [E.eq_sum_limbs (E.ofLimbs c0 c1)]
  simp

/-- Rebuilding a word from its limbs is the identity. -/
theorem ofLimbs_limb (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) = x :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- `IsInK` is exactly the image of `ofK`. -/
theorem isInK_iff (x : E) : IsInK x ↔ ∃ a, x = ofK a := by
  constructor
  · intro h1
    exact ⟨x.limb 0, E.ext fun i ↦ by fin_cases i <;> simp [show x.limb 1 = 0 from h1]⟩
  · rintro ⟨a, rfl⟩
    show (ofK a).limb 1 = 0
    simp

/-- Limb `i` of a sum is the sum of the limbs (CompPoly's `Ext.coeff_add`). -/
theorem limb_add (x z : E) (i : Fin 2) : (x + z).limb i = x.limb i + z.limb i :=
  Ext.coeff_add x z i

/-- Limb `i` of the zero word is zero. -/
theorem limb_zero (i : Fin 2) : (0 : E).limb i = 0 :=
  Ext.coeff_zero (P := eParams) i

/-- `ofK` preserves sums: it is `algebraMap K E`. -/
theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- `ofK` preserves products: it is `algebraMap K E`. -/
theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- `ofK` preserves zero. -/
theorem ofK_zero : ofK 0 = 0 := map_zero (algebraMap K E)

/-- `ofK` preserves one. -/
theorem ofK_one : ofK 1 = 1 := map_one (algebraMap K E)

/-- `ofK` preserves powers. -/
theorem ofK_pow (a : K) (n : ℕ) : ofK (a ^ n) = ofK a ^ n := map_pow (algebraMap K E) a n

/-- `ofK` preserves differences. -/
theorem ofK_sub (a b : K) : ofK (a - b) = ofK a - ofK b := map_sub (algebraMap K E) a b

/-- `ofK a` is the word with limbs `(a, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with a zero upper limb lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0) := by
  show (E.ofLimbs c 0).limb 1 = 0
  simp

/-- A word in `K` is its low limb with zero above. -/
theorem ofLimbs_of_isInK {x : E} (h : IsInK x) : E.ofLimbs (x.limb 0) 0 = x :=
  calc E.ofLimbs (x.limb 0) 0 = E.ofLimbs (x.limb 0) (x.limb 1) := by rw [show x.limb 1 = 0 from h]
    _ = x := ofLimbs_limb x

/-- A single-limb word is zero exactly when its limb is. -/
theorem ofLimbs_eq_zero_iff (c : K) : E.ofLimbs c 0 = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simpa only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero] using this
  · rintro rfl
    exact E.ext fun i ↦ by rw [limb_zero]; fin_cases i <;> simp

/-- The sum of two words, limb by limb: addition in `E` is bitwise `XOR` in each limb, never
integer addition with carries (the `XOR` table's result coordinates, specification §7.1). -/
theorem add_limbs (a0 a1 b0 b1 : K) :
    E.ofLimbs a0 a1 + E.ofLimbs b0 b1 = E.ofLimbs (a0 + b0) (a1 + b1) :=
  E.ext fun i ↦ by rw [limb_add]; fin_cases i <;> simp

/-- The product of two words, limb by limb: the four limb products, `a₁b₁·y^2` folded by
`y^2 = x·y + 1` into both lanes (the `MUL_NATIVE` table's result coordinates, specification §7.2;
`TOWER_LANES`, `crates/lean_vm_core/src/tables.rs`). -/
theorem mul_limbs (a0 a1 b0 b1 : K) :
    E.ofLimbs a0 a1 * E.ofLimbs b0 b1 =
      E.ofLimbs (a0 * b0 + a1 * b1) (a0 * b1 + a1 * b0 + g * (a1 * b1)) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y²`; `y² = x·y + 1` folds `p₂` into both lanes.
  linear_combination (ofK a1 * ofK b1) * y_sq

/-! ## Words of `K`

`K.ofBits` is injective below `2^64`, turns `xor` into `+`, and the word with bits `v` is
`Σ_c v_c · x^c`. -/

/-- `K.ofBits 0 = 0`. -/
theorem K.ofBits_zero : K.ofBits 0 = 0 := rfl

/-- `K.ofBits 1 = 1`. -/
theorem K.ofBits_one : K.ofBits 1 = 1 := rfl

/-- `K.ofBits` reads only the low `64` bits. -/
theorem K.ofBits_mod (n : ℕ) : K.ofBits (n % 2 ^ 64) = K.ofBits n :=
  congrArg BF64.ofBitVec (BitVec.eq_of_toNat_eq (by simp))

/-- A word below `2^64` is read back exactly. -/
theorem K.toNat_ofBits {n : ℕ} (hn : n < 2 ^ 64) : (K.ofBits n).toBitVec.toNat = n := by
  simpa [K.ofBits] using hn

/-- Every element is the word of its bits. -/
theorem K.ofBits_toNat (a : K) : K.ofBits a.toBitVec.toNat = a := by
  apply BF64.ext
  simp [K.ofBits]

/-- Words below `2^64` are distinct field elements. -/
theorem K.ofBits_injOn : Set.InjOn K.ofBits {n | n < 2 ^ 64} := by
  intro a ha b hb h
  rw [← K.toNat_ofBits ha, ← K.toNat_ofBits hb, h]

/-- A word below `2^64` is zero only when it is `0`. -/
theorem K.ofBits_eq_zero_iff {n : ℕ} (hn : n < 2 ^ 64) : K.ofBits n = 0 ↔ n = 0 :=
  ⟨fun h ↦ K.ofBits_injOn (show n < 2 ^ 64 from hn) (show 0 < 2 ^ 64 by norm_num) h,
    fun h ↦ h ▸ K.ofBits_zero⟩

/-- Below `2^i`, adding `2^i` sets a bit that is clear: it is the exclusive or. -/
theorem two_pow_add_eq_xor {i v : ℕ} (hv : v < 2 ^ i) : 2 ^ i + v = 2 ^ i ^^^ v := by
  have h := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [mul_one] at h
  rw [h]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hj : i = j
  · subst hj
    simp [Nat.testBit_lt_two_pow hv]
  · simp [hj]

/-- Sum in `K` is bitwise exclusive or of words. -/
theorem K.ofBits_xor (a b : ℕ) : K.ofBits (a ^^^ b) = K.ofBits a + K.ofBits b := by
  simp only [K.ofBits, BitVec.ofNat_xor]
  rfl

/-- `x_{2^i + v} = x^i + x_v` for `v < 2^i`. -/
theorem K.ofBits_two_pow_add {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits (2 ^ i + v) = K.ofBits (2 ^ i) + K.ofBits v := by
  rw [two_pow_add_eq_xor hv, K.ofBits_xor]

/-- The word with bits `v` is `Σ_c v_c · x^c`. -/
theorem K.ofBits_eq_sum {i v : ℕ} (hv : v < 2 ^ i) :
    K.ofBits v = ∑ c ∈ Finset.range i, if v.testBit c then K.ofBits (2 ^ c) else 0 := by
  induction i generalizing v with
  | zero =>
    obtain rfl : v = 0 := by simpa using hv
    simp [K.ofBits_zero]
  | succ i ih =>
    rw [Finset.sum_range_succ]
    by_cases hb : v.testBit i
    · have hlt : v - 2 ^ i < 2 ^ i := by
        have := Nat.ge_two_pow_of_testBit hb
        rw [pow_succ] at hv
        omega
      have hv' : v = 2 ^ i + (v - 2 ^ i) := by
        have := Nat.ge_two_pow_of_testBit hb
        omega
      have hbits : ∀ c < i, v.testBit c = (v - 2 ^ i).testBit c := by
        intro c hc
        conv_lhs => rw [hv']
        exact Nat.testBit_two_pow_add_gt hc _
      have hb' : (2 ^ i + (v - 2 ^ i)).testBit i = true := by rw [← hv']; exact hb
      rw [hv', K.ofBits_two_pow_add hlt, ih hlt, hb']
      simp only [ite_true]
      rw [add_comm]
      congr 1
      refine Finset.sum_congr rfl fun c hc ↦ ?_
      rw [← hv', hbits c (Finset.mem_range.mp hc)]
    · have hlt : v < 2 ^ i := by
        by_contra h
        have h1 : 2 ^ i ≤ v := not_lt.mp h
        have : v.testBit i = true := by
          have hv2 : v - 2 ^ i < 2 ^ i := by rw [pow_succ] at hv; omega
          have := Nat.testBit_two_pow_add_eq (v - 2 ^ i) i
          rw [Nat.add_sub_cancel' h1, Nat.testBit_lt_two_pow hv2] at this
          simpa using this
        exact hb this
      simp only [Bool.not_eq_true] at hb
      rw [ih hlt, hb]
      simp

end
end LeanVM.Parameters
