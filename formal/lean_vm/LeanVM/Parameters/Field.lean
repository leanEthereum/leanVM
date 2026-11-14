/-
  LeanVM.Parameters.Field

  Lemmas about the fields `K = GF(2^64)` and `E = GF(2^128)` of `Statement.Field`: the limb
  view of `E` and its arithmetic.
-/

module

public import Statement.Field
public import Statement.Fast.QuadExt
public import Statement.Fast.FieldWords
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
`TOWER_LANES`, `crates/leanvm_core/src/tables.rs`). -/
theorem mul_limbs (a0 a1 b0 b1 : K) :
    E.ofLimbs a0 a1 * E.ofLimbs b0 b1 =
      E.ofLimbs (a0 * b0 + a1 * b1) (a0 * b1 + a1 * b0 + g * (a1 * b1)) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y²`; `y² = x·y + 1` folds `p₂` into both lanes.
  linear_combination (ofK a1 * ofK b1) * y_sq

end
end LeanVM.Parameters
