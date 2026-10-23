/-
  LeanVM.Parameters.Field

  Lemmas about the fields `K = GF(2^64)` and `E = GF(2^192)` of `LeanVM.Spec.Field`: the limb
  view of `E` and its arithmetic.
-/

module

public import LeanVM.Spec.Field
import Mathlib.Tactic.LinearCombination

/-!
# The fields `K` and `E`

The moduli and the
limb order are transcribed from specification §2, `doc/leanvm/body/02-vm-specification.tex:6-8`
at leanVM pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, and are exactly CompPoly's `BF64` and
`BF64.Ext3` at pin `572f997390aa4fc131ef30b1186fa1dcf292ca10`:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      BF64.basePoly_eq, BF64.basePoly_irreducible
E = K[y]/(y^3 + y + 1),  |E| = 2^192         BF64.ext3Params_poly, BF64.ext3Poly_irreducible
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`
(`crates/primitives/src/field/gf2_64.rs:16-19`, `F64`); `E` is a `Vector K 3` whose limb `i` is
the coefficient of `y^i`. The definitions are in `LeanVM.Spec.Field`, abbreviations or one-line
definitions over those CompPoly declarations; this module proves lemmas about them. The limb
arithmetic under "Load-bearing lemmas" (`add_limbs`,
`mul_limbs`, the `K`-word lemmas) is what the opcode tables read their result
coordinates with: a sum is bitwise `XOR` limb by limb, a product is the twelve limb products
folded by `y^3 = y + 1`.

## Wrong readings excluded

* `CompPoly.Fields.Binary.Tower` presents `GF(2^64)` with a different bit encoding; it is never
  used.
* Natural-number casts follow characteristic two: `2 : K = 0`. Wire words use
  `K.ofBits`; `K.ofBits 2` is `x` (bit 1).
* `ofK a` occupies the `y^0` limb only. "`x ∈ K`" is the predicate `IsInK`; a canonical 128-bit
  word, the cell shape BLAKE2S consumes, is `IsCanonical128`.

## Computability and the module system

The section is `@[expose]`d so that definitions unfold downstream. From a `module` file, the
kernel reduces `K` arithmetic, `E.ofLimbs`, `E.limb`, and the two predicates on literal words
(`decide +kernel`), which is why `E.ofLimbs` is a literal vector. It does not reduce CompPoly's
`Ext.ofFn`, hence not `ofK`, `y`, `+`, `*`, or `DecidableEq E`: core's `Array.ofFn` is not
`@[expose]`d, and a `module` importer sees only exposed bodies. Executable checks of those go
through compiled evaluation (`#guard` under `meta import`), and any later-layer plan to decide an
execution by `decide` depends on CompPoly or core lifting this.

## Clean's field interface

Clean's `FiniteField K` is `instFiniteFieldK` in `LeanVM.Parameters.CleanField`.
Clean now uses Lean's module system. The Clean bridge is a separate module, keeping the field carrier independent of that
interface for the Semantics layer.
-/

namespace LeanVM.Parameters

@[expose] public section

open CompPoly.Extension

/-! ## The fields -/

/-- A proof-only enumeration of `K`; executable code uses its explicit bit coordinates. -/
noncomputable instance : Fintype K := Fintype.ofFinite K

/-- The defining relation of `E`: `y^3 = y + 1`. -/
theorem y_pow_three : y ^ 3 = y + 1 := BF64.ext3Gen_pow_three

/-- Hexadecimal rendering `E(0x<c2><c1><c0>)`, the Python verifier's `E.__repr__`
(`python-verifier/verifier.py:177`). -/
instance : ToString E :=
  ⟨fun x ↦
    let hi := (x.limb 2).toBitVec.toHex
    let mid := (x.limb 1).toBitVec.toHex
    let lo := (x.limb 0).toBitVec.toHex
    s!"E(0x{hi}{mid}{lo})"⟩

/-! ## Load-bearing lemmas -/

/-- Words with the same limbs are equal. -/
theorem E.ext {x z : E} (h : ∀ i, x.limb i = z.limb i) : x = z := Ext.ext h

/-- The limbs of `E.ofLimbs c0 c1 c2` are `c0, c1, c2`. -/
@[simp] theorem limb_ofLimbs (c0 c1 c2 : K) (i : Fin 3) :
    (E.ofLimbs c0 c1 c2).limb i = ![c0, c1, c2] i := by
  fin_cases i <;> rfl

/-- `ofK a` has `a` in limb `0` and zero elsewhere. -/
@[simp] theorem limb_ofK (a : K) (i : Fin 3) :
    (ofK a).limb i = if (i : ℕ) = 0 then a else 0 :=
  Ext.coeff_ofBase (P := BF64.ext3Params) a i

/-- `ofK` is injective. -/
theorem ofK_injective : Function.Injective ofK := by
  intro a b h
  simpa using congrArg (fun z : E ↦ z.limb 0) h

/-- Every word is its limbs in the basis `1, y, y²`. -/
theorem E.eq_sum_limbs (x : E) :
    x = ofK (x.limb 0) + ofK (x.limb 1) * y + ofK (x.limb 2) * y ^ 2 := by
  apply Ext.toQuot_injective
  have hx : Ext.toQuot x = ∑ i : Fin 3,
      algebraMap K (AdjoinRoot BF64.ext3Params.poly) (x.limb i) *
        Ext.rt BF64.ext3Params ^ (i : ℕ) := rfl
  rw [hx, Fin.sum_univ_three]
  simp [y]

/-- `E.ofLimbs c0 c1 c2 = c0 + c1·y + c2·y²`. -/
theorem ofLimbs_eq (c0 c1 c2 : K) :
    E.ofLimbs c0 c1 c2 = ofK c0 + ofK c1 * y + ofK c2 * y ^ 2 := by
  conv_lhs => rw [E.eq_sum_limbs (E.ofLimbs c0 c1 c2)]
  simp

/-- Rebuilding a word from its limbs is the identity. -/
theorem ofLimbs_limb (x : E) : E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) = x :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- `IsInK` is exactly the image of `ofK`. -/
theorem isInK_iff (x : E) : IsInK x ↔ ∃ a, x = ofK a := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨x.limb 0, E.ext fun i ↦ by fin_cases i <;> simp [h1, h2]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨by simp, by simp⟩

/-- Limb `i` of a sum is the sum of the limbs (CompPoly's `Ext.coeff_add`). -/
theorem limb_add (x z : E) (i : Fin 3) : (x + z).limb i = x.limb i + z.limb i :=
  Ext.coeff_add x z i

/-- Limb `i` of the zero word is zero. -/
theorem limb_zero (i : Fin 3) : (0 : E).limb i = 0 :=
  Ext.coeff_zero (P := BF64.ext3Params) i

/-- `ofK` preserves sums: it is `algebraMap K E`. -/
theorem ofK_add (a b : K) : ofK (a + b) = ofK a + ofK b := map_add (algebraMap K E) a b

/-- `ofK` preserves products: it is `algebraMap K E`. -/
theorem ofK_mul (a b : K) : ofK (a * b) = ofK a * ofK b := map_mul (algebraMap K E) a b

/-- `ofK a` is the word with limbs `(a, 0, 0)`. -/
theorem ofK_eq_ofLimbs (a : K) : ofK a = E.ofLimbs a 0 0 :=
  E.ext fun i ↦ by fin_cases i <;> simp

/-- A word with zero upper limbs lies in `K`. -/
theorem isInK_ofLimbs (c : K) : IsInK (E.ofLimbs c 0 0) := ⟨by simp, by simp⟩

/-- A word in `K` is its low limb with zeros above. -/
theorem ofLimbs_of_isInK {x : E} (h : IsInK x) : E.ofLimbs (x.limb 0) 0 0 = x :=
  calc E.ofLimbs (x.limb 0) 0 0 = E.ofLimbs (x.limb 0) (x.limb 1) (x.limb 2) := by rw [h.1, h.2]
    _ = x := ofLimbs_limb x

/-- A single-limb word is zero exactly when its limb is. -/
theorem ofLimbs_eq_zero_iff (c : K) : E.ofLimbs c 0 0 = 0 ↔ c = 0 := by
  constructor
  · intro h
    have := congrArg (fun z : E ↦ z.limb 0) h
    simpa only [limb_ofLimbs, limb_zero, Matrix.cons_val_zero] using this
  · rintro rfl
    exact E.ext fun i ↦ by rw [limb_zero]; fin_cases i <;> simp

/-- The sum of two words, limb by limb: addition in `E` is bitwise `XOR` in each limb, never
integer addition with carries (the `XOR` table's result coordinates, specification §7.1). -/
theorem add_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 + E.ofLimbs b0 b1 b2 = E.ofLimbs (a0 + b0) (a1 + b1) (a2 + b2) :=
  E.ext fun i ↦ by rw [limb_add]; fin_cases i <;> simp

/-- The product of two words, limb by limb: the twelve products over the nine limb pairs,
folded by `y^3 = y + 1` into three lanes (the `MUL_NATIVE` table's result coordinates,
specification §7.2; the pinned Rust's `TOWER_LANES`). -/
theorem mul_limbs (a0 a1 a2 b0 b1 b2 : K) :
    E.ofLimbs a0 a1 a2 * E.ofLimbs b0 b1 b2 =
      E.ofLimbs (a0 * b0 + a1 * b2 + a2 * b1)
        (a0 * b1 + a1 * b0 + a1 * b2 + a2 * b1 + a2 * b2)
        (a0 * b2 + a1 * b1 + a2 * b0 + a2 * b2) := by
  simp only [ofLimbs_eq, ofK_add, ofK_mul]
  -- The product is `p₀ + p₁·y + p₂·y² + p₃·y³ + p₄·y⁴`; `y³ = y + 1` folds `p₃` and `p₄`.
  linear_combination (ofK a1 * ofK b2 + ofK a2 * ofK b1 + ofK a2 * ofK b2 * y) * y_pow_three

end
end LeanVM.Parameters
