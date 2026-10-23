/-
  LeanVM.Spec.Field

  The fields of leanVM: `K = GF(2^64)`, `E = GF(2^192)` with its limb view, and the generator `g`.
-/

module

public import CompPoly.Fields.Binary.BF64
public import LeanVM.Spec.Fast.CubicExt
public import LeanVM.Spec.Fast.FieldWords

/-!
# The fields

Specification §2 (`doc/leanvm/body/02-vm-specification.tex:6-12`, leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`), on CompPoly's computable carriers:

```text
K = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)      CompPoly's BF64
E = K[y]/(y^3 + y + 1)                       CompPoly's BF64.Ext3
g = x                                        a generator of K^× (order 2^64 - 1)
```

`K` wraps a `BitVec 64` whose bit `i` is the coefficient of `x^i`; `E` is a `Vector K 3` whose
limb `i` is the coefficient of `y^i`. Natural-number casts follow characteristic two
(`2 : K = 0`); wire words go through `K.ofBits`. The two `Fast` imports only make the compiled
arithmetic fast (`@[csimp]`); they change no definition.
-/

namespace LeanVM.Parameters

@[expose] public section

open CompPoly.Extension

/-- `K = GF(2^64)`, CompPoly's `BF64`: a wrapper of `BitVec 64` with bit `i` the
coefficient of `x^i`. -/
abbrev K : Type := BF64

/-- Decode a polynomial-basis word, reducing its integer representation modulo `2^64`.
This is a wire encoding, distinct from the characteristic-two natural-number cast. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- Decide equality through bit coordinates, keeping kernel comparisons of computed words
free of the dependent transport introduced by the upstream derived instance. -/
instance instDecidableEqK : DecidableEq K := fun a b ↦
  decidable_of_iff (a.toBitVec = b.toBitVec) BF64.toBitVec_injective.eq_iff

/-- `E = K[y]/(y^3 + y + 1)`, CompPoly's `BF64.Ext3`: a `Vector K 3` in limb order
`c0 + c1·y + c2·y²`. -/
abbrev E : Type := BF64.Ext3

/-- The adjoined root `y` of `y^3 + y + 1`. -/
def y : E := BF64.ext3Gen

/-! ## Limbs -/

/-- The embedding `K ↪ E` as the `y^0` limb; it is `algebraMap K E` by `rfl`. -/
abbrev ofK (a : K) : E := Ext.ofBase a

/-- Limb `i` of a word: the coefficient of `y^i`. -/
abbrev E.limb (x : E) (i : Fin 3) : K := Ext.coeff x i

/-- The word `c0 + c1·y + c2·y²`, as the literal limb vector. -/
def E.ofLimbs (c0 c1 c2 : K) : E := Ext.ofVector #v[c0, c1, c2]

/-- A word lies in `K`: its `y` and `y²` limbs are zero. -/
def IsInK (x : E) : Prop := x.limb 1 = 0 ∧ x.limb 2 = 0

/-- A canonical 128-bit word: its `y²` limb is zero. -/
def IsCanonical128 (x : E) : Prop := x.limb 2 = 0

/-- The canonical word of a two-limb cell, `c0 + c1·y`: the cell shape `BLAKE2S` consumes. -/
def E.ofCell (v : Vector K 2) : E := E.ofLimbs v[0] v[1] 0

instance : DecidablePred IsInK :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 1 = 0 ∧ x.limb 2 = 0))

instance : DecidablePred IsCanonical128 :=
  fun x ↦ inferInstanceAs (Decidable (x.limb 2 = 0))

/-! ## The generator -/

/-- `g = x`, the word `0x2` (`crates/primitives/src/field/gf2_64.rs:25`, `F64::G = F64(2)`;
`python-verifier/verifier.py:182`, `GEN = E(2)`). Its order `2^64 - 1` is proved
(`orderOf_g`), not assumed. -/
def g : K := K.ofBits 0x2

/-- Exponent addressing: index `i` is the address `g ^ i`. -/
abbrev gpow (i : ℕ) : K := g ^ i

end
end LeanVM.Parameters
