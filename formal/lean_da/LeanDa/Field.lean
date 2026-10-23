module

public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Algebra.Algebra.ZMod

/-!
# The fields `K = GF(2^64)` and `E = GF(2^192)`

CompPoly's carriers, as `formal/lean_vm/LeanVM/Spec/Field.lean` uses them: `K` is `BF64`, a
`BitVec 64` whose bit `i` is the coefficient of `x^i` in `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`
(`crates/primitives/src/field/gf2_64.rs`, `F64`), and `E` is `BF64.Ext3 = K[y]/(y^3 + y + 1)`
(`F192`, limbs `c0 + c1·y + c2·y^2`). CompPoly proves both moduli irreducible.

The domain of the Reed-Solomon code is spanned over `GF(2)` by `e_c = x^c`
(`doc/leanvm/body/d-novel-basis.tex`, the basis of Annex D), so its point of index `b` is the
element whose bits are `b` (`point`). The novel basis of CompPoly's `AdditiveNTT` is built on
the first sixteen of them (`basis`).
-/

namespace LeanDa

@[expose] public section

/-- `K = GF(2^64)` (`F64`). -/
abbrev K : Type := BF64

/-- `E = K[y]/(y^3 + y + 1)` (`F192`). -/
abbrev E : Type := BF64.Ext3

/-- The element of `K` whose bits are `n`, reduced modulo `2^64`: the wire encoding of a word. -/
def K.ofBits (n : ℕ) : K := BF64.ofBitVec (BitVec.ofNat 64 n)

/-- An enumeration of `K` through its bits, for proofs only: compiled, it would list `2^64`
elements when a program starts. -/
noncomputable instance : Fintype K := Fintype.ofEquiv (Fin (2 ^ 64)) BF64.equivFin.symm

/-- `K` is a `GF(2)`-algebra, being of characteristic two. -/
instance : Algebra (ZMod 2) K := ZMod.algebra K 2

instance : Fact (Nat.Prime (ringChar (ZMod 2))) := ⟨by rw [ZMod.ringChar_zmod_n]; exact Nat.prime_two⟩

instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩

/-- The embedding `K ↪ E` as the `y^0` limb. -/
abbrev ι : K →+* E := algebraMap K E

/-- The point of index `b` of an additive domain: `Σ_c b_c e_c` with `e_c = x^c`. -/
def point (b : ℕ) : K := K.ofBits b

/-- `e_c = x^c` for `c < 16`, the start of the basis of Annex D. -/
def basis (c : Fin 16) : K := K.ofBits (2 ^ (c : ℕ))

/-- Uniform sampling of `K` through its bits. -/
instance : SampleableType K := SampleableType.ofEquiv BF64.equivFin.symm

/-- Uniform sampling of `E` limb by limb. -/
instance : SampleableType E := SampleableType.ofEquiv (CompPoly.Extension.Ext.equivFn _).symm

end

end LeanDa
