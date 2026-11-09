module

public import CompPoly.Fields.Binary.BF64
public import CompPoly.Fields.Binary.AdditiveNTT.NovelPolynomialBasis
public import VCVio.OracleComp.Constructions.SampleableType
public import Mathlib.Algebra.Algebra.ZMod
public import Statement.LeanDa

/-!
# The fields `K = GF(2^64)` and `E = GF(2^192)`

CompPoly's carriers, as `formal/lean_vm/Statement/Field.lean` uses them: `K` is `BF64`, a
`BitVec 64` whose bit `i` is the coefficient of `x^i` in `GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)`
(`crates/primitives/src/field/gf2_64.rs`, `F64`), and `E` is `BF64.Ext3 = K[y]/(y^3 + y + 1)`
(`F192`, limbs `c0 + c1·y + c2·y^2`). CompPoly proves both moduli irreducible.

The domain of the Reed-Solomon code is spanned over `GF(2)` by `e_c = x^c`
(`doc/leanvm/body/d-novel-basis.tex`, the basis of Annex D), so its point of index `b` is the
element whose bits are `b` (`point`). The novel basis of CompPoly's `AdditiveNTT` is built on
the first sixteen of them (`basis`).

Part of `lean_da`, which instantiates Benedikt Wagner's framework for erasure code commitments
(`PqDas`, ported from https://github.com/b-wagn/fv-pq-da) with LeanDA.
-/

namespace LeanDa

@[expose] public section

instance : Fact (Nat.Prime (ringChar (ZMod 2))) := ⟨by rw [ZMod.ringChar_zmod_n]; exact Nat.prime_two⟩

instance : Fact (Fintype.card (ZMod 2) = 2) := ⟨ZMod.card 2⟩

end

end LeanDa
