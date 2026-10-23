/-
  LeanVMTests.Protocol.BitProductTable

  Controls for tables that factor over the index bits: the coordinate order, the geometric
  table, and the Lagrange basis as one of them.
-/

module

public import LeanVM.Protocol.ToCompPoly.BitProductTable
public import LeanVM.Parameters.Field
meta import LeanVM.Protocol.ToCompPoly.BitProductTable
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Bit-product table controls

A table with a different factor at each coordinate detects a swap of two coordinates. The
geometric table is checked over `ℚ`, where no characteristic hides a sign, and over `K`.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly CMlPolynomialEval

@[expose] public section

/-- Coordinate 0 contributes `2` or `3`, coordinate 1 contributes `5` or `7`. -/
def factors : Fin 2 → Bool → K := fun k b ↦
  match k, b with
  | 0, false => K.ofBits 2
  | 0, true => K.ofBits 3
  | 1, false => K.ofBits 5
  | 1, true => K.ofBits 7

-- Entry `i` multiplies the factor of each bit of `i`, low bit first.
#guard bitProductTable factors = #v[(K.ofBits 2) * (K.ofBits 5), (K.ofBits 3) * (K.ofBits 5), (K.ofBits 2) * (K.ofBits 7), (K.ofBits 3) * (K.ofBits 7)]
-- Its extension is the product of the one-variable interpolants.
#guard evalMle (bitProductTable factors) #v[K.ofBits 11, K.ofBits 13] =
  ((1 - (K.ofBits 11)) * (K.ofBits 2) + (K.ofBits 11) * (K.ofBits 3)) * ((1 - (K.ofBits 13)) * (K.ofBits 5) + (K.ofBits 13) * (K.ofBits 7))
-- Mutation: the interpolants with the two coordinates swapped give another value.
#guard evalMle (bitProductTable factors) #v[K.ofBits 11, K.ofBits 13] ≠
  ((1 - (K.ofBits 13)) * (K.ofBits 2) + (K.ofBits 13) * (K.ofBits 3)) * ((1 - (K.ofBits 11)) * (K.ofBits 5) + (K.ofBits 11) * (K.ofBits 7))

/-! ## The geometric table -/

example (a : ℚ) : evalMle (powersTable a 0) #v[] = 1 := by
  rw [evalMle_powersTable]
  simp

example : evalMle (powersTable (2 : ℚ) 2) #v[3, 5] = 64 := by
  simp only [evalMle_powersTable]
  norm_num [Fin.prod_univ_succ]

example : evalMle (powersTable (2 : ℚ) 2) #v[3, 5] ≠
    evalMle (powersTable (2 : ℚ) 2) #v[5, 3] := by
  simp only [evalMle_powersTable]
  norm_num [Fin.prod_univ_succ]

#guard powersTable (K.ofBits 3 : K) 2 = #v[1, K.ofBits 3, (K.ofBits 3) ^ 2, (K.ofBits 3) ^ 3]
-- The binary expansion of the exponent: `a ^ 5 = a ^ 1 * a ^ 4`.
example (a : ℚ) : a ^ 5 = ∏ k : Fin 3, if (5 : ℕ).testBit k then a ^ 2 ^ k.val else 1 :=
  pow_eq_prod_testBit a (by decide)

/-! ## The Lagrange basis -/

-- The Lagrange basis at `w`, evaluated at `x`, is the equality kernel, symmetric in `w`, `x`.
#guard evalMle (lagrangeBasis (#v[K.ofBits 5, K.ofBits 9] : Vector K 2)) #v[K.ofBits 11, K.ofBits 13] =
  ((1 - (K.ofBits 11)) * (1 - (K.ofBits 5)) + (K.ofBits 11) * (K.ofBits 5)) * ((1 - (K.ofBits 13)) * (1 - (K.ofBits 9)) + (K.ofBits 13) * (K.ofBits 9))
#guard evalMle (lagrangeBasis (#v[K.ofBits 5, K.ofBits 9] : Vector K 2)) #v[K.ofBits 11, K.ofBits 13] =
  evalMle (lagrangeBasis (#v[K.ofBits 11, K.ofBits 13] : Vector K 2)) #v[K.ofBits 5, K.ofBits 9]

end
end LeanVMTests.Protocol
