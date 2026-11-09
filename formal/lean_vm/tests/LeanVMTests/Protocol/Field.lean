module

public import LeanVM.Protocol.Field
public import LeanVM.Protocol.ToCompPoly.Multilinear
meta import LeanVM.Protocol.Field
meta import LeanVM.Parameters.Field
meta import CompPoly.Multilinear.Basic

/-!
# Protocol field tests: samplers and the inner-product oracle

Compiled checks (`#guard`) that the inner-product oracle on a two-variable column answers
`⟨W, q⟩` for the equality kernel, on cube points and off them, and for a weight that is no
equality kernel, with a mutated column; code-generation probes that the two samplers have
compiler IR (a sampler built from `Fintype` would be noncomputable, or would enumerate the
field); that scalar messages have an oracle interface; and the cardinality of `E`.
-/

namespace LeanVMTests.Protocol

open LeanVM.Parameters LeanVM.Protocol CompPoly OracleComp

public section

/-! ## The inner-product oracle -/

/-- The column `[1, x, x + 1, x²]` on two variables, written by its `K.ofBits` words:
`q(0,0) = 1`, `q(1,0) = x`, `q(0,1) = x + 1`, `q(1,1) = x²`. -/
def col : Column 2 := ⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 4]⟩

/-- The oracle's answer, typed as the field element it is. -/
def answer (q : Column 2) (W : Weight E 2) : E := OracleInterface.answer q W

-- On the cube the equality kernel is an indicator: the answer is the table entry.
#guard answer col (eqWeight #v[ofK 0, ofK 0]) = ofK 1
#guard answer col (eqWeight #v[ofK 1, ofK 0]) = ofK (K.ofBits 2)
#guard answer col (eqWeight #v[ofK 0, ofK 1]) = ofK (K.ofBits 3)
#guard answer col (eqWeight #v[ofK 1, ofK 1]) = ofK (K.ofBits 4)
-- Off the cube it is the multilinear extension: at `(y, 0)` the value is `1 + y·(1 + x)` in
-- characteristic two (`(1 - y)·1 + y·x`, with `-1 = 1`), and `1 + x` is the word `3`.
#guard answer col (eqWeight #v[y, ofK 0]) = ofK 1 + ofK (K.ofBits 3) * y
-- And it agrees with CompPoly's evaluation of the lifted table.
#guard answer col (eqWeight #v[y, y ^ 2]) =
  CMlPolynomialEval.evalMle (CMlPolynomialEval.map (algebraMap K E) col.values) #v[y, y ^ 2]
-- Mutation: a different column answers differently at the same point.
#guard answer ⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 5]⟩ (eqWeight #v[y, y ^ 2]) ≠
  answer col (eqWeight #v[y, y ^ 2])

/-- A weight that is no equality kernel: `1` on every cube point, so the answer is the sum of
the column's cells. Its extension is the constant `1`. -/
def sumWeight : Weight E 2 where
  onCube := Vector.replicate 4 1
  mle := fun _ ↦ 1
  mle_eq := fun r ↦ (evalMle_replicate 1 r).symm

-- The sum of the cells `1, x, x + 1, x²` is `x²`, the word `4`; the mutated column sums to the
-- word `5`.
#guard answer col sumWeight = ofK (K.ofBits 4)
#guard answer ⟨#v[1, K.ofBits 2, K.ofBits 3, K.ofBits 5]⟩ sumWeight = ofK (K.ofBits 5)

/-- The answer to the equality kernel is the column's extension, on the cube and off it. -/
example (p : Vector E 2) :
    OracleInterface.answer col (eqWeight p) =
      CMlPolynomialEval.eval₂Mle col.values (algebraMap K E) p :=
  answer_eqWeight col p

/-! ## Samplers have compiler IR -/

/-- Compiles only if the `K` sampler is computable: a sampler through `Fintype` would not be. -/
def sampleK : ProbComp K := $ᵗ K

/-- Compiles only if the `E` sampler is computable. -/
def sampleE : ProbComp E := $ᵗ E

/-! ## Cardinality -/

example : Fintype.card E = 2 ^ 192 := card_E

end
end LeanVMTests.Protocol
