/-
  LeanVMTests.Protocol.ClaimWeights

  Controls for column claims as weighted claims, on the toy instance.
-/

import LeanVM.Protocol.ClaimWeights
import LeanVM.Protocol.Spine.Toy

/-!
# Claim weight controls

On the toy instance, whose layout is written by hand and knows nothing of aligned blocks: the
weight of a claim on a column, paired with the stack, is the column's evaluation at the claim's
point; with another column's selector it is not; and the closed form of the weight's extension
is the extension of its cube values. A plain file, so `#guard` evaluates the compiled
definitions.
-/

namespace LeanVMTests.Protocol.ClaimWeights

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Toy CompPoly CMlPolynomialEval

/-- A point of `E` outside `K`. -/
def u : E := E.ofLimbs 0 1 0

/-- The claim's point on a column of the toy, which has one variable. -/
def z : Vector E 1 := #v[u]

/-- A stack that is not the honest one. -/
def arbitrary : Column 3 := ⟨#v[K.ofBits 9, K.ofBits 8, K.ofBits 7, K.ofBits 6, K.ofBits 5, K.ofBits 4, K.ofBits 3, K.ofBits 2]⟩

-- The weight of a claim on column `c` at `z`, paired with the stack, is column `c` at `z`.
#guard (List.finRange 3).all fun c ↦
  (eqWeight (toy.layout.extend ⟨0, c⟩ z)).pair (algebraMap K E) honest.values =
    eval₂Mle (toy.column honest ⟨0, c⟩).values (algebraMap K E) z
#guard (List.finRange 3).all fun c ↦
  (eqWeight (toy.layout.extend ⟨0, c⟩ z)).pair (algebraMap K E) arbitrary.values =
    eval₂Mle (toy.column arbitrary ⟨0, c⟩).values (algebraMap K E) z

-- Mutation: the weight of column 1 does not evaluate column 2.
#guard (eqWeight (toy.layout.extend ⟨0, 1⟩ z)).pair (algebraMap K E) arbitrary.values ≠
  eval₂Mle (toy.column arbitrary ⟨0, 2⟩).values (algebraMap K E) z

-- The verifier's closed form is the extension of the weight's cube values, off the cube.
#guard (eqWeight (#v[u, u + 1, u * u] : Vector E 3)).mle #v[u + 1, u, 1] =
  evalMle (eqWeight (#v[u, u + 1, u * u] : Vector E 3)).onCube #v[u + 1, u, 1]
-- On the cube it is the indicator of the point.
#guard (eqWeight (#v[0, 1, 1] : Vector E 3)).mle #v[0, 1, 1] = 1
#guard (eqWeight (#v[0, 1, 1] : Vector E 3)).mle #v[1, 1, 0] = 0

end LeanVMTests.Protocol.ClaimWeights
