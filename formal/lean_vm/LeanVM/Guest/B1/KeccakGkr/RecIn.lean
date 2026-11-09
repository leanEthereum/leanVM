/-
  LeanVM.Guest.B1.KeccakGkr.RecIn

  A word in a region, and the offsets of a round record the pack rounds' loops read and write.
-/

module

public import LeanVM.Guest.Memory.LiftPure

/-!
# Words in a region

`InR R p k`: the word at `p·g^k` lies in the region `R`. `roundRecOffs`: the offsets of a round
record (`KR_CAP = 16` apart: the capacity, the cursor, the claim, the scale) at `x` and at `x·g`,
which the pack rounds' loops read and write.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics

@[expose] public section

/-- The word at `p·g^k` lies in the region `R`. -/
def InR (R : ℕ → Prop) (p : E) (k : ℕ) : Prop :=
  ∃ i, p.limb 0 * Parameters.addressOfIndex k = Parameters.addressOfIndex i ∧ R i

/-- The record's offsets a pack round's iteration reads and writes. -/
def roundRecOffs : List ℕ := [0, 16, 32, 48, 64, 80, 96, 112, 1, 17, 33, 49, 65, 81, 97, 113]

end
end LeanVM.Guest.B1.VerifySub
