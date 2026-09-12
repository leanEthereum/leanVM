import SphincsSecurity.Proof.Base.Prelude
import SphincsSecurity.Statement

/-!
# One guess

A fresh oracle answer, truncated to the digest length, hits a fixed target with probability at most
`2 ^ -n`. Every per-query bound in the development is an instance of this: the adversary picks the
tweak and so the position, domain separation fixes the target, and this bounds what the answer buys.
-/

namespace SphincsSecurity

open OracleComp ENNReal

/-! ### The same, at any width

The digest's index is the low `h` bits of an oracle answer, and the leak argument needs it to be
near-uniform. That is the fiber count above at a different width, so it is worth having once.
-/

theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

end SphincsSecurity
