/-
  Rv64mc.Model.Extra.Transcript

  `Model.Sponge`'s values in the forms the compiled code computes them: a challenge's limbs are the two lanes it
  is made of.
-/

import Rv64mc.Model.Transcript

namespace Rv64mc.Model

theorem limbs_ofLimbsW (w : Limbs) : limbs (ofLimbsW w) = w := by
  rw [ofLimbsW, limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

/-- The challenge's limbs: lanes `0` and `1`. -/
theorem limbs_challengeRust (s : List (BitVec 64)) : limbs (challengeRust s) = (s.getD 0 0, s.getD 1 0) := by
  rw [challengeRust, limbs_ofLimbsW]

end Rv64mc.Model
