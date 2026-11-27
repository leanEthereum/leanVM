/-
  Rv64mc.Proof.Whir.Frobenius8SafeT

  `frobenius_8`'s total contract (`Frobenius8T.specT`, for every value) as one contract on the registers alone, for
  callers whose safety does not depend on the value: from `8 k < 2^64` (`k` in `a2`), it returns. The value is the
  one the limbs in `a0`, `a1` name (`Model.ofLimbsW`).

  ## Main results

  * `frobSafe`
-/

import Rv64mc.Proof.Whir.Frobenius8T

namespace Rv64mc.Proof.Whir.Frobenius8SafeT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The limbs of the value `Model.ofLimbsW` names. -/
theorem limbs_ofLimbsW (w : Model.Limbs) : Model.limbs (Model.ofLimbsW w) = w := by
  rw [Model.ofLimbsW, Model.limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

/-- **`frobenius_8` returns** from any limbs, `8 k < 2^64`. -/
theorem frobSafe {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat} (h : Frobenius8T.specT env p i need) :
    HoldsT env p i need (fun regs _ => 8 * (regs .x12).toNat < 2 ^ 64) (fun _ _ _ _ => True) :=
  fun Q ret top rest regs m ⟨⟨he, hs, hst, hn, hp, ha⟩, hw⟩ hstop hk =>
    have hl := limbs_ofLimbsW (regs .x10, regs .x11)
    h (Model.ofLimbsW (regs .x10, regs .x11)) Q ret top rest regs m
      ⟨⟨he, hs, hst, hn, ⟨by rw [hl], by rw [hl], hp⟩, ha⟩, hw⟩ hstop
      fun r' m' ⟨⟨h1, h2, h3, _⟩, h5⟩ => hk r' m' ⟨⟨h1, h2, h3, trivial⟩, h5⟩

end Rv64mc.Proof.Whir.Frobenius8SafeT
