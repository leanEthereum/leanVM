/-
  Rv64mc.Proof.Multilinear.ScalerMul

  `Scaler::mul` keeps its contract (`Spec.Multilinear.Scaler.mulSpec`), over any program holding its template, from
  the contracts of `Scaled::mul` and `E::mul`, each tail-called on its variant.
-/

import Rv64mc.Spec.Multilinear.Scaler
import Rv64mc.Spec.Field.EMul
import Rv64mc.Spec.Field.Scaled
import Rv64mc.Gen.Tmpl.Verifier.Multilinear.Scaler.Mul
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Multilinear.ScalerMul

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.Scaler
open Rv64mc.Gen.Verifier.Multilinear.Scaler.Mul (Link tmpl)

theorem limbs_ofLimbsW (w : Model.Limbs) : Model.limbs (Model.ofLimbsW w) = w := by
  rw [Model.ofLimbsW, Model.limbs_ofLimbs, BF64.toBitVec_ofBitVec, BF64.toBitVec_ofBitVec]

variable (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
  {need needS needM : Nat} (hnS : needS ≤ need) (hnM : needM ≤ need)
  (hsm : Spec.Field.Scaled.mulSpec env p L.scaled_Mul.idx needS)
  (hmul : Spec.Field.EMul.spec env p L.asMul_Mul.idx needM)
include hp hL hnS hnM hsm hmul

omit hnS hsm in
theorem ok_plain (r v : E) : Holds env p i need (MulPre env (.plain r) v) (MulPost (.plain r) v) := by
  rv_auto hp with [hL] using [hmul]
  · omega
  · rw [hpre_6.2.1, hpre_6.2.2, Model.eMul_eq]; rfl
  · rw [hpre_6.2.1, hpre_6.2.2, Model.eMul_eq]; rfl
  · exact absurd hpre_6.1 hc

omit hnM hmul in
theorem ok_table (tabs : List Model.Limbs) (v : E) :
    Holds env p i need (MulPre env (.table tabs) v) (MulPost (.table tabs) v) := by
  rv_auto hp with [hL] using [hsm tabs]
  all_goals obtain ⟨ptr, cap, hv, hl⟩ := hpre_6
  all_goals have hp8 : m.getMem (regs .x10 + 8#64) = ptr := hv.ptr_eq
  · have hc0 := hv.cap_eq
    simp only [vecCap, Layouts.Vec.cap, BitVec.add_zero] at hc0
    rw [hc0, ← BitVec.toNat_inj] at hc
    have := hv.cap_lt
    simp at hc; omega
  · omega
  · exact hv.len_eq
  · rw [hp8]; exact hv.elems
  · rw [hp8]; exact hl
  · show _ = (Model.limbs (Model.scaledMulE tabs v)).1; rw [Model.scaledMulE, limbs_ofLimbsW]
  · show _ = (Model.limbs (Model.scaledMulE tabs v)).2; rw [Model.scaledMulE, limbs_ofLimbsW]

/-- **`Scaler::mul` keeps its contract.** -/
theorem ok : mulSpec env p i need := by
  intro s v
  cases s with
  | plain r => exact ok_plain env p i L hp hL hnM hmul r v
  | table tabs => exact ok_table env p i L hp hL hnS hsm tabs v

end Rv64mc.Proof.Multilinear.ScalerMul
