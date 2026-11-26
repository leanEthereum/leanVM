/-
  Rv64mc.Proof.Multilinear.ScalerMulT

  `Scaler::mul` is total: it returns `Scaler.MulPost`'s product (`Spec.Multilinear.Scaler`), or ends the run with
  `a0 = 2` where `Scaled::mul` does, over any program holding its template, from the total contracts of `E::mul`
  (`EMulT`) and `Scaled::mul` (`ScaledMulT`). The partial proof (`ScalerMul.lean`) ported by `rv_autoT`, one case of
  the scaler at a time. The precondition (`MulPreT`) adds that the scaler's three words lie in a window, 8-byte
  aligned, and a table's entries as `ScaledMulT.MulPreT` asks (`TabWin`).

  ## Main definitions

  * `TabWin`, `MulPreT`, `mulSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.ScalerMul
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ScaledMulT

namespace Rv64mc.Proof.Multilinear.ScalerMulT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.Scaler
open Rv64mc.Proof.Multilinear.ScalerMul
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.Scaler.Mul (Link tmpl)

/-- A table scaler's entries, at the pointer in the scaler's second word, in a window and 8-byte aligned unless
    there are none. -/
def TabWin (env : Env) (m : MachineState) (a : Word) : Model.Scaler → Prop
  | .plain _ => True
  | .table tabs => tabs.length = 0 ∨
      (InWin env (m.getMem (a + 8#64)) (16 * tabs.length) ∧ (m.getMem (a + 8#64)).toNat % 8 = 0)

/-- The total precondition: `MulPre`, the scaler's three words in a window and 8-byte aligned, and `TabWin`. -/
def MulPreT (env : Env) (s : Model.Scaler) (v : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  MulPre env s v regs m ∧ InWin env (regs .x10) 24 ∧ (regs .x10).toNat % 8 = 0 ∧ TabWin env m (regs .x10) s

/-- **The total contract of `Scaler::mul`**: `Scaler.mulSpec`'s, as a `HoldsT`, from `MulPreT`, ending the run with
    `a0 = 2` where `Scaled::mul` does. -/
def mulSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ s v, HoldsT env p i need (MulPreT env s v) (MulPost s v) (Stop := AbortStop)

variable (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
  {need needS needM : Nat} (hnS : needS ≤ need) (hnM : needM ≤ need)
  (hsm : Field.ScaledMulT.mulSpecT env p L.scaled_Mul.idx needS)
  (hmul : Field.EMulT.specT env p L.asMul_Mul.idx needM)
include hp hL hnS hnM hsm hmul

omit hnS hsm in
theorem total_plain (r v : E) :
    HoldsT env p i need (MulPreT env (.plain r) v) (MulPost (.plain r) v) (Stop := AbortStop) := by
  rv_autoT hp with [hL] using [hmul]
  · omega
  · rw [hpre_6.2.1, hpre_6.2.2, Model.eMul_eq]; rfl
  · rw [hpre_6.2.1, hpre_6.2.2, Model.eMul_eq]; rfl
  · exact absurd hpre_6.1 hc

omit hnM hmul in
theorem total_table (tabs : List Model.Limbs) (v : E) :
    HoldsT env p i need (MulPreT env (.table tabs) v) (MulPost (.table tabs) v) (Stop := AbortStop) := by
  rv_autoT hp with [hL] using [hsm tabs]
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

/-- **`Scaler::mul` is total.** -/
theorem total : mulSpecT env p i need := by
  intro s v
  cases s with
  | plain r => exact total_plain env p i L hp hL hnM hmul r v
  | table tabs => exact total_table env p i L hp hL hnS hsm tabs v

end Rv64mc.Proof.Multilinear.ScalerMulT

/-- info: 'Rv64mc.Proof.Multilinear.ScalerMulT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.ScalerMulT.total
