/-
  Rv64mc.Proof.Whir.Frobenius8T

  `frobenius_8` is total: it returns `Frobenius8.Post`'s value (`Spec.Whir.Frobenius8`), over any program holding its
  template, from `E::square`'s total contract (`ESquareT`). The partial proof (`Frobenius8.lean`) ported by
  `rv_autoT`, its loop by `Total.loop` with the squarings left as the measure (`LoopInv`: `Frobenius8.Inv` and the
  code map kept).

  ## Main definitions

  * `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Whir.Frobenius8
import Rv64mc.Proof.Field.ESquareT

namespace Rv64mc.Proof.Whir.Frobenius8T

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.Frobenius8
open Rv64mc.Proof.Whir.Frobenius8
open Rv64mc.Gen.Verifier.RingSwitch.Frobenius8 (Link tmpl)

/-- **The total contract of `frobenius_8`**: `Frobenius8.spec`'s, as a `HoldsT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := ∀ v, HoldsT env p i need (Pre v) (Post v)

/-- The loop at its head with `k + 1` squarings left of `N`: `Inv` after the others, and the code map kept. -/
def LoopInv (env : Env) (v : E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (N k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < N ∧ Inv env v ret top regs m (N - 1 - k) R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needS : Nat} (hnS : 16 + needS ≤ need) (hsq : Field.ESquareT.specT env p L.square.idx needS) :
    specT env p i need := by
  intro v
  rv_autoT hp with [hL] using [hsq]
  · rw [p_zero hc]; rfl
  · rw [p_zero hc]; rfl
  have h8 := hpre_8
  refine Total.loop (LoopInv env v ret top regs m (8 * (regs .x12).toNat)) ?_ (8 * (regs .x12).toNat - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hI, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = 8 * (regs .x12).toNat := ⟨8 * (regs .x12).toNat - 1 - k, by omega⟩
    rw [show 8 * (regs .x12).toNat - 1 - k = j by omega] at hI
    rv_introT hI
    rv_symT hp with [hL] using [hsq]
    · cases k with
      | zero => exact absurd ((count_zero h8 (by omega)).2 (by omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, Eq.trans (by assumption) hcode⟩
        rw [show 8 * (regs .x12).toNat - 1 - k = j + 1 by omega]
        rv_closeT
        · exact count_step h8 (by omega)
        · rw [limbs_sq_succ]
        · rw [limbs_sq_succ]
    all_goals rw [show Model.frobenius8Rust v (regs .x12).toNat = Frobenius8.sq v (j + 1) by
      rw [show j + 1 = 8 * (regs .x12).toNat from (count_zero h8 (by omega)).1 hc]; rfl, limbs_sq_succ]
  · refine ⟨by have := p_pos hc; omega, ?_, rfl⟩
    rw [show 8 * (regs .x12).toNat - 1 - (8 * (regs .x12).toNat - 1) = 0 by omega]
    rv_closeT
    · exact count_start hpre_8
    all_goals rfl

end Rv64mc.Proof.Whir.Frobenius8T

/-- info: 'Rv64mc.Proof.Whir.Frobenius8T.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.Frobenius8T.total
