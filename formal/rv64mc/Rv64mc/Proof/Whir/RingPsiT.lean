/-
  Rv64mc.Proof.Whir.RingPsiT

  `ring_psi` is total: it returns `RingPsi.Post`'s value (`Spec.Whir.RingPsi`), over any program holding its
  template, from the total contracts of `E::mul` (`EMulT`) and `E::square` (`ESquareT`). The partial proof
  (`RingPsi.lean`) ported by `rv_autoT`: its loop, there an induction on the elements left, is `Total.loop` at
  instruction 32 with them as the measure (`LoopInv`, the partial `Inv` and the code map kept). The precondition
  (`PreT`) adds that a nonempty `g` lies in a window (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Whir.RingPsi
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESquareT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Whir.RingPsiT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Whir.RingPsi Rv64mc.Proof.Whir
open Rv64mc.Proof.Whir.RingPsi
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.RingSwitch.RingPsi (Link tmpl)

/-- The total precondition: `Pre`, and a nonempty `g` in a window and 8-byte aligned. -/
def PreT (env : Env) (v : E) (gs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env v gs regs m ∧ (gs.length = 0 ∨ (InWin env (regs .x12) (16 * gs.length) ∧ (regs .x12).toNat % 8 = 0))

/-- **The total contract of `ring_psi`**: `RingPsi.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ v gs, HoldsT env p i need (PreT env v gs) (Post v gs)

/-- The loop's head with `k + 1` elements left: `Inv` after the others, and the code map kept since the entry. -/
def LoopInv (env : Env) (v : E) (gs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < gs.length ∧ Inv env v gs ret top regs m (gs.length - 1 - k) R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS) :
    specT env p i need := by
  intro v gs
  rv_autoT hp with [hL] using [hmul, hsq]
  all_goals have hb := live_bound hpre_10 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hb
  · have h0 : gs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  · have h0 : gs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : gs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  obtain ⟨hw, hal⟩ := hpre_11.resolve_left h0
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs gs).length < 2 ^ 64 := by
    simp only [List.length_map]; omega
  refine Total.loop (LoopInv env v gs ret top regs m) ?_ (gs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = gs.length := ⟨gs.length - 1 - k, by omega⟩
    rw [show gs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x12 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x12).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul, hsq]
    · cases k with
      | zero => exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret2_18, hret1_18, hcode]⟩
        rw [show gs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact ptr_step _ _
        · rw [← body_psi hinv_14 hpre_5 hpre_9 hpre_10 (by omega)]
        · rw [← body_psi hinv_14 hpre_5 hpre_9 hpre_10 (by omega)]
        · rw [acc_succ (by omega), RingPsi.step, power_limbs]
        · rw [acc_succ (by omega), RingPsi.step, power_limbs]
    all_goals have he := (end_iff hq (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals rw [ringPsiRust_acc, ← he, ← body_psi hinv_14 hpre_5 hpre_9 hpre_10 (by omega)]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show gs.length - 1 - (gs.length - 1) = 0 by omega]
    rv_closeT
    · exact ptr_start _
    all_goals rfl

end Rv64mc.Proof.Whir.RingPsiT

/-- info: 'Rv64mc.Proof.Whir.RingPsiT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Whir.RingPsiT.total
