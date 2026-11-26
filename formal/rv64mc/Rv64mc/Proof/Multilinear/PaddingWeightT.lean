/-
  Rv64mc.Proof.Multilinear.PaddingWeightT

  `padding_weight` is total: it returns `PaddingWeight.Post`'s value (`Spec.Multilinear.PaddingWeight`), over any
  program holding its template, from `E::mul`'s total contract (`EMulT`). The partial proof (`PaddingWeight.lean`)
  ported by `rv_autoT`: its loop, there an induction on the coordinates left, is `Total.loop` at instruction 40 with
  them as the measure (`LoopInv`, the partial `Inv` and the code map kept). The precondition (`PreT`) adds that a
  nonempty point lies in a window (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.PaddingWeight
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Multilinear.PaddingWeightT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PaddingWeight
open Rv64mc.Proof.Multilinear Rv64mc.Proof.Multilinear.PaddingWeight
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.PaddingWeight (Link tmpl)

/-- The total precondition: `Pre`, and a nonempty point in a window and 8-byte aligned. -/
def PreT (env : Env) (xs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env xs regs m ∧ (xs.length = 0 ∨ (InWin env (regs .x10) (16 * xs.length) ∧ (regs .x10).toNat % 8 = 0))

/-- **The total contract of `padding_weight`**: `PaddingWeight.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs, HoldsT env p i need (PreT env xs) (Post xs)

/-- The loop's head with `k + 1` coordinates left: `Inv` after the others, and the code map kept since the
    entry. -/
def LoopInv (env : Env) (xs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < xs.length ∧ Inv env xs ret top regs m (xs.length - 1 - k) R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 96 + needM ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM) :
    specT env p i need := by
  intro xs
  rv_autoT hp with [hL] using [hmul]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [← post_val, h0]; rfl
  · have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [← post_val, h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  obtain ⟨hw, hal⟩ := hpre_9.resolve_left h0
  refine Total.loop (LoopInv env xs ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have he8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [he0]; unfold InWin at hw; omega), he0, Nat.add_assoc]
    have hjl : j < (List.map Model.limbs xs).length := by simp; omega
    rv_introT hinv
    have hnm := hinv_9.1
    have ex := EListAt.load (j := j) hinv_9 hpre_5 hpre_7 (by simpa using hpre_8) hjl
    simp only [List.getElem_map] at ex
    rv_symT hp with [hL] using [hmul]
    · cases k with
      | zero => exact absurd ((cnt_iff (by simp; omega) (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret2_18, hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact cnt_step j
        · exact step_ptr _ _
        · rw [(body_val ex.1 ex.2).1, ← low_succ (by omega)]
        · rw [(body_val ex.1 ex.2).2, ← low_succ (by omega)]
    all_goals have he := (cnt_iff (by simp; omega) (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals rw [(body_val ex.1 ex.2).1, (body_val ex.1 ex.2).2, ← low_succ (by omega), he, post_val]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    · exact start_ptr _
    · rw [show low xs (regs .x12) 0 = 1 from rfl, Model.limbs_one]; rfl
    · rw [show low xs (regs .x12) 0 = 1 from rfl, Model.limbs_one]; rfl

end Rv64mc.Proof.Multilinear.PaddingWeightT

/-- info: 'Rv64mc.Proof.Multilinear.PaddingWeightT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.PaddingWeightT.total
