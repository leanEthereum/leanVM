/-
  Rv64mc.Proof.Multilinear.EqEvalT

  `eq_eval` is total: it returns `EqEval.Post`'s value (`Spec.Multilinear.EqEval`), or ends the run with `a0 = 2`
  when the lengths differ (`assert_eq!`), over any program holding its template, from the total contracts of
  `E::mul` (`EMulT`) and `assert_failed` (`Aborts`). The partial proof (`EqEval.lean`) ported by `rv_autoT`: its
  loop, there an induction on the elements left, is `Total.loop` at instruction 28 with them as the measure
  (`LoopInv`, the partial `Inv` and the code map kept). The precondition (`PreT`) adds that each nonempty slice lies
  in a window (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.EqEval
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Core.AbortStop
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Multilinear.EqEvalT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.EqEval Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.EqEval
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.EqEval (Link tmpl)

/-- The total precondition: `Pre`, and each nonempty slice in a window and 8-byte aligned. -/
def PreT (env : Env) (xs ys : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env xs ys regs m ∧
    (xs.length = 0 ∨ (InWin env (regs .x10) (16 * xs.length) ∧ (regs .x10).toNat % 8 = 0)) ∧
    (ys.length = 0 ∨ (InWin env (regs .x12) (16 * ys.length) ∧ (regs .x12).toNat % 8 = 0))

/-- **The total contract of `eq_eval`**: `EqEval.spec`'s, as a `HoldsT`, from `PreT`, ending the run with `a0 = 2` on
    slices of different lengths. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs ys, HoldsT env p i need (PreT env xs ys) (Post xs ys) (Stop := AbortStop)

/-- The loop's head with `k + 1` elements left: `Inv` after the others, and the code map kept since the entry. -/
def LoopInv (env : Env) (xs ys : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < xs.length ∧ Inv env xs ys ret top regs m (xs.length - 1 - k) R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needF : Nat} (hnM : 48 + needM ≤ need) (hnF : 48 + needF ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hfail : Aborts env p L.assertFailedUsizeUsize.idx needF) :
    specT env p i need := by
  intro xs ys
  rv_autoT hp with [hL] using [hmul, hfail]
  all_goals have hlx := live_bound hpre_10 hpre_5
  all_goals have hly := live_bound hpre_11 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx hly
  all_goals have hlen : xs.length = ys.length := by simpa using len_eq (by simp; omega) (by simp; omega) hc_1
  · intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    simp [acc, h0, Model.limbs_one, Model.eOne]
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  obtain ⟨hwx, halx⟩ := hpre_12.resolve_left h0
  obtain ⟨hwy, haly⟩ := hpre_13.resolve_left (by omega)
  rw [← hlen] at hwy
  have hq : (regs .x12).toNat + 16 * (List.map Model.limbs xs).length + 8 < 2 ^ 64 := by
    simp only [List.length_map]; omega
  refine Total.loop (LoopInv env xs ys ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have hx0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hwx; omega)
    have hx8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [hx0]; unfold InWin at hwx; omega), hx0, Nat.add_assoc]
    have hy0 : (regs .x12 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x12).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hwy; omega)
    have hy8 : (regs .x12 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x12).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [hy0]; unfold InWin at hwy; omega), hy0, Nat.add_assoc]
    rv_introT hinv
    have hnm := hinv_16.1
    rv_symT hp with [hL] using [hmul]
    · cases k with
      | zero => exact absurd ((end_iff hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr _ _
        · exact step_ptr _ _
        all_goals rw [body_val hinv_16 hpre_5 hpre_7 hpre_9 hpre_10 hpre_11 (by omega) (by omega)]
    have he := (end_iff hq (by simp; omega)).1 hc
    simp only [List.length_map] at he
    intro v hv
    rw [eqEvalRust_acc hlen, Option.some.injEq] at hv
    subst hv
    rw [← he, ← body_val hinv_16 hpre_5 hpre_7 hpre_9 hpre_10 hpre_11 (by omega) (by omega)]
    exact ⟨rfl, rfl⟩
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    all_goals first
      | exact start_ptr _
      | (rw [show acc xs ys 0 = 1 from rfl, Model.limbs_one]; rfl)

end Rv64mc.Proof.Multilinear.EqEvalT

/-- info: 'Rv64mc.Proof.Multilinear.EqEvalT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.EqEvalT.total
