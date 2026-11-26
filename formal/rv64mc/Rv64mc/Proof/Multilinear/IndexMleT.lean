/-
  Rv64mc.Proof.Multilinear.IndexMleT

  `index_mle` is total: it returns `IndexMle.Post`'s value (`Spec.Multilinear.IndexMle`), over any program holding
  its template, from the total contracts of `E::mul` (`EMulT`) and `E::square` (`ESquareT`). The partial proof
  (`IndexMle.lean`) ported by `rv_autoT`: its loop, there an induction on the coordinates left, is `Total.loop` at
  instruction 32 with them as the measure (`LoopInv`, the partial `Inv` and the code map kept). The precondition
  (`PreT`) adds that a nonempty point lies in a window (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.IndexMle
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Field.ESquareT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Multilinear.IndexMleT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.IndexMle Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.IndexMle
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.IndexMle (Link tmpl)

/-- The total precondition: `Pre`, and a nonempty point in a window and 8-byte aligned. -/
def PreT (env : Env) (xs : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env xs regs m ∧ (xs.length = 0 ∨ (InWin env (regs .x10) (16 * xs.length) ∧ (regs .x10).toNat % 8 = 0))

/-- **The total contract of `index_mle`**: `IndexMle.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ xs, HoldsT env p i need (PreT env xs) (Post xs)

/-- The loop's head with `k + 1` coordinates left: `Inv` after the others, and the code map kept since the
    entry. -/
def LoopInv (env : Env) (xs : List E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  k < xs.length ∧ Inv env xs ret top regs m (xs.length - 1 - k) R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM needS : Nat} (hnM : 64 + needM ≤ need) (hnS : 64 + needS ≤ need)
    (hmul : Field.EMulT.specT env p L.mul.idx needM) (hsq : Field.ESquareT.specT env p L.square.idx needS) :
    specT env p i need := by
  intro xs
  rv_autoT hp with [hL] using [hmul, hsq]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  iterate 2
    have h0 : xs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]; rfl
  have h0 : xs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  obtain ⟨hw, hal⟩ := hpre_9.resolve_left h0
  have hq : (regs .x10).toNat + 16 * (List.map Model.limbs xs).length < 2 ^ 64 := by
    simp only [List.length_map]; omega
  refine Total.loop (LoopInv env xs ret top regs m) ?_ (xs.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨hlt, hinv, hcode⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = xs.length := ⟨xs.length - 1 - k, by omega⟩
    rw [show xs.length - 1 - k = j by omega] at hinv
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have hjl : j < xs.length := by omega
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul, hsq]
    all_goals have ex := EListAt.load (j := j) hinv_14 hpre_5 hpre_7 (by simpa using hpre_8) (by simpa using hjl)
    all_goals simp only [List.getElem_map] at ex
    · cases k with
      | zero => exact absurd ((end_iff0 hq (by simp; omega)).2 (by simp; omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨by omega, ?_, by rw [hret3_18, hret2_18, hret1_18, hcode]⟩
        rw [show xs.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr0 _ _
        · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
        · rw [body_res _ ex.1 ex.2, st_succ (by omega)]
        all_goals rw [body_g _ xs[j], st_succ (by omega)]
    all_goals have he := (end_iff0 hq (by simp; omega)).1 hc
    all_goals simp only [List.length_map] at he
    all_goals have hs := st_succ (xs := xs) (j := j) (by omega)
    all_goals rw [he] at hs
    all_goals rw [body_res _ ex.1 ex.2, indexMleRust_st, hs]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rw [show xs.length - 1 - (xs.length - 1) = 0 by omega]
    rv_closeT
    · exact start_ptr0 _
    · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
    · rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_one]; rfl
    all_goals rw [show st xs 0 = (1, LeanVM.Protocol.Verifier.gen) from rfl, Model.limbs_gen]; rfl

end Rv64mc.Proof.Multilinear.IndexMleT

/-- info: 'Rv64mc.Proof.Multilinear.IndexMleT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.IndexMleT.total
