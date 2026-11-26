/-
  Rv64mc.Proof.Multilinear.PolyEvalT

  `poly_eval` is total: it returns `PolyEval.Post`'s value (`Spec.Multilinear.PolyEval`), over any program holding
  its template, from `E::mul`'s total contract (`EMulT`). The partial proof (`PolyEval.lean`) ported by `rv_autoT`:
  its loop, there an induction on the coefficients left, is `Total.loop` at instruction 36 with them as the measure
  (`LoopInv`, the partial `Inv` and the code map kept). The precondition (`PreT`) adds that a
  nonempty slice lies in a window (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Multilinear.PolyEval
import Rv64mc.Proof.Field.EMulT
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Multilinear.PolyEvalT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Multilinear.PolyEval Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Multilinear.PolyEval
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Multilinear.PolyEval (Link tmpl)

/-- The total precondition: `Pre`, and a nonempty slice in a window and 8-byte aligned. -/
def PreT (env : Env) (cs : List E) (pt : E) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env cs pt regs m ∧ (cs.length = 0 ∨ (InWin env (regs .x10) (16 * cs.length) ∧ (regs .x10).toNat % 8 = 0))

/-- **The total contract of `poly_eval`**: `PolyEval.spec`'s, as a `HoldsT`, from `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ cs pt, HoldsT env p i need (PreT env cs pt) (Post cs pt)

/-- The loop's head about to read coefficient `j`: `Inv` and the code map kept since the entry. -/
def LoopInv (env : Env) (cs : List E) (pt : E) (ret top : Word) (regs : Reg → Word) (m : MachineState) (j : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  j < cs.length ∧ Inv env cs pt ret top regs m j R M ∧ M.code = m.code

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need needM : Nat} (hnM : 64 + needM ≤ need) (hmul : Field.EMulT.specT env p L.mul.idx needM) :
    specT env p i need := by
  intro cs pt
  rv_autoT hp with [hL] using [hmul]
  all_goals have hlx := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hlx
  iterate 2
    have h0 : cs.length = 0 := by simpa using (len_zero (by simp; omega)).1 hc
    rw [List.length_eq_zero_iff.1 h0]
    simp [Model.polyEvalRust, Model.limbs_zero, Model.eZero]
  have h0 : cs.length ≠ 0 := fun h => hc ((len_zero (by simp; omega)).2 (by simpa using h))
  obtain ⟨hw, hal⟩ := hpre_11.resolve_left h0
  refine Total.loop (LoopInv env cs pt ret top regs m) ?_ (cs.length - 1) _ _ ?_
  · intro j R M hI ih
    obtain ⟨hj, hinv, hcode⟩ := hI
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have he8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [he0]; unfold InWin at hw; omega), he0, Nat.add_assoc]
    rv_introT hinv
    have hnm := hinv_14.1
    rv_symT hp with [hL] using [hmul]
    · cases j with
      | zero => exact absurd ((exit_iff (by omega)).2 rfl) hc
      | succ j =>
        refine ih j _ _ (by omega) ⟨by omega, ?_, by rw [hret1_18, hcode]⟩
        rv_closeT
        · exact back_ptr _ _
        all_goals rw [← body_val hinv_14 hpre_5 hpre_7 hpre_8 hj]
    all_goals obtain rfl := (exit_iff (by omega)).1 hc
    all_goals rw [← hor_zero, ← body_val hinv_14 hpre_5 hpre_7 hpre_8 hj]
  · refine ⟨by omega, ?_, by rv_closeT⟩
    rv_closeT
    · rw [List.length_map]; exact PolyEval.start_ptr (by omega) (by omega)
    all_goals rw [show cs.length - 1 + 1 = cs.length by omega, hor_len, Model.limbs_zero]; rfl

end Rv64mc.Proof.Multilinear.PolyEvalT

/-- info: 'Rv64mc.Proof.Multilinear.PolyEvalT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Multilinear.PolyEvalT.total
