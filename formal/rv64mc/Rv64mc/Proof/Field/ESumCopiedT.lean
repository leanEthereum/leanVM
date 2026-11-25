/-
  Rv64mc.Proof.Field.ESumCopiedT

  `E::sum` over a copied slice iterator is total: it returns `ESumCopied.Post`'s sum (`Spec.Field.ESum`), over any
  program holding its template. The partial proof (`ESumCopied.lean`) ported by `rv_autoT`, its loop by `Total.loop`
  with the elements left as the measure. The precondition (`PreT`) adds that a nonempty slice lies in a window
  (`InWin`) and is 8-byte aligned, for its doubleword loads.

  ## Main definitions

  * `PreT`, `specT`, `LoopInv`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Field.ESumCopied
import Rv64mc.Proof.Runtime.MemsetT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Field.ESumCopiedT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Field.ESumCopied Rv64mc.Proof.Multilinear
open Rv64mc.Proof.Field.ESumCopied
open Rv64mc.Proof.Runtime.MemsetT (InWin)
open Rv64mc.Gen.Verifier.Field.E.SumCopiedIterE (Link tmpl)

/-- The total precondition: `Pre`, and a nonempty slice in a window and 8-byte aligned. -/
def PreT (env : Env) (es : List Model.Limbs) (regs : Reg → Word) (m : MachineState) : Prop :=
  Pre env es regs m ∧ (es.length = 0 ∨ (InWin env (regs .x10) (16 * es.length) ∧ (regs .x10).toNat % 8 = 0))

/-- **The total contract of `E::sum` over a copied slice iterator**: `ESumCopied.spec`'s, as a `HoldsT`, from
    `PreT`. -/
def specT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ es, HoldsT env p i need (PreT env es) (Post es)

/-- The loop at its head with `k + 1` elements left: `Inv` after the others, the memory the entry's. -/
def LoopInv (env : Env) (es : List Model.Limbs) (ret top : Word) (regs : Reg → Word) (m : MachineState) (k : Nat)
    (R : Reg → Word) (M : MachineState) : Prop :=
  M = m ∧ k < es.length ∧ Inv env es ret top regs m (es.length - 1 - k) R M

theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (need : Nat) :
    specT env p i need := by
  intro es
  rv_autoT hp
  all_goals have hq := live_bound hpre_8 hpre_5
  all_goals simp only [Layouts.E.byteSize] at hq
  · obtain rfl := List.eq_nil_of_length_eq_zero (len_zero_of (by omega) hc); rfl
  · obtain rfl := List.eq_nil_of_length_eq_zero (len_zero_of (by omega) hc); rfl
  have h0 : es.length ≠ 0 := fun h => hc (by rw [h]; simp)
  obtain ⟨hw, hal⟩ := hpre_9.resolve_left h0
  refine Total.loop (LoopInv env es ret top regs m) ?_ (es.length - 1) _ _ ?_
  · intro k R M hI ih
    obtain ⟨rfl, hlt, hI⟩ := hI
    obtain ⟨j, hj⟩ : ∃ j, j + k + 1 = es.length := ⟨es.length - 1 - k, by omega⟩
    rw [show es.length - 1 - k = j by omega] at hI
    have he0 : (regs .x10 + BitVec.ofNat 64 (16 * j)).toNat = (regs .x10).toNat + 16 * j :=
      toNat_add_ofNat (by unfold InWin at hw; omega)
    have he8 : (regs .x10 + BitVec.ofNat 64 (16 * j) + 8#64).toNat = (regs .x10).toNat + (16 * j + 8) := by
      rw [toNat_add_ofNat (by rw [he0]; unfold InWin at hw; omega), he0, Nat.add_assoc]
    rv_introT hI
    rv_symT hp
    · cases k with
      | zero => exact absurd ((end_iff hq (by omega)).2 (by omega)) hc
      | succ k =>
        refine ih k _ _ (by omega) ⟨rfl, by omega, ?_⟩
        rw [show es.length - 1 - k = j + 1 by omega]
        rv_closeT
        · exact step_ptr _ _
        · rw [← body_val (j := j) hI_19 hpre_5 hpre_6 hpre_8 (by omega)]
        · rw [← body_val (j := j) hI_19 hpre_5 hpre_6 hpre_8 (by omega)]
    · rw [← acc_len, ← (end_iff hq (by omega)).1 hc,
        ← body_val hI_19 hpre_5 hpre_6 hpre_8 (by omega)]
    · rw [← acc_len, ← (end_iff hq (by omega)).1 hc,
        ← body_val hI_19 hpre_5 hpre_6 hpre_8 (by omega)]
  · refine ⟨rfl, by omega, ?_⟩
    rw [show es.length - 1 - (es.length - 1) = 0 by omega]
    rv_closeT
    · exact start_ptr _
    · exact end_eq (by omega)
    all_goals rfl

end Rv64mc.Proof.Field.ESumCopiedT

/-- info: 'Rv64mc.Proof.Field.ESumCopiedT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Field.ESumCopiedT.total
