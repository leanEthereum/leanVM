/-
  Rv64mc.Proof.Runtime.DoReserve

  `RawVecInner::reserve::do_reserve_and_handle` meets `DoReserveSpec`: it calls `grow_amortized` with its own
  arguments and returns on `Ok`, else calls `handle_error`, which does not return.
-/

import Rv64mc.Spec.Runtime.RawVec
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal
import Rv64mc.Tactic.Sym
import Rv64mc.Proof.Runtime.GrowOne

namespace Rv64mc.Proof.Runtime.DoReserve

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Gen.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal (Link tmpl)

theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need nga : Nat} (hn : 16 + nga ≤ need) (hga : GrowAmortizedSpec env p L.growAmortized.idx nga)
    (hhe : NoReturn env p L.handleError.idx nga) : DoReserveSpec env p i need := by
  rv_auto hp with [hL] using [hga, hhe]
  all_goals
    have hlay := env.layout
    rw [hpre_2] at hpre_6
    simp only [Layouts.RawVecInner.byteSize] at hpre_6 hpre_7
    have hown : env.Owned m top (regs .x10) 16 := ⟨hpre_6, hpre_7⟩
    have hlim : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
    have hslot := GrowOne.slot_notin hown hpre_5 hlim
    have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have hb8 : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by rw [h8]; omega
    have hne : regs .x10 ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h]; exact ⟨Nat.le_refl _, by omega⟩)
    have hneP : rvPtrAt (regs .x10) ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h, GrowOne.rvPtrAt_eq]
      exact ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩)
    have hcap1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10)) =
        m.getMem (rvCapAt (regs .x10)) := by
      rw [GrowOne.rvCapAt_eq]; exact MachineState.getMem_setMem_ne hne
    have hptr1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvPtrAt (regs .x10)) =
        m.getMem (rvPtrAt (regs .x10)) := MachineState.getMem_setMem_ne hneP
    have hnx1 : env.next (m.setMem (top + 0xfffffffffffffff8#64) ret) = env.next m := Env.next_setMem_stack hb8
    have hout : ¬ GrowOut regs m (top + 0xfffffffffffffff8#64) := by
      rintro (h | h)
      · exact hne (by rw [h, GrowOne.rvCapAt_eq])
      · exact hneP h.symm
  -- `grow_amortized`'s precondition, after `ra`'s store
  · rw [hnx1]; rcases hpre_6 with h | h
    · exact Or.inl (by simp only [Layouts.RawVecInner.byteSize]; exact h)
    · exact Or.inr (by rw [h16]; omega)
  · rw [hcap1, hptr1]; unfold Env.Live; rw [hnx1]; exact hpre_11
  · rw [hcap1]; exact hpre_12
  -- `handle_error`'s
  · exact hret1_14.2.1
  -- the return
  · rw [hret1_14.getMem_above (by rw [h16]; omega) (by rw [h16, h8]; omega) hout]
    exact MachineState.getMem_setMem_eq
  · exact (Env.Frame.setMem_stack hpre_5 hb8 (by rw [h8]; omega)).trans hret1_14 (by rw [h16]; omega)
      fun a h => Or.inr (Or.inr (Or.inr h))
  all_goals have hg := GrowOne.grown_of_store hown hpre_11 hslot hb8 hpre_5 (hret1_16 hc)
  · exact hg.1
  · exact hg.2.1
  · exact hg.2.2

end Rv64mc.Proof.Runtime.DoReserve
