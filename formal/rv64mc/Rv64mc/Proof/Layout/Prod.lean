/-
  Rv64mc.Proof.Layout.Prod

  `prod` keeps its contract (`Spec.Layout.Constant.prodSpec`) from `alloc`'s, `gpow`'s and `Form::term`'s: the
  monomial `[min, max]` in a fresh block, its header on the stack, `term`'s region starting at `NEXT` at entry.
  `rv_auto` stops at the call to `term` (pc 66) on both orders of the two columns, where its ghosts (the block) are
  named.
-/

import Rv64mc.Spec.Layout.Constant
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Verifier.Layout.Prod
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Prod

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Gen.Verifier.Layout.Prod (Link tmpl)

set_option maxHeartbeats 1000000 in
set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i need needG : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (halloc : Spec.Runtime.AllocSpec env p L.alloc.idx 0)
    (hgpow : Spec.Layout.Gpow.spec env p L.gpow.idx needG) (hterm : Spec.Layout.Term.spec env p L.term.idx)
    (hpanic : Spec.Runtime.NoReturn env p L.panicNounwindFmt.idx 0) (hn : 64 + needG ≤ need)
    (hn' : 64 + Spec.Layout.Term.need ≤ need) : prodSpec env p i need := by
  rv_auto hp stop [66] with [hL, hn, hn'] using [halloc, hgpow, hpanic]
  all_goals
    have h64 : env.stackLimit.toNat + 64 ≤ top.toNat := by
      have := hpre_3; simp only [Spec.Layout.Term.need] at hn'; omega
    have hr16 : (r1 .x10).toNat + 16 ≤ env.heapEnd.toNat := by
      have := hret1_14.2.1; simp only [BitVec.toNat_ofNat] at hret1_18; omega
    have hr1 : (r1 .x10).toNat < env.stackLimit.toNat := by have := env.layout; omega
  · exact absurd hc (by rw [BitVec.lt_def] at hc_2 ⊢; omega)
  · rv_sym hp with [hL, hn, hn'] using [hterm [(regs .x11).toNat, (regs .x12).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · refine ⟨?_, ?_, ?_, by simp, by decide, ⟨?_, fun k hk => ?_⟩⟩
      all_goals try simp only [vecPtr, vecCap, vecLen, Layouts.Vec.ptr, Layouts.Vec.cap, Layouts.Vec.len,
        List.length_map, List.length_cons, List.length_nil]
      · rv_mem; rfl
      · rv_mem; rfl
      · rv_mem; rfl
      · have := (env.next m1).isLt
        simp only [BitVec.toNat_ofNat] at hret1_18; omega
      · simp only [BitVec.toNat_ofNat] at hret1_18
        have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
        rcases hk2 with rfl | rfl
        · simp only [Nat.mul_zero, List.map_cons, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
            BitVec.add_zero]
          rw [keep4_2 (r1 .x10) (Or.inl (by rv_mem; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr1) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_ne (Tactic.ne_add (by decide)), MachineState.getMem_setMem_eq]
        · simp only [Nat.mul_one, List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero,
            BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hr8 : (r1 .x10 + 8#64).toNat < env.stackLimit.toNat := by
            rw [Tactic.toNat_add_lit _ _ 8 rfl]; have := env.layout; omega
          rw [keep4_2 (r1 .x10 + 8#64) (Or.inl (by rv_mem; rw [Tactic.toNat_add_lit _ _ 8 rfl]; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr8)
              (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_eq]
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by
        rw [BitVec.lt_def] at hc_2; omega
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by
        rw [BitVec.lt_def] at hc_2; omega
      rw [hmin, hmax]; exact hret1_16
  · rv_sym hp with [hL, hn, hn'] using [hterm [(regs .x12).toNat, (regs .x11).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · refine ⟨?_, ?_, ?_, by simp, by decide, ⟨?_, fun k hk => ?_⟩⟩
      all_goals try simp only [vecPtr, vecCap, vecLen, Layouts.Vec.ptr, Layouts.Vec.cap, Layouts.Vec.len,
        List.length_map, List.length_cons, List.length_nil]
      · rv_mem; rfl
      · rv_mem; rfl
      · rv_mem; rfl
      · have := (env.next m1).isLt
        simp only [BitVec.toNat_ofNat] at hret1_18; omega
      · simp only [BitVec.toNat_ofNat] at hret1_18
        have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
        rcases hk2 with rfl | rfl
        · simp only [Nat.mul_zero, List.map_cons, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
            BitVec.add_zero]
          rw [keep5_2 (r1 .x10) (Or.inl (by rv_mem; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr1) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_ne (Tactic.ne_add (by decide)), MachineState.getMem_setMem_eq]
        · simp only [Nat.mul_one, List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero,
            BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hr8 : (r1 .x10 + 8#64).toNat < env.stackLimit.toNat := by
            rw [Tactic.toNat_add_lit _ _ 8 rfl]; have := env.layout; omega
          rw [keep5_2 (r1 .x10 + 8#64) (Or.inl (by rv_mem; rw [Tactic.toNat_add_lit _ _ 8 rfl]; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr8)
              (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_eq]
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by
        rw [BitVec.lt_def] at hc; omega
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by
        rw [BitVec.lt_def] at hc; omega
      rw [hmin, hmax]; exact hret1_16
  · have hab : regs .x12 = regs .x11 := BitVec.le_antisymm hc_2 hc
    rv_sym hp with [hL, hn, hn'] using [hterm [(regs .x12).toNat, (regs .x11).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · refine ⟨?_, ?_, ?_, by simp, by decide, ⟨?_, fun k hk => ?_⟩⟩
      all_goals try simp only [vecPtr, vecCap, vecLen, Layouts.Vec.ptr, Layouts.Vec.cap, Layouts.Vec.len,
        List.length_map, List.length_cons, List.length_nil]
      · rv_mem; rfl
      · rv_mem; rfl
      · rv_mem; rfl
      · have := (env.next m1).isLt
        simp only [BitVec.toNat_ofNat] at hret1_18; omega
      · simp only [BitVec.toNat_ofNat] at hret1_18
        have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
        rcases hk2 with rfl | rfl
        · simp only [Nat.mul_zero, List.map_cons, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
            BitVec.add_zero]
          rw [keep6_2 (r1 .x10) (Or.inl (by rv_mem; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr1) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_ne (Tactic.ne_add (by decide)), MachineState.getMem_setMem_eq]
        · simp only [Nat.mul_one, List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero,
            BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hr8 : (r1 .x10 + 8#64).toNat < env.stackLimit.toNat := by
            rw [Tactic.toNat_add_lit _ _ 8 rfl]; have := env.layout; omega
          rw [keep6_2 (r1 .x10 + 8#64) (Or.inl (by rv_mem; rw [Tactic.toNat_add_lit _ _ 8 rfl]; omega))]
          repeat rw [MachineState.getMem_setMem_ne
            (Tactic.ne_of_off_stack (Or.inl hr8)
              (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
          rw [MachineState.getMem_setMem_eq, hab]
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by rw [hab]; simp
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by rw [hab]; simp
      rw [hmin, hmax]; exact hret1_16

end Rv64mc.Proof.Layout.Prod
