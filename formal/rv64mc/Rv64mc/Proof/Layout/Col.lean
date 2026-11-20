/-
  Rv64mc.Proof.Layout.Col

  `col` keeps its contract (`Spec.Layout.Constant.colSpec`) from `alloc`'s, `gpow`'s and `Form::term`'s: the
  monomial `[index]` in a fresh block, its header on the stack. `rv_auto` stops at the call to `term` (pc 50), where
  its ghosts (the block) are named; the header's word in the block is read back through `gpow`'s frame by hand.
-/

import Rv64mc.Spec.Layout.Constant
import Rv64mc.Spec.Runtime.Panic
import Rv64mc.Gen.Tmpl.Verifier.Layout.Col
import Rv64mc.Tactic.Sym

namespace Rv64mc.Proof.Layout.Col

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Gen.Verifier.Layout.Col (Link tmpl)

set_option rv_sym.heap true in
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i need needG : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (halloc : Spec.Runtime.AllocSpec env p L.alloc.idx 0)
    (hgpow : Spec.Layout.Gpow.spec env p L.gpow.idx needG) (hterm : Spec.Layout.Term.spec env p L.term.idx)
    (hpanic : Spec.Runtime.NoReturn env p L.panicNounwindFmt.idx 0) (hn : 64 + needG ≤ need)
    (hn' : 64 + Spec.Layout.Term.need ≤ need) : colSpec env p i need := by
  rv_auto hp stop [50] with [hL, hn, hn'] using [halloc, hgpow, hpanic]
  have h64 : env.stackLimit.toNat + 64 ≤ top.toNat := by
    have := hpre_3; simp only [Spec.Layout.Term.need] at hn'; omega
  have hr1 : (r1 .x10).toNat < env.stackLimit.toNat := by
    have := hret1_14.2.1; have := env.layout; simp only [BitVec.toNat_ofNat] at hret1_18; omega
  rv_sym hp with [hL, hn, hn'] using [hterm [(regs .x11).toNat] (Model.gpowRust (regs .x12)) (env.next m) (r1 .x10) 1]
  · refine ⟨?_, ?_, ?_, by simp, by decide, ⟨?_, fun k hk => ?_⟩⟩
    all_goals try simp only [vecPtr, vecCap, vecLen, Layouts.Vec.ptr, Layouts.Vec.cap, Layouts.Vec.len, List.length_map,
      List.length_singleton]
    · rv_mem; rfl
    · rv_mem; rfl
    · rv_mem; rfl
    · have := (env.next m1).isLt
      simp only [BitVec.toNat_ofNat] at hret1_18; omega
    · simp only [List.length_map, List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      simp only [Nat.mul_zero, List.map_cons, List.map_nil, List.getElem_cons_zero, BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
      have h8 := hret1_18
      simp only [BitVec.toNat_ofNat] at h8
      rw [BitVec.add_zero, keep3_2 (r1 .x10) (Or.inl (by rv_mem; omega))]
      repeat rw [MachineState.getMem_setMem_ne
        (Tactic.ne_of_off_stack (Or.inl hr1) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
      rw [MachineState.getMem_setMem_eq]
  · have e : BitVec.ofNat 64 (regs .x12).toNat = regs .x12 := by simp
    simpa [Model.colRust, e] using hret1_16

end Rv64mc.Proof.Layout.Col
