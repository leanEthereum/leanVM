/-
  Rv64mc.Proof.Layout.ProdAlT

  `prod`'s second total contract (`prodSpecT`), beside `ProdT.prodSpecT`: `Spec.Layout.Constant.prodSpec`'s
  postcondition and the result's buffers 8-byte aligned (`TermAlT.FormAl`), so that the result is a `FormT`
  (`TermAlT.formT_of`), as `<Form as Add>::add` (`FormAddT`) and `Flushes::state_derived` ask of their operands. The
  proof is `ProdT.total`'s over `Form::term`'s second contract (`TermAlT`): the monomial's buffer is the block
  `alloc` returned, 8-byte aligned (`AllocPost`), as `TermAlT.PreA` asks.

  ## Main definitions

  * `prodSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.Prod
import Rv64mc.Proof.Layout.GpowT
import Rv64mc.Proof.Layout.ConstantT
import Rv64mc.Proof.Layout.TermAlT

namespace Rv64mc.Proof.Layout.ProdAlT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Gen.Verifier.Layout.Prod (Link tmpl)

open Rv64mc.Proof.Layout.Prod
open Rv64mc.Spec.Runtime (AllocPre AllocPost)
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.ConstantT (SretWin)
open Rv64mc.Proof.Layout.TermAlT (FormAl)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)

/-- **`prod`'s second total contract**, with `need` bytes of stack: `ProdT.prodSpecT`'s and the result's buffers
    aligned. -/
def prodSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => ColPre env regs m ∧ SretWin env regs m)
    (fun regs m r' m' => Post env (Model.prodRust (regs .x11).toNat (regs .x12).toNat (regs .x13).toNat) regs m r' m' ∧
      FormAl m' (regs .x10)) Term.Out AbortStop

set_option hygiene false in
/-- `Form::term`'s precondition at the call, `keep` the stores' lemma of the arm: the monomial `[e0, e1]` stored in
    the block `alloc` returned. -/
local macro "term_pre " keep:ident : tactic => `(tactic| (
    refine ⟨?_, ?_, ?_, by simp, by decide, ⟨?_, fun k hk => ?_⟩⟩
    all_goals try simp only [vecPtr, vecCap, vecLen, Layouts.Vec.ptr, Layouts.Vec.cap, Layouts.Vec.len,
      List.length_map, List.length_cons, List.length_nil]
    · rv_mem; rfl
    · rv_mem; rfl
    · rv_mem; rfl
    · have := (env.next m1).isLt
      simp only [BitVec.toNat_ofNat] at hret1_18; omega
    simp only [BitVec.toNat_ofNat] at hret1_18
    have hk2 : k = 0 ∨ k = 1 := by simp at hk; omega
    rcases hk2 with rfl | rfl
    · simp only [Nat.mul_zero, List.map_cons, List.getElem_cons_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_zero]
      rw [$keep:ident (r1 .x10) (Or.inl (by rv_mem; omega))]
      repeat rw [MachineState.getMem_setMem_ne
        (Tactic.ne_of_off_stack (Or.inl hr1) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
      rw [MachineState.getMem_setMem_ne (Tactic.ne_add (by decide)), MachineState.getMem_setMem_eq]
    simp only [Nat.mul_one, List.map_cons, List.getElem_cons_succ, List.getElem_cons_zero,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have hr8 : (r1 .x10 + 8#64).toNat < env.stackLimit.toNat := by
      rw [Tactic.toNat_add_lit _ _ 8 rfl]; have := env.layout; omega
    rw [$keep:ident (r1 .x10 + 8#64) (Or.inl (by rv_mem; rw [Tactic.toNat_add_lit _ _ 8 rfl]; omega))]
    repeat rw [MachineState.getMem_setMem_ne
      (Tactic.ne_of_off_stack (Or.inl hr8) (Tactic.slot_ge h64 (by decide)) (Tactic.slot_lt h64 (by decide)))]
    rw [MachineState.getMem_setMem_eq]))

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i need needG : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (halloc : AllocSpecT env p L.alloc.idx 0)
    (hgpow : GpowT.specT env p L.gpow.idx needG) (hterm : TermAlT.specT env p L.term.idx)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0) (hn : 64 + needG ≤ need)
    (hn' : 64 + Spec.Layout.Term.need ≤ need) : prodSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop) :=
    halloc.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [66] with [hL, hn, hn'] using [hal', hgpow, hpanic]
  all_goals
    have h64 : env.stackLimit.toNat + 64 ≤ top.toNat := by
      have := hpre_3; simp only [Spec.Layout.Term.need] at hn'; omega
    have hr16 : (r1 .x10).toNat + 16 ≤ env.heapEnd.toNat := by
      have := hret1_14.2.1; simp only [BitVec.toNat_ofNat] at hret1_18; omega
    have hr1 : (r1 .x10).toNat < env.stackLimit.toNat := by have := env.layout; omega
  · exact absurd hc (by rw [BitVec.lt_def] at hc_2 ⊢; omega)
  · rv_symT hp with [hL, hn, hn'] using [hterm [(regs .x11).toNat, (regs .x12).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · term_pre keep4_2
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by
        rw [BitVec.lt_def] at hc_2; omega
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by
        rw [BitVec.lt_def] at hc_2; omega
      rw [hmin, hmax]; exact hret1_16
    · simpa only [vecCap_eq, vecPtr_eq] using hret1_17
    · simpa only [vecCap_eq, vecPtr_eq, vecLen_eq] using hret1_18
  · rv_symT hp with [hL, hn, hn'] using [hterm [(regs .x12).toNat, (regs .x11).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · term_pre keep5_2
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by
        rw [BitVec.lt_def] at hc; omega
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by
        rw [BitVec.lt_def] at hc; omega
      rw [hmin, hmax]; exact hret1_16
    · simpa only [vecCap_eq, vecPtr_eq] using hret1_17
    · simpa only [vecCap_eq, vecPtr_eq, vecLen_eq] using hret1_18
  · have hab : regs .x12 = regs .x11 := BitVec.le_antisymm hc_2 hc
    rv_symT hp with [hL, hn, hn'] using [hterm [(regs .x12).toNat, (regs .x11).toNat] (Model.gpowRust (regs .x13))
      (env.next m) (r1 .x10) 2]
    · term_pre keep6_2
      rw [hab]
    · have e : BitVec.ofNat 64 (regs .x13).toNat = regs .x13 := by simp
      simp only [Model.prodRust, e]
      have hmin : min (regs .x11).toNat (regs .x12).toNat = (regs .x12).toNat := by rw [hab]; simp
      have hmax : max (regs .x11).toNat (regs .x12).toNat = (regs .x11).toNat := by rw [hab]; simp
      rw [hmin, hmax]; exact hret1_16
    · simpa only [vecCap_eq, vecPtr_eq] using hret1_17
    · simpa only [vecCap_eq, vecPtr_eq, vecLen_eq] using hret1_18

end Rv64mc.Proof.Layout.ProdAlT

/-- info: 'Rv64mc.Proof.Layout.ProdAlT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ProdAlT.total
