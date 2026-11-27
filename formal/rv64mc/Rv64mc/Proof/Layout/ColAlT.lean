/-
  Rv64mc.Proof.Layout.ColAlT

  `col`'s second total contract (`colSpecT`), beside `ColT.colSpecT`: `Spec.Layout.Constant`'s postcondition for
  `Model.colRust` and the result's buffers 8-byte aligned (`TermAlT.FormAl`), so that the result is a `FormT`
  (`TermAlT.formT_of`). The proof is `ColT.total`'s over `Form::term`'s second contract (`TermAlT`): the monomial's
  buffer is the block `alloc` returned, 8-byte aligned (`AllocPost`), as `TermAlT.PreA` asks.

  ## Main definitions

  * `colSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Layout.Col
import Rv64mc.Proof.Layout.GpowT
import Rv64mc.Proof.Layout.ConstantT
import Rv64mc.Proof.Layout.TermAlT

namespace Rv64mc.Proof.Layout.ColAlT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Layout Rv64mc.Spec.Layout.Constant
open Rv64mc.Spec.Runtime (AllocPre AllocPost)
open Rv64mc.Proof.Runtime (Aborts)
open Rv64mc.Proof.Runtime.AllocT (AllocSpecT)
open Rv64mc.Proof.Layout.ConstantT (SretWin)
open Rv64mc.Proof.Layout.TermAlT (FormAl)
open Rv64mc.Proof.Runtime.VecHdrT (vecCap_eq vecPtr_eq vecLen_eq)
open Rv64mc.Gen.Verifier.Layout.Col (Link tmpl)

/-- **`col`'s second total contract**, with `need` bytes of stack: `ColT.colSpecT`'s and the result's buffers
    aligned. -/
def colSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => ColPre env regs m ∧ SretWin env regs m)
    (fun regs m r' m' => Post env (Model.colRust (regs .x11).toNat (regs .x12).toNat) regs m r' m' ∧
      FormAl m' (regs .x10)) Term.Out AbortStop

set_option rv_sym.heap true in
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i need needG : Nat) (L : Link) (hp : p[i]? = some (tmpl L))
    (hL : L.WF p) (halloc : AllocSpecT env p L.alloc.idx 0)
    (hgpow : GpowT.specT env p L.gpow.idx needG) (hterm : TermAlT.specT env p L.term.idx)
    (hpanic : Aborts env p L.panicNounwindFmt.idx 0) (hn : 64 + needG ≤ need)
    (hn' : 64 + Spec.Layout.Term.need ≤ need) : colSpecT env p i need := by
  have hal' : HoldsT env p L.alloc.idx 0 AllocPre (AllocPost env) (Stop := AbortStop) :=
    halloc.mono_stop fun _ _ _ _ _ h => h.1
  rv_autoT hp stop [50] with [hL, hn, hn'] using [hal', hgpow, hpanic]
  have h64 : env.stackLimit.toNat + 64 ≤ top.toNat := by
    have := hpre_3; simp only [Spec.Layout.Term.need] at hn'; omega
  have hr1 : (r1 .x10).toNat < env.stackLimit.toNat := by
    have := hret1_14.2.1; have := env.layout; simp only [BitVec.toNat_ofNat] at hret1_18; omega
  rv_symT hp with [hL, hn, hn'] using [hterm [(regs .x11).toNat] (Model.gpowRust (regs .x12)) (env.next m) (r1 .x10) 1]
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
  · simpa only [vecCap_eq, vecPtr_eq] using hret1_17
  · simpa only [vecCap_eq, vecPtr_eq, vecLen_eq] using hret1_18

end Rv64mc.Proof.Layout.ColAlT

/-- info: 'Rv64mc.Proof.Layout.ColAlT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Layout.ColAlT.total
