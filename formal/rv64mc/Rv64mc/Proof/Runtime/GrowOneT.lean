/-
  Rv64mc.Proof.Runtime.GrowOneT

  `RawVec<T>::grow_one` is total for every `T` the image keeps: `GrowOneSpec`'s postcondition and the header still
  a vector's (`VecReprT.RawVecT`), or the run ends with the guest's abort (`AbortStop`) where `grow_amortized` does
  or where `handle_error` is called. From `grow_amortized`'s total contract (`GrowAmortizedT`) and `handle_error`'s
  `Aborts`. One proof over the body with `T`'s alignment and size as parameters (`GrowOne.growOneBody`), as the
  partial `GrowOne.lean`; each instance is `GrowOnesT.lean`'s.

  ## Main definitions

  * `GrowOneSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.GrowOne
import Rv64mc.Proof.Runtime.GrowAmortizedT
import Rv64mc.Proof.Runtime.HaltT

namespace Rv64mc.Proof.Runtime.GrowOneT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.GrowOne
open Rv64mc.Proof.Runtime.VecReprT (RawVecT)
open Rv64mc.Proof.Runtime.GrowAmortizedT (GrowPreT GrowAmortizedSpecT)

/-- **The total contract of `RawVec<T>::grow_one`**, `T` of `size` bytes aligned to `align`. -/
def GrowOneSpecT (env : Env) (align size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (GrowPreT env align size)
    (fun regs m r' m' => GrowOnePost env size regs m r' m' ∧ RawVecT env m' (regs .x10) size) GrowOut AbortStop

set_option rv_sym.heap true in
/-- **`grow_one` is total**, with 16 bytes of stack beyond its callees'. -/
theorem total {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {fd : Lfundef (Op Reg) Reg} (hp : p[i]? = some fd)
    {base : Word} {s0 s1 : Site} {ga he : Callee} {align size : Nat}
    (hb : fd.body = growOneBody base s0 s1 ga he align size) (hga : ga.WF p) (hhe : he.WF p) (hs0 : s0.WF ga)
    (hs1 : s1.WF he) (halign : align < 2 ^ 63) (hsize : size < 2 ^ 63) {nga : Nat}
    (hGa : GrowAmortizedSpecT env p ga.idx nga) (hHe : Aborts env p he.idx nga) :
    GrowOneSpecT env align size p i (16 + nga) := by
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hga hhe
  simp only [Site.WF] at hs0 hs1
  rv_autoT hp with [Lprog.Isa.addrAt, hga, hhe, hs0, hs1, growOneBody] using [hGa, hHe]
  all_goals
    have hlay := env.layout
    have hown : env.Owned m top (regs .x10) 16 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
    have hw : (regs .x10).toNat + 16 < 2 ^ 64 := hown.2
    have h16 : (top + 0xfffffffffffffff0#64).toNat = top.toNat - 16 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have h8 : (top + 0xfffffffffffffff8#64).toNat = top.toNat - 8 := by
      rw [BitVec.toNat_add]; have := top.isLt; simp only [BitVec.toNat_ofNat]; omega
    have hslot := slot_notin hown hpre_5 (by omega)
    have hb8 : env.stackLimit.toNat ≤ (top + 0xfffffffffffffff8#64).toNat := by rw [h8]; omega
    have hne : regs .x10 ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h]; exact ⟨Nat.le_refl _, by omega⟩)
    have hnx1 := Env.next_setMem_stack (env := env) (m := m) (v := ret) hb8
    have hcap1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvCapAt (regs .x10)) =
        m.getMem (rvCapAt (regs .x10)) := by rw [rvCapAt_eq]; exact MachineState.getMem_setMem_ne hne
    have hneP : rvPtrAt (regs .x10) ≠ top + 0xfffffffffffffff8#64 := fun h => hslot (by
      rw [← h, rvPtrAt_eq]
      exact ⟨by rw [toNat_add_ofNat (by omega)]; omega, by rw [toNat_add_ofNat (by omega)]; omega⟩)
    have hptr1 : (m.setMem (top + 0xfffffffffffffff8#64) ret).getMem (rvPtrAt (regs .x10)) =
        m.getMem (rvPtrAt (regs .x10)) := MachineState.getMem_setMem_ne hneP
    have hal' : (BitVec.ofNat 64 align).toNat = align := by rw [BitVec.toNat_ofNat]; omega
    have hsz' : (BitVec.ofNat 64 size).toNat = size := by rw [BitVec.toNat_ofNat]; omega
  -- `grow_amortized(self, cap, 1, align, size)`'s precondition, after `ra`'s store
  · rw [hsz']; exact hpre_8
  · rw [hal']; exact hpre_9
  · rw [hal']; exact hpre_10
  · rw [hcap1, hptr1, hsz']; unfold Env.Live; rw [hnx1]; exact hpre_11
  · rw [hcap1, hsz']; exact hpre_12
  · rw [hcap1, hptr1, hsz']; exact VecReprT.BufT.mono hpre_15 (by rw [hnx1])
  · rw [hcap1, hsz']; exact hpre_12
  -- `ra`, read back from its slot, which `grow_amortized` keeps
  · have hout : ¬ GrowOut regs m (top + 0xfffffffffffffff8#64) := by
      rintro (h | h)
      · exact hne (by rw [h, rvCapAt_eq])
      · exact hneP h.symm
    rw [hret1_14.getMem_above (by rw [h16]; omega) (by rw [h16, h8]; omega) hout]
    exact MachineState.getMem_setMem_eq
  -- the return
  · have hok := hret1_16 (hc.trans rfl)
    rw [hsz', show (1#64 : Word).toNat = 1 from rfl] at hok
    exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      (Env.Frame.setMem_stack hpre_5 hb8 (by rw [h8]; omega)).trans hret1_14
        (by rw [h16]; omega) fun a h => Or.inr (Or.inr (Or.inr h)), hret1_15,
      grown_of_store hown hpre_11 hslot hb8 hpre_5 (by simpa only [rvCapAt_eq] using hok),
      hret1_17, hret1_18, by rw [← hsz']; exact hret1_19, by rw [← hsz']; exact hret1_20⟩

end Rv64mc.Proof.Runtime.GrowOneT

/-- info: 'Rv64mc.Proof.Runtime.GrowOneT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.GrowOneT.total
