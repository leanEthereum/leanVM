/-
  Rv64mc.Proof.Runtime.DoReserveT

  `RawVecInner::reserve::do_reserve_and_handle` is total: `DoReserveSpec`'s postcondition and the header still a
  vector's (`VecReprT.RawVecT`), or the run ends with the guest's abort (`AbortStop`) where `grow_amortized` does or
  where `handle_error` is called. From `grow_amortized`'s total contract (`GrowAmortizedT`) and `handle_error`'s
  `Aborts`; the partial proof (`DoReserve.lean`) ported by `rv_autoT`.

  ## Main definitions

  * `DoReserveSpecT`

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.DoReserve
import Rv64mc.Proof.Runtime.GrowOneT
import Rv64mc.Proof.Runtime.HaltT
import Rv64mc.Tactic.SymT

namespace Rv64mc.Proof.Runtime.DoReserveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.VecReprT (RawVecT)
open Rv64mc.Proof.Runtime.GrowAmortizedT (GrowPreT GrowAmortizedSpecT)
open Rv64mc.Gen.Alloc.RawVec.RawVecInnerAny.Reserve.DoReserveAndHandleGlobal (Link tmpl)

/-- **The total contract of `do_reserve_and_handle`**: `DoReserveSpec`'s, from `GrowPreT`, the header still
    `RawVecT`. -/
def DoReserveSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => GrowPreT env (regs .x13).toNat (regs .x14).toNat regs m)
    (fun regs m _ m' => Grown env m m' (regs .x10) ((regs .x11).toNat + (regs .x12).toNat) (regs .x14).toNat ∧
      RawVecT env m' (regs .x10) (regs .x14).toNat)
    GrowOut AbortStop

set_option rv_sym.heap true in
/-- **`do_reserve_and_handle` is total**, with 16 bytes of stack beyond its callees'. -/
theorem total (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need nga : Nat} (hn : 16 + nga ≤ need) (hga : GrowAmortizedSpecT env p L.growAmortized.idx nga)
    (hhe : Aborts env p L.handleError.idx nga) : DoReserveSpecT env p i need := by
  rv_autoT hp with [hL] using [hga, hhe]
  all_goals
    have hlay := env.layout
    have hown : env.Owned m top (regs .x10) 16 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
    have hlim : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
    have hslot := GrowOne.slot_notin hown hpre_5 hlim
    obtain ⟨h8, h16, hb8, hcap1, hptr1, hout⟩ := GrowOneT.ra_store (ret := ret) hown hpre_5 hlim
    have hnx1 : env.next (m.setMem (top + 0xfffffffffffffff8#64) ret) = env.next m := Env.next_setMem_stack hb8
  -- `grow_amortized`'s precondition, after `ra`'s store
  · rw [hcap1, hptr1]; unfold Env.Live; rw [hnx1]; exact hpre_11
  · rw [hcap1]; exact hpre_12
  · rw [hcap1, hptr1]; exact VecReprT.BufT.mono hpre_15 (by rw [hnx1])
  · rw [hcap1]; exact hpre_12
  -- `ra`, read back
  · rw [hret1_14.getMem_above (by rw [h16]; omega) (by rw [h16, h8]; omega) hout]
    exact MachineState.getMem_setMem_eq
  -- the return
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      (Env.Frame.setMem_stack hpre_5 hb8 (by rw [h8]; omega)).trans hret1_14 (by rw [h16]; omega)
        fun a h => Or.inr (Or.inr (Or.inr h)), hret1_15,
      GrowOne.grown_of_store hown hpre_11 hslot hb8 hpre_5 (hret1_16 (hc.trans rfl)),
      hret1_17, hret1_18, hret1_19, hret1_20⟩

end Rv64mc.Proof.Runtime.DoReserveT

/-- info: 'Rv64mc.Proof.Runtime.DoReserveT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.DoReserveT.total
