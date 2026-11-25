/-
  Rv64mc.Proof.Runtime.ReserveT

  `Vec<T>::reserve(&mut self, additional)` is total for every `T` the image keeps: `ReserveSpec`'s postcondition
  (`Spec/Runtime/VecReserve.lean`, which has no partial proof) and the `Vec` still a vector's (`VecReprT.VecT`), or
  the run ends with the guest's abort (`AbortStop`) where `do_reserve_and_handle` does. It reads the capacity and
  the length, returns when the spare capacity holds `additional`, and otherwise tail-calls
  `do_reserve_and_handle(self, len, additional, align, size)` (`DoReserveT`). One proof over the body with `T`'s
  alignment and size as parameters (`reserveBody`); each instance is its template's equation by `rfl`.

  ## Main definitions

  * `reserveBody`, `ReserveSpecT`

  ## Main results

  * `total`; `e_total`, `form_total`, `optionE_total`, `busBlock_total`, `k_total`, `u8_total`, `usize_total`
-/

import Rv64mc.Proof.Runtime.DoReserveT
import Rv64mc.Spec.Runtime.VecReserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecE.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecForm.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecOptionE.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecBusBlock.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecK.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecU8.Reserve
import Rv64mc.Gen.Tmpl.Alloc.Vec.VecUsize.Reserve

namespace Rv64mc.Proof.Runtime.ReserveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime
open Rv64mc.Proof.Runtime.VecReprT (RawVecT VecT)
open Rv64mc.Proof.Runtime.DoReserveT (DoReserveSpecT)

/-- `reserve`'s body, for `T` aligned to `align` and of `size` bytes. -/
def reserveBody (s0 : Site) (dr : Callee) (align size : Nat) : List (LinstrR (Op Reg) Reg) :=
  [.Llabel .internal 0, .Lopn (.set .x12 (.bin .add (.reg .x11) (.imm 0#64))),
   .Llabel .internal 1, .Lopn (.load .x13 .b8 false (.bin .add (.reg .x10) (.imm 0#64))),
   .Llabel .internal 2, .Lopn (.load .x11 .b8 false (.bin .add (.reg .x10) (.imm 0x10#64))),
   .Llabel .internal 3, .Lopn (.set .x13 (.bin .sub (.reg .x13) (.reg .x11))),
   .Llabel .internal 4, .Lcond (.cmp "ltu" (.reg .x13) (.reg .x12)) 6,
   .Llabel .internal 5, .Lret,
   .Llabel .internal 6, .Lopn (.set .x13 (.bin .add (.imm 0#64) (.imm (BitVec.ofNat 64 align)))),
   .Llabel .internal 7, .Lopn (.set .x14 (.bin .add (.imm 0#64) (.imm (BitVec.ofNat 64 size)))),
   .Llabel .internal 8, .Lopn (.set .x6 (.imm s0.hi)),
   .Llabel .internal 9,
   .Ltail (.indirect (.bin .and (.bin .add (.reg .x6) (.imm s0.lo)) (.imm 0xfffffffffffffffe#64)) [dr.idx])]

/-- **The total contract of `Vec<T>::reserve`**, `T` of `size` bytes aligned to `align`: `ReserveSpec`'s, from the
    `Vec` a vector's, which it stays. -/
def ReserveSpecT (env : Env) (align size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (fun regs m => ReservePre env align size regs m ∧ VecT env m (regs .x10) size)
    (fun regs m r' m' => ReservePost env size regs m r' m' ∧ VecT env m' (regs .x10) size) GrowOut AbortStop

/-- A word of an object the caller owns, outside a callee's `out`, is kept by the callee's frame. -/
theorem getMem_owned {env : Env} {top a b : Word} {n : Nat} {out : Word → Prop} {m m' : MachineState}
    (hf : env.Frame top out m m') (hown : env.Owned m top a n) (hnx : (env.next m).toNat ≤ env.heapEnd.toNat)
    (hlim : env.stackLimit.toNat ≤ top.toNat) (hb : InRange a n b) (hout : ¬ out b) : m'.getMem b = m.getMem b := by
  have hlay := env.layout
  have hn' := hf.2.1
  refine hf.2.2 b fun hw => ?_
  unfold InRange at hb
  rcases hw with hw | hw | hw | hw
  · rcases hown.1 with h | h <;> omega
  · rcases hown.1 with h | h <;> omega
  · exact hown.not_next hnx hlim hb hw
  · exact hout hw

theorem vecCap_eq (m : MachineState) (a : Word) : vecCap m a = m.getMem a := by
  simp only [vecCap, Layouts.Vec.cap]; exact congrArg _ (BitVec.add_zero a)

theorem vecLen_eq (m : MachineState) (a : Word) : vecLen m a = m.getMem (a + 16#64) := rfl

set_option rv_sym.heap true in
/-- **`reserve` is total**, with no stack beyond `do_reserve_and_handle`'s. -/
theorem total {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {fd : Lfundef (Op Reg) Reg} (hp : p[i]? = some fd)
    {s0 : Site} {dr : Callee} {align size : Nat} (hb : fd.body = reserveBody s0 dr align size) (hdr : dr.WF p)
    (hs0 : s0.WF dr) (halign : align < 2 ^ 63) (hsize : size < 2 ^ 63) {need : Nat}
    (hDr : DoReserveSpecT env p dr.idx need) : ReserveSpecT env align size p i need := by
  obtain ⟨name, addr, depth, body⟩ := fd
  simp only at hb
  subst hb
  simp only [Callee.WF] at hdr
  simp only [Site.WF] at hs0
  rv_autoT hp with [Lprog.Isa.addrAt, hdr, hs0, reserveBody] using [hDr]
  all_goals
    have hlay := env.layout
    have hsz' : (BitVec.ofNat 64 size).toNat = size := by rw [BitVec.toNat_ofNat]; omega
    have hal' : (BitVec.ofNat 64 align).toNat = align := by rw [BitVec.toNat_ofNat]; omega
    have hown : env.Owned m top (regs .x10) 24 := ⟨by rw [← hpre_2]; exact hpre_6, hpre_7⟩
    have hw : (regs .x10).toNat + 24 < 2 ^ 64 := hown.2
    have hle := hpre_15
    rw [vecCap_eq, vecLen_eq] at hle
    have hsub : (m.getMem (regs .x10) - m.getMem (regs .x10 + 16#64)).toNat =
        (m.getMem (regs .x10)).toNat - (m.getMem (regs .x10 + 16#64)).toNat := by
      rw [BitVec.toNat_sub]; omega
  -- `do_reserve_and_handle(self, len, additional, align, size)`'s precondition
  · rw [hsz']; exact hpre_10
  · rw [hal']; exact hpre_11
  · rw [hal']; exact hpre_12
  · rw [hsz']; exact hpre_13
  · rw [hsz']; exact hpre_14
  · rw [hsz']; exact hpre_19
  · rw [hsz']; exact hpre_20
  -- after the grow: the length kept, the buffer grown, the `Vec` still a vector's
  all_goals try
    have h16 : (regs .x10 + 16#64).toNat = (regs .x10).toNat + 16 := toNat_add_ofNat (by omega)
    have hlen : m1.getMem (regs .x10 + 16#64) = m.getMem (regs .x10 + 16#64) :=
      getMem_owned hret1_14 hown hpre_5 (by omega) ⟨by omega, by omega⟩ fun h => by
        rcases h with h | h
        · have := congrArg BitVec.toNat h
          rw [h16, Tactic.rf, GrowOne.rvCapAt_eq] at this
          omega
        · have := congrArg BitVec.toNat h
          rw [h16, Tactic.rf, GrowOne.rvPtrAt_eq, toNat_add_ofNat (by omega)] at this
          omega
  · exact hlen
  · intro h
    rw [BitVec.lt_def, hsub] at hc
    omega
  · intro _
    rw [hsz'] at hret1_17
    refine ⟨hret1_16, hret1_17, fun k hk => hret1_18 k (by rw [hsz']; exact hk)⟩
  · rw [hsz'] at hret1_21; exact hret1_21
  · rw [hsz'] at hret1_22; exact hret1_22
  · rw [hlen]
    rw [GrowOne.rvCapAt_eq] at hret1_16
    omega
  -- no grow
  · intro h
    rw [BitVec.le_def, hsub] at hc
    omega
  · exact hle

/-! ## The instances -/

section Instances

open Rv64mc.Gen.Alloc.Vec

variable {env : Env} {p : Lprog (Op Reg) Reg} {i need : Nat}

theorem e_total (L : VecE.Reserve.Link) (hp : p[i]? = some (VecE.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 16 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem form_total (L : VecForm.Reserve.Link) (hp : p[i]? = some (VecForm.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 24 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem optionE_total (L : VecOptionE.Reserve.Link) (hp : p[i]? = some (VecOptionE.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 24 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem busBlock_total (L : VecBusBlock.Reserve.Link) (hp : p[i]? = some (VecBusBlock.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 48 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem k_total (L : VecK.Reserve.Link) (hp : p[i]? = some (VecK.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 8 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem u8_total (L : VecU8.Reserve.Link) (hp : p[i]? = some (VecU8.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 1 1 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

theorem usize_total (L : VecUsize.Reserve.Link) (hp : p[i]? = some (VecUsize.Reserve.tmpl L)) (hL : L.WF p)
    (hDr : DoReserveSpecT env p L.doReserveAndHandleGlobal.idx need) : ReserveSpecT env 8 8 p i need :=
  total hp rfl hL.doReserveAndHandleGlobal hL.s0 (by decide) (by decide) hDr

end Instances

end Rv64mc.Proof.Runtime.ReserveT

/-- info: 'Rv64mc.Proof.Runtime.ReserveT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.ReserveT.total
