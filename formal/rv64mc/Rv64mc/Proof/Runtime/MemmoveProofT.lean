/-
  Rv64mc.Proof.Runtime.MemmoveProofT

  `compiler_builtins`' `memmove(dst, src, n)` is total (`MemmoveT.MemmoveSpecT`, `Spec/Runtime/MemT.lean`'s pre- and
  postcondition with overlapping ranges allowed): it saves `s0` in its frame, then copies forward when `dst - src`
  (wrapping) is at least `n` (`MemmoveFwdT.fwd_ok`) and backward otherwise (`MemmoveBwdT.bwd_ok`), and returns `dst`
  with `[dst, dst + n)` holding what `[src, src + n)` held, every other byte apart from its stack kept.

  ## Main results

  * `total`
-/

import Rv64mc.Proof.Runtime.MemmoveFwdT
import Rv64mc.Proof.Runtime.MemmoveBwdT

namespace Rv64mc.Proof.Runtime.MemmoveProofT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime Rv64mc.Proof.Runtime.CopyT Rv64mc.Proof.Runtime.MoveT
open Rv64mc.Proof.Runtime.MemsetT (InWin Kept)
open Rv64mc.Proof.Runtime.MemmoveT (MemmoveSpecT)
open Rv64mc.Proof.Runtime.MemmoveFwdT (fwd_ok)
open Rv64mc.Proof.Runtime.MemmoveBwdT (bwd_ok)
open Rv64mc.Gen.CompilerBuiltins.Mem.Memmove (Link tmpl)

variable {env : Env} {p : Lprog (Op Reg) Reg} {i : Nat} {L : Link}

/-- **`memmove` is total**, with its 16-byte frame: it returns `dst` with the bytes copied, from `CopyPreT true`. -/
theorem total (hp : p[i]? = some (tmpl L)) : MemmoveSpecT env p i 16 := by
  intro Q ret top rest regs m hpre _ hk
  obtain ⟨⟨⟨hra, hsp⟩, hstk, hst, hnx, ⟨⟨hnw1, hnw2, -⟩, hwin0⟩, hal⟩, hwin⟩ := hpre
  have hR0 : Regs ret top regs (updReg regs .x2 (regs .x2 + 0xfffffffffffffff0#64)) := by
    refine ⟨by simp [updReg_apply, hra], by simp [updReg_apply, hsp], ?_, by simp [updReg_apply]⟩
    simp [AbiRegs, updReg_apply, hsp]
  have h8 : regs .x2 + 0xfffffffffffffff8#64 = top + 0xfffffffffffffff8#64 := by rw [hsp]
  have hroom : env.stackLimit.toNat + 16 ≤ top.toNat := by omega
  have hIF : FInv env top (regs .x10) (regs .x11) (regs .x12).toNat (regs .x8) m
      (Tactic.storeMem .b8 m (regs .x2 + 0xfffffffffffffff8#64) (regs .x8)) 0 := by
    rw [h8]; exact FInv.start hst hnx hroom hal
  have hFx (hn0 : (regs .x12).toNat ≠ 0) : Fx env top (regs .x10) (regs .x11) (regs .x12).toNat m :=
    let ⟨hdw, hdoff, hsw, hsoff⟩ := hwin0.resolve_left hn0
    ⟨hwin, hroom, hal, hdw, hsp ▸ hdoff, hsw, hsp ▸ hsoff⟩
  unfold NoWrap at hnw1 hnw2
  rv_symT hp stop [8, 128]
  · -- forward: `dst - src`, wrapping, at least `n`
    have hc' := BitVec.le_def.1 hc
    rw [BitVec.toNat_sub] at hc'
    by_cases hn0 : (regs .x12).toNat = 0
    · have hz : regs .x10 + regs .x12 = regs .x10 := by
        rw [show regs .x12 = 0#64 from BitVec.eq_of_toNat_eq hn0, BitVec.add_zero]
      clear hc hc'
      rv_symT hp stop [146, 158, 332, 450]
      · exact absurd hc (by rw [hz]; exact BitVec.lt_irrefl _)
      · refine ret_ok' hp hwin hroom hal hk hsp (by regs_ok hR0) ?_
        rw [hn0] at hIF ⊢; exact hIF
      · exact absurd (BitVec.le_def.1 hc_1) (by rw [hn0]; decide)
      · exact absurd (BitVec.le_def.1 hc_1) (by rw [hn0]; decide)
    · have F : FxF env top (regs .x10) (regs .x11) (regs .x12).toNat m := by
        refine ⟨hFx hn0, fun k k' hk hk' he => ?_⟩
        have := (regs .x10).isLt
        have := (regs .x11).isLt
        omega
      clear hc hc'
      exact fwd_ok hp F hk hsp (by regs_ok hR0) hIF (by simp [updReg_apply]) (by simp [updReg_apply]) hn0
  · -- backward: the destination starts inside the source
    have hc' := BitVec.lt_def.1 hc
    rw [BitVec.toNat_sub] at hc'
    have hn0 : (regs .x12).toNat ≠ 0 := by omega
    have F : FxB env top (regs .x10) (regs .x11) (regs .x12).toNat m := by
      refine ⟨hFx hn0, fun k k' hk hk' he => ?_⟩
      have := (regs .x10).isLt
      have := (regs .x11).isLt
      omega
    clear hc hc'
    exact bwd_ok hp F hk hsp (by regs_ok hR0) hIF.toB (by simp [updReg_apply]) (by simp [updReg_apply])
end Rv64mc.Proof.Runtime.MemmoveProofT

/-- info: 'Rv64mc.Proof.Runtime.MemmoveProofT.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Rv64mc.Proof.Runtime.MemmoveProofT.total
