/-
  Rv64mc.Final.Start

  `_start` (`guest/src/main.rs`'s `global_asm!`) as a relocatable template, and its safety at Lprog from `main`'s
  contract: it sets `gp` and `sp`, calls `main`, and halts with `main`'s result in `a0`, so an accepting halt is one
  where `main` returned `0`, which `MainSpec` makes the verdict. The `j .` after the `ecall` is never reached: SP1's
  `HALT` stops the machine.
-/

import Rv64mc.Final.MainSpec
import Rv64mc.Link.Basic

namespace Rv64mc.Start

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine

/-- Where `_start`'s addresses come from: its entry, `gp`'s `auipc` value and offset, the call site of `main` and
    the address after it, and `main`. -/
structure Link where
  base : Word
  gpHi : Word
  gpLo : Word
  site : Site
  ret : Word
  main : Callee

/-- The facts of `L` the proof uses (`Callee.WF`, `Site.WF`), as equations for `simp`. -/
structure Link.WF (p : Lprog (Op Reg) Reg) (L : Link) : Prop where
  main : (p[L.main.idx]?).map (·.addr) = some L.main.entry
  site : (L.site.hi + L.site.lo) &&& 0xfffffffffffffffe#64 = L.main.entry

/-- `auipc gp; addi gp; li sp, 3; slli sp, sp, 30; addi sp, sp, -16; auipc ra; jalr ra (main); li t0, 0; ecall;
    j .`, lifted. -/
def tmpl (L : Link) : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := L.base, depth := 0, body :=
    [.Llabel .internal 0, .Lopn (.set .x3 (.imm L.gpHi)),
     .Llabel .internal 1, .Lopn (.set .x3 (.bin .add (.reg .x3) (.imm L.gpLo))),
     .Llabel .internal 2, .Lopn (.set .x2 (.bin .add (.imm 0#64) (.imm 3#64))),
     .Llabel .internal 3, .Lopn (.set .x2 (.bin .shl (.reg .x2) (.imm 0x1e#64))),
     .Llabel .internal 4, .Lopn (.set .x2 (.bin .add (.reg .x2) (.imm 0xfffffffffffffff0#64))),
     .Llabel .internal 5, .Lopn (.set .x1 (.imm L.site.hi)),
     .Llabel .internal 6, .Lcall L.ret
       (.indirect (.bin .and (.bin .add (.reg .x1) (.imm L.site.lo)) (.imm 0xfffffffffffffffe#64)) [L.main.idx]),
     .Llabel .internal 7, .Lopn (.set .x5 (.bin .add (.imm 0#64) (.imm 0#64))),
     .Llabel .internal 8, .Lext 0,
     .Llabel .internal 9, .Lgoto 9] }

/-- SP1's `ecall` with `t0 = 0` (`HALT`) does not continue. -/
theorem sp1Ecall_halt {u : MachineState} (hc : u.code u.pc = some .ECALL) (h5 : u.getReg .x5 = 0) :
    sp1Ecall u = none := by
  have hacc : Sp1.isAccelId 0#64 = false := by decide
  have hhost : Sp1.isHostId 0#64 = true := by decide
  simp [sp1Ecall, hc, h5, hacc, hhost, RiscvZkvm.Rv64.step, Sp1.HINT_LEN, Sp1.HINT_READ, Sp1.COMMIT,
    Sp1.COMMIT_DEFERRED_PROOFS]

/-- **`_start` is safe for the verdict**, at Lprog, from `main`'s contract: from its entry, with the input in
    memory and its length in `a0`, `NEXT` at the heap's start and the static data in place. -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Link) (hp : p[i]? = some (tmpl L)) (hL : L.WF p)
    {need : Nat} (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hmain : MainSpec env p L.main.idx need) {words : List Word} {regs : Reg → Word} {m : MachineState}
    (hst : env.Static m) (hpre : MainPre env words regs m) {G : State rvIsa → Prop} {k : Nat} {ret top : Word} :
    rvIsa.SafeN p sp1Ctx G k (fun _ => Verdict words) ⟨[⟨i, 0, ret, top⟩], regs, m⟩ := by
  obtain ⟨h10, hcap, hin, hnx⟩ := hpre
  lsym hp with [Lprog.Isa.addrAt, hL.main, hL.site, Holds.post, AbiRegs]
    using [(hmain words).contract]
  -- `main`'s precondition, at `sp = stackTop`
  · refine ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, ?_, hst, by rw [hnx]; exact hheap,
      by simpa [updReg_apply] using h10, hcap, hin, hnx⟩
    simp only [lsym_simp]
    exact hstack
  -- the halt: accepting only where `main` returned `0`, and no state after it
  · refine SafeN.ext hp rfl (fun ha => ?_) sp1Ctx_ext_ne_wrong fun r'' m'' es he => ?_
    · simp only [sp1Ctx, getReg_ofParts, updReg_apply] at ha
      exact hret.2.2.2 (by simpa using ha.2)
    · obtain ⟨u, hag, hc, hu⟩ := he
      have h5 : u.getReg .x5 = 0 := by
        rw [← hag.regs .x5]; simp [getReg_ofParts, updReg_apply]
      rw [sp1Ecall_halt hc h5] at hu
      cases hu

end Rv64mc.Start
