/-
  Rv64mc.Final.Start

  The safety of `_start` (`guest/src/main.rs`'s `global_asm!`) at Lprog, over its generated template
  (`Rv64mc/Gen/Tmpl/Start.lean`, the lift of `auipc gp; addi gp; li sp, 3; slli sp, sp, 30; addi sp, sp, -16;
  auipc ra; jalr ra (main); li t0, 0; ecall; j .` with its addresses fields of `Gen.Start.Link`), from `main`'s
  contract: it sets `gp` and `sp`, calls `main`, and halts with `main`'s result in `a0`, so an accepting halt is one
  where `main` returned `0`, which `MainSpec` makes the verdict. The `j .` after the `ecall` is never reached: SP1's
  `HALT` stops the machine.
-/

import Rv64mc.Final.MainSpec
import Rv64mc.Gen.Tmpl.Start
import Rv64mc.Core.Sp1

namespace Rv64mc.Start

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine

/-- **`_start` is safe for the verdict**, at Lprog, from `main`'s contract: from its entry, with the input in
    memory and its length in `a0`, `NEXT` at the heap's start and the static data in place. -/
theorem ok (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) (L : Gen.Start.Link) (hp : p[i]? = some (Gen.Start.tmpl L))
    (hL : Gen.Start.Link.WF p L)
    {need : Nat} (hstack : env.stackLimit.toNat + need ≤ stackTop.toNat) (hheap : heapStart.toNat ≤ env.heapEnd.toNat)
    (hmain : MainSpec env p L.main.idx need) {words : List Word} {regs : Reg → Word} {m : MachineState}
    (hst : env.Static m) (hpre : MainPre env words regs m) {G : State rvIsa → Prop} {k : Nat} {ret top : Word} :
    rvIsa.SafeN p sp1Ctx G k (fun _ => Verdict words) ⟨[⟨i, 0, ret, top⟩], regs, m⟩ := by
  obtain ⟨h10, hcap, hin, hnx⟩ := hpre
  lsym hp with [Lprog.Isa.addrAt, hL.main, hL.s0, Holds.post, AbiRegs]
    using [(hmain words).contract]
  -- `main`'s precondition, at `sp = stackTop`
  · refine ⟨⟨by simp [updReg_apply], by simp [updReg_apply]⟩, ?_, hst, by rw [hnx]; exact hheap,
      ⟨by simpa [updReg_apply] using h10, hcap, hin, hnx⟩, by simp only [lsym_simp]; decide⟩
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
